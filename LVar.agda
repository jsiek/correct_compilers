module LVar where

open import Data.Nat using (ℕ; zero; suc; _≤ᵇ_)
open import Data.Nat.Properties
open import Data.Product
open import Data.Integer using (ℤ; -_; _-_; 0ℤ)
open import Data.List
open import Data.Maybe
open import Relation.Binary.PropositionalEquality
   using (_≡_; refl; trans; sym; cong; cong-app)
open import Agda.Builtin.Bool
open import Reader

nth : ∀{A : Set} → List A → ℕ → Maybe A
nth [] i = nothing
nth (x ∷ xs) zero    = just x
nth (x ∷ xs) (suc i) = nth xs i

update : ∀{A : Set} → List A → ℕ → A → List A
update [] i v = []
update (x ∷ xs) zero v = v ∷ xs
update (x ∷ xs) (suc i) v = x ∷ update xs i v

----------------- Variables ----------------------------

Id : Set
Id = ℕ

----------------- Definition of LVar ----------------------------

data Exp : Set where
  Num : ℤ → Exp
  Read : Exp
  Sub : Exp → Exp → Exp
  Var : (i : Id) → Exp
  Let : Exp → Exp → Exp

Env : Set
Env = List ℤ

interp-exp : Exp → Env → Reader ℤ
interp-exp (Num n) ρ = return n
interp-exp Read ρ = read
interp-exp (Sub e₁ e₂) ρ =
  (interp-exp e₁ ρ) then
  λ v₁ → (interp-exp e₂ ρ) then
  λ v₂ → return (Data.Integer._-_ v₁ v₂)
interp-exp (Var i) ρ = try (nth ρ i)
interp-exp (Let e₁ e₂) ρ =
  (interp-exp e₁ ρ) then
  λ v₁ → interp-exp e₂ (v₁ ∷ ρ)

interp-LVar : Exp → Inputs → Maybe ℤ
interp-LVar e s = run (interp-exp e []) s

----------------- Definition of LMonVar ----------------------------

data Atm : Set where
  Num : ℤ → Atm 
  Var : Id → Atm

data Mon : Set where
  Atom : Atm → Mon
  Read : Mon
  Sub : Atm → Atm → Mon
  Let : Mon → Mon → Mon

interp-atm : Atm → Env → Reader ℤ
interp-atm (Num n) ρ = return n
interp-atm (Var i) ρ = try (nth ρ i)

interp-mon : Mon → Env → Reader ℤ
interp-mon (Atom atm) ρ = interp-atm atm ρ
interp-mon Read ρ = read
interp-mon (Sub a₁ a₂) ρ =
  (interp-atm a₁ ρ) then
  λ v₁ → (interp-atm a₂ ρ) then
  λ v₂ → return (Data.Integer._-_ v₁ v₂)
interp-mon (Let e₁ e₂) ρ =
  (interp-mon e₁ ρ) then
  λ v₁ → interp-mon e₂ (v₁ ∷ ρ)

interp-LMonVar : Mon → Inputs → Maybe ℤ
interp-LMonVar m s = run (interp-mon m []) s

shift-atm : Atm → ℕ → Atm
shift-atm (Num x) c = Num x
shift-atm (Var x) c
    with c ≤ᵇ x
... | true = Var (suc x)
... | false = Var x

shift-mon : Mon → ℕ → Mon
shift-mon (Atom atm) c = Atom (shift-atm atm c)
shift-mon Read c = Read
shift-mon (Sub a₁ a₂) c = Sub (shift-atm a₁ c) (shift-atm a₂ c)
shift-mon (Let m₁ m₂) c = Let (shift-mon m₁ c) (shift-mon m₂ (suc c))

----------------- Remove Complex Operands ----------------------------

rco : Exp → Mon
rco (Num x) = Atom (Num x)
rco Read = Read
rco (Sub e₁ e₂) =
   Let (rco e₁)
   (Let (shift-mon (rco e₂) zero) (Sub (Var (suc (zero))) (Var zero)))
rco (Var i) = Atom (Var i)
rco (Let e₁ e₂) = Let (rco e₁) (rco e₂)

----------------- Definition of CVar ----------------------------

data CExp : Set where
  Atom : Atm → CExp
  Read : CExp
  Sub : Atm → Atm → CExp

data CTail : Set where
  Return : CExp → CTail
  Let : CExp → CTail → CTail

interp-CExp : CExp → Env → Reader ℤ
interp-CExp (Atom atm) ρ = interp-atm atm ρ
interp-CExp Read ρ = read
interp-CExp (Sub a₁ a₂) ρ =
  (interp-atm a₁ ρ) then
  λ v₁ → (interp-atm a₂ ρ) then
  λ v₂ → return (Data.Integer._-_ v₁ v₂)

interp-tail : CTail → Env → Reader ℤ
interp-tail (Return e) ρ = interp-CExp e ρ
interp-tail (Let e t) ρ =
  (interp-CExp e ρ) then
  λ v₁ → interp-tail t (v₁ ∷ ρ)

interp-CVar : CTail → Inputs → Maybe ℤ
interp-CVar t s = run (interp-tail t []) s

shift-exp : CExp → ℕ → CExp
shift-exp (Atom atm) c = Atom (shift-atm atm c)
shift-exp Read c = Read
shift-exp (Sub a₁ a₂) c = Sub (shift-atm a₁ c) (shift-atm a₂ c)

shift-tail : CTail → ℕ → CTail
shift-tail (Return e) c = Return (shift-exp e c)
shift-tail (Let e t) c = Let (shift-exp e c) (shift-tail t (suc c))

----------------- Explicate Control ----------------------------

explicate-let : Mon → CTail → CTail
explicate : Mon → CTail

explicate-let (Atom x) rest = Let (Atom x) rest  
explicate-let Read rest = Let Read rest
explicate-let (Sub a₁ a₂) rest = Let (Sub a₁ a₂) rest
explicate-let (Let m₁ m₂) rest =
  -- (Let (Let m₁ m₂) rest) ==> (Let m₁ (Let m₂ rest))
  let rest' = explicate-let m₂ (shift-tail rest 1) in
  explicate-let m₁ rest'

explicate (Atom x) = Return (Atom x)
explicate Read = Return Read
explicate (Sub a₁ a₂) = Return (Sub a₁ a₂)
explicate (Let m₁ m₂) = explicate-let m₁ (explicate m₂)

----------------- Definition of CVar2 ----------------------------

data CStmt : Set where
  Return : CExp → CStmt
  Assign : ℕ → CExp → CStmt → CStmt

data CProg : Set where
  Program : ℕ → CStmt → CProg

interp-stmt : CStmt → Env → Reader ℤ
interp-stmt (Return e) ρ = interp-CExp e ρ
interp-stmt (Assign x e s) ρ =
  (interp-CExp e ρ) then
  (λ v → interp-stmt s (update ρ x v))

interp-prog : CProg → Inputs → Maybe ℤ
interp-prog (Program n is) s = run (interp-stmt is (replicate n 0ℤ)) s

----------------- Lower Lets (Explicate Part 2) -------------------

shifts-atm : Atm → ℕ → ℕ → Atm
shifts-atm (Num x) c n = Num x
shifts-atm (Var x) c n
    with c ≤ᵇ x
... | true = Var (n Data.Nat.+ x)
... | false = Var x

shifts-exp : CExp → ℕ → ℕ → CExp
shifts-exp (Atom atm) c n = Atom (shifts-atm atm c n)
shifts-exp Read c n = Read
shifts-exp (Sub a₁ a₂) c n = Sub (shifts-atm a₁ c n) (shifts-atm a₂ c n)

lower-tail : CTail → CStmt × ℕ
lower-tail (Return e) = Return e , 0
lower-tail (Let e t)
    with lower-tail t
... | s , n = Assign n (shifts-exp e 0 (suc n)) s , suc n

lower-lets : CTail → CProg
lower-lets t
    with lower-tail t
... | s , n = Program n s

----------------- Definition of X86Var ----------------------------

data Arg : Set where
  Num : ℤ → Arg
  Var : Id → Arg
  Reg : ℕ → Arg

rax : ℕ
rax = 0

data Inst : Set where
  MovQ : Arg → Arg → Inst
  SubQ : Arg → Arg → Inst
  ReadInt : Inst

data X86Var : Set where
  Program : ℕ → List Inst → X86Var

StateX86 : Set
StateX86 = Inputs × List ℤ × List ℤ -- input + registers + variables

interp-arg : Arg → StateX86 → Maybe ℤ
interp-arg (Num i) s = just i
interp-arg (Var x) (inputs , regs , ρ) = nth ρ x
interp-arg (Reg x) (inputs , regs , ρ) = nth regs x

write-arg : Arg → ℤ → StateX86 → Maybe StateX86
write-arg (Num x) v (inputs , regs , ρ) = nothing
write-arg (Var x) v (inputs , regs , ρ) = just (inputs , regs , update ρ x v)
write-arg (Reg x) v (inputs , regs , ρ) = just (inputs , update regs x v , ρ)

interp-inst : Inst → StateX86 → Maybe StateX86
interp-inst (MovQ src dest) s
    with interp-arg src s
... | nothing = nothing
... | just val = write-arg dest val s
interp-inst (SubQ src dest) s
    with interp-arg src s
... | nothing = nothing
... | just y
    with interp-arg dest s
... | nothing = nothing
... | just x = write-arg dest (x - y) s
interp-inst ReadInt (inputs , regs , ρ)
    with read inputs
... | nothing = nothing  
... | just (v , inputs') =
      just (inputs' , update regs rax v , ρ)

interp-insts : List Inst → StateX86 → Maybe StateX86
interp-insts [] s = just s
interp-insts (inst ∷ is) s
    with interp-inst inst s
... | nothing = nothing
... | just s' = interp-insts is s'

interp-x86-var : X86Var → (ℕ × (ℕ → ℤ)) → Maybe ℤ
interp-x86-var (Program n is) inputs
    with interp-insts is (inputs , [ 0ℤ ] , replicate n 0ℤ)
... | nothing = nothing
... | just (inputs , regs , ρ) = nth regs 0

----------------- Instruction Selection ----------------------------

to-arg : Atm → Arg
to-arg (Num x) = Num x
to-arg (Var x) = Var x

select-exp : CExp → Arg → List Inst
select-exp (Atom a) dest = [ MovQ (to-arg a) dest ]
select-exp Read dest = ReadInt ∷ (MovQ (Reg rax) dest) ∷ []
select-exp (Sub a₁ a₂) dest = MovQ (to-arg a₁) dest ∷ (SubQ (to-arg a₂) dest) ∷ []

select-stmt : CStmt → List Inst
select-stmt (Return e) = select-exp e (Reg rax)
select-stmt (Assign x e rest) = (select-exp e (Var x)) ++ select-stmt rest

select-inst : CProg → X86Var
select-inst (Program n s) = Program n (select-stmt s)
