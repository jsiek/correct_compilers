module LVar where

open import Agda.Builtin.Unit
open import Data.Nat using (ℕ; zero; suc; _≤ᵇ_; _<_; _+_)
open import Data.Nat.Properties
open import Data.Product
open import Data.Integer using (ℤ; -_; _-_; 0ℤ)
open import Data.List
open import Data.Maybe
open import Relation.Binary.PropositionalEquality
   using (_≡_; refl; trans; sym; cong; cong-app)
open import Agda.Builtin.Bool
open import Reader
open import Utilities

----------------- Definition of LVar ----------------------------

data Exp : Set where
  Num : ℤ → Exp
  Read : Exp
  Sub : Exp → Exp → Exp
  Var : (i : Id) → Exp
  Let : Exp → Exp → Exp

interp-exp : Exp → Env ℤ → Reader ℤ
interp-exp (Num n) ρ = return n
interp-exp Read ρ = read
interp-exp (Sub e₁ e₂) ρ =
  (interp-exp e₁ ρ) then
  λ v₁ → (interp-exp e₂ ρ) then
  λ v₂ → return (v₁ - v₂)
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

interp-atm : Atm → Env ℤ → Maybe ℤ
interp-atm (Num n) ρ = just n
interp-atm (Var i) ρ = nth ρ i

interp-mon : Mon → Env ℤ → Reader ℤ
interp-mon (Atom atm) ρ = try (interp-atm atm ρ)
interp-mon Read ρ = read
interp-mon (Sub a₁ a₂) ρ =
  (try (interp-atm a₁ ρ)) then
  λ v₁ → try (interp-atm a₂ ρ) then
  λ v₂ → return (v₁ - v₂)
interp-mon (Let e₁ e₂) ρ =
  (interp-mon e₁ ρ) then
  λ v₁ → interp-mon e₂ (v₁ ∷ ρ)

interp-LMonVar : Mon → Inputs → Maybe ℤ
interp-LMonVar m s = run (interp-mon m []) s

shift-atm : Atm → ℕ → Atm
shift-atm (Num x) c = Num x
shift-atm (Var x) c = Var (shift-var x c)

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

----------------- Definition of IL ----------------------------

data IL-Exp : Set where
  Atom : Atm → IL-Exp
  Read : IL-Exp
  Sub : Atm → Atm → IL-Exp
  Assign : Id → IL-Exp → IL-Exp → IL-Exp
  
data IL-Prog : Set where
  Program : ℕ → IL-Exp → IL-Prog

StateIL : Set
StateIL = Inputs × List ℤ

data _⊢_⇓_⊣_ : StateIL → IL-Exp → ℤ → StateIL → Set where
  ⇓atom : ∀{s ρ a v}
     → interp-atm a ρ ≡ just v
     → (s , ρ) ⊢ Atom a ⇓ v ⊣ (s , ρ)
  ⇓read : ∀{i f ρ}
     → ((i , f) , ρ) ⊢ Read ⇓ (f i) ⊣ ((suc i , f) , ρ)
  ⇓sub : ∀{s ρ a₁ a₂ n₁ n₂}
     → interp-atm a₁ ρ ≡ just n₁
     → interp-atm a₂ ρ ≡ just n₂
     → (s , ρ) ⊢ Sub a₁ a₂ ⇓ n₁ - n₂ ⊣ (s , ρ)
  ⇓assign : ∀{sρ s′ ρ′ sρ″ x e₁ e₂ n₁ n₂}
     → sρ ⊢ e₁ ⇓ n₁ ⊣ (s′ , ρ′)
     → (s′ , update ρ′ x n₁) ⊢ e₂  ⇓ n₂ ⊣ sρ″ 
     → sρ ⊢ Assign x e₁ e₂ ⇓ n₂ ⊣ sρ″ 

interp-imp : IL-Prog → Inputs → ℤ → Set
interp-imp (Program n e) s v =
    Σ[ sρ′ ∈ Inputs × Env ℤ ] (s , (replicate n 0ℤ)) ⊢ e ⇓ v ⊣ sρ′ 

----------------- Lift Locals ----------------------------

shifts-atm : Atm → ℕ → ℕ → Atm
shifts-atm (Num x) c n = Num x
shifts-atm (Var x) c n = Var (shifts-var x c n)

shifts-imp-exp : IL-Exp → ℕ → ℕ → IL-Exp
shifts-imp-exp (Atom atm) c n = Atom (shifts-atm atm c n)
shifts-imp-exp Read c n = Read
shifts-imp-exp (Sub a₁ a₂) c n =
    Sub (shifts-atm a₁ c n) (shifts-atm a₂ c n)
shifts-imp-exp (Assign x e₁ e₂) c n =
    Assign (shifts-var x c n) (shifts-imp-exp e₁ c n) (shifts-imp-exp e₂ c n)

-- Lift Locals hoists all the Let's to the top, leaving in their place assignments.
--   let x = e₁ in e₂
--   ==>
--   let x = 0 in { x := e′₁; e′₂ }
--
--
--   Returns the number of variables bound by the let's around the expression:
--   let y₁=0,...,yᵢ=0 in m
--   is represented as
--   i , m

lift-locals-mon : Mon → ℕ × IL-Exp
lift-locals-mon (Atom a) = 0 , (Atom a)
lift-locals-mon Read = 0 , Read
lift-locals-mon (Sub a₁ a₂) = 0 , (Sub a₁ a₂)
lift-locals-mon (Let m₁ m₂)
    with lift-locals-mon m₁
... | i , e₁
    with lift-locals-mon m₂
... | j , e₂
    = (suc (i + j)) , Assign (i + j) (shifts-imp-exp e₁ 0 (suc j)) (shifts-imp-exp e₂ j i)

lift-locals : Mon → IL-Prog
lift-locals m
    with lift-locals-mon m
... | n , e = Program n e    

----------------- Definition of CVar ----------------------------

data CExp : Set where
  Atom : Atm → CExp
  Read : CExp
  Sub : Atm → Atm → CExp

data CStmt : Set where
  Return : CExp → CStmt
  Assign : Id → CExp → CStmt → CStmt

data CProg : Set where
  Program : ℕ → CStmt → CProg

interp-CExp : CExp → Env ℤ → Reader ℤ
interp-CExp (Atom atm) ρ = try (interp-atm atm ρ)
interp-CExp Read ρ = read
interp-CExp (Sub a₁ a₂) ρ =
  (try (interp-atm a₁ ρ)) then
  λ v₁ → try (interp-atm a₂ ρ) then
  λ v₂ → return (Data.Integer._-_ v₁ v₂)

data _⊢ᶜ_⇓_⊣_ : StateIL → CStmt → ℤ → StateIL → Set where
  ⇓return : ∀{s s' ρ e v}
     → interp-CExp e ρ s ≡ just (v , s')
     → (s , ρ) ⊢ᶜ Return e ⇓ v ⊣ (s' , ρ)
  ⇓assign : ∀{s ρ s′ sρ″ x e₁ e₂ v₁ v₂}
     → interp-CExp e₁ ρ s ≡ just (v₁ , s′)
     → (s′ , update ρ x v₁) ⊢ᶜ e₂  ⇓ v₂ ⊣ sρ″ 
     → (s , ρ) ⊢ᶜ Assign x e₁ e₂ ⇓ v₂ ⊣ sρ″ 

interp-prog : CProg → Inputs → ℤ → Set
interp-prog (Program n st) s v =
    Σ[ sρ′ ∈ Inputs × Env ℤ ] (s , (replicate n 0ℤ)) ⊢ᶜ st ⇓ v ⊣ sρ′ 

----------------- Explicate Control ----------------------------

explicate-assign : Id → IL-Exp → CStmt → CStmt
explicate-tail : IL-Exp → CStmt

explicate-assign x (Atom a) rest = Assign x (Atom a) rest  
explicate-assign x Read rest = Assign x Read rest
explicate-assign x (Sub a₁ a₂) rest = Assign x (Sub a₁ a₂) rest
explicate-assign x (Assign y e₁ e₂) rest =
    explicate-assign y e₁ (explicate-assign x e₂ rest)
    
explicate-tail (Atom a) = Return (Atom a)
explicate-tail Read = Return Read
explicate-tail (Sub a₁ a₂) = Return (Sub a₁ a₂)
explicate-tail (Assign x e₁ e₂) =
    explicate-assign x e₁ (explicate-tail e₂)

explicate : IL-Prog → CProg
explicate (Program n e) = Program n (explicate-tail e)

----------------- Definition of X86Var ----------------------------

data Arg : Set where
  Num : ℤ → Arg
  Var : Id → Arg
  Reg : ℕ → Arg

data Dest : Set where
  Var : Id → Dest
  Reg : ℕ → Dest

rax : ℕ
rax = 0

data Inst : Set where
  MovQ : Arg → Dest → Inst
  SubQ : Arg → Dest → Inst
  ReadInt : Inst

data X86Var : Set where
  Program : ℕ → List Inst → X86Var

StateX86 : Set
StateX86 = Inputs × List ℤ × List ℤ -- input + registers + variables

interp-arg : Arg → StateX86 → Maybe ℤ
interp-arg (Num i) s = just i
interp-arg (Var x) (inputs , regs , ρ) = nth ρ x
interp-arg (Reg x) (inputs , regs , ρ) = nth regs x

interp-dest : Dest → StateX86 → Maybe ℤ
interp-dest (Var x) (inputs , regs , ρ) = nth ρ x
interp-dest (Reg x) (inputs , regs , ρ) = nth regs x

write : Dest → ℤ → StateX86 → StateX86
write (Var x) v (inputs , regs , ρ) = (inputs , regs , update ρ x v)
write (Reg x) v (inputs , regs , ρ) = (inputs , update regs x v , ρ)

infix 4 _⊢_⇓_
data _⊢_⇓_ : StateX86 → Inst → StateX86 → Set where
  ⇓movq : ∀{src}{dest}{s}{val}
        → interp-arg src s ≡ just val
        → s ⊢ (MovQ src dest) ⇓ write dest val s
  ⇓subq : ∀{src}{dest}{s}{x y}
        → interp-arg src s ≡ just y
        → interp-dest dest s ≡ just x
        → s ⊢ (SubQ src dest) ⇓ write dest (x - y) s
  ⇓read : ∀{inputs inputs'}{regs}{ρ}{v}
        → read inputs ≡ just (v , inputs')
        → (inputs , regs , ρ) ⊢ ReadInt ⇓ (inputs' , update regs rax v , ρ)

infix 4 _⊩_⇓_
data _⊩_⇓_ : StateX86 → List Inst → StateX86 → Set where
  ⇓null : ∀{s : StateX86} → s ⊩ [] ⇓ s
  ⇓cons : ∀{s s′ s″ : StateX86}{i}{is}
      → s ⊢ i ⇓ s′
      → s′ ⊩ is ⇓ s″ 
      → s ⊩ i ∷ is ⇓ s″ 
  
interp-x86-var : X86Var → Inputs → ℤ → Set
interp-x86-var (Program n is) inputs v =
  Σ[ inputs' ∈ Inputs ] Σ[ regs ∈ List ℤ ] Σ[ ρ ∈ List ℤ ]
  (inputs , [ 0ℤ ] , replicate n 0ℤ) ⊩ is ⇓ (inputs' , regs , ρ)
  × nth regs 0 ≡ just v

----------------- Instruction Selection ----------------------------

to-arg : Atm → Arg
to-arg (Num x) = Num x
to-arg (Var x) = Var x

select-exp : CExp → Dest → List Inst
select-exp (Atom a) dest = [ MovQ (to-arg a) dest ]
select-exp Read dest = ReadInt ∷ (MovQ (Reg rax) dest) ∷ []
select-exp (Sub a₁ a₂) dest =
  -- was:
  -- MovQ (to-arg a₁) dest ∷ (SubQ (to-arg a₂) dest) ∷ []
  -- but if dest = a₂, there's a problem.
  MovQ (to-arg a₁) (Reg rax) ∷ (SubQ (to-arg a₂) (Reg rax)) ∷ MovQ (Reg rax) dest ∷ []

select-stmt : CStmt → List Inst
select-stmt (Return e) = select-exp e (Reg rax)
select-stmt (Assign x e rest) = (select-exp e (Var x)) ++ (select-stmt rest)

select-inst : CProg → X86Var
select-inst (Program n s) = Program n (select-stmt s)

----------------- Compile ----------------------------

compile : Exp → X86Var
compile e =
  let m = rco e in
  let il = lift-locals m in
  let c = explicate il in
  select-inst c
  
