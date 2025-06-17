module LIf2 where

open import Agda.Builtin.Unit
open import Data.Nat using (ℕ; zero; suc; _≤ᵇ_; _<_; _+_; _≡ᵇ_)
open import Data.Nat.Properties
open import Data.Product
open import Data.Integer using (ℤ; -_; _-_; 0ℤ)
open import Data.List
open import Data.Maybe
open import Relation.Binary.PropositionalEquality
   using (_≡_; refl; trans; sym; cong; cong-app)
open import Agda.Builtin.Bool renaming (Bool to 𝔹)
open import Reader
open import Utilities

----------------- Definition of LIf ----------------------------

data Exp : Set where
  Num : ℤ → Exp
  Bool : 𝔹 → Exp
  Read : Exp
  Sub : Exp → Exp → Exp
  Eq : Exp → Exp → Exp
  Var : (i : Id) → Exp
  Let : Exp → Exp → Exp
  If : Exp → Exp → Exp → Exp

data Value : Set where
  Int : ℤ → Value
  Bool : 𝔹 → Value

sub : Value → Value → Maybe Value
sub (Int x) (Int y) = just (Int (x - y))
sub (Int x) (Bool x₁) = nothing
sub (Bool x) v2 = nothing

equal : Value → Value → Maybe Value
equal (Int (ℤ.pos x)) (Int (ℤ.pos y)) = just (Bool (x ≡ᵇ y))
equal (Int (ℤ.pos n)) (Int (ℤ.negsuc n₁)) = just (Bool false)
equal (Int (ℤ.negsuc n)) (Int (ℤ.pos n₁)) = just (Bool false)
equal (Int (ℤ.negsuc x)) (Int (ℤ.negsuc y)) = just (Bool (x ≡ᵇ y))
equal (Int x) (Bool y) = nothing
equal (Bool x) (Int y) = nothing
equal (Bool false) (Bool false) = just (Bool true)
equal (Bool false) (Bool true) = just (Bool false)
equal (Bool true) (Bool false) = just (Bool false)
equal (Bool true) (Bool true) = just (Bool true)

interp-exp : Exp → Env Value → Reader Value
interp-exp (Num n) ρ = return (Int n)
interp-exp (Bool b) ρ = return (Bool b)
interp-exp Read ρ = read-int Int
interp-exp (Sub e₁ e₂) ρ =
  (interp-exp e₁ ρ) then
  λ v₁ → (interp-exp e₂ ρ) then
  λ v₂ → try (sub v₁ v₂)
interp-exp (Eq e₁ e₂) ρ =
  (interp-exp e₁ ρ) then
  λ v₁ → (interp-exp e₂ ρ) then
  λ v₂ → try (equal v₁ v₂)
interp-exp (Var i) ρ = try (nth ρ i)
interp-exp (Let e₁ e₂) ρ =
  (interp-exp e₁ ρ) then
  λ v₁ → interp-exp e₂ (v₁ ∷ ρ)
interp-exp (If e₁ e₂ e₃) ρ =
  (interp-exp e₁ ρ) then
  λ { (Bool true) → interp-exp e₂ ρ
    ; (Bool false) → interp-exp e₃ ρ
    ; (Int n) → error }

interp-LIf : Exp → Inputs → Maybe Value
interp-LIf e s = run (interp-exp e []) s

----------------- Definition of LMonVar ----------------------------

data Atm : Set where
  Num : ℤ → Atm 
  Bool : 𝔹 → Atm 
  Var : Id → Atm

data Mon : Set where
  Atom : Atm → Mon
  Read : Mon
  Sub : Atm → Atm → Mon
  Eq : Atm → Atm → Mon
  Let : Mon → Mon → Mon
  If : Mon → Mon → Mon → Mon

interp-atm : Atm → Env Value → Maybe Value
interp-atm (Num n) ρ = just (Int n)
interp-atm (Bool b) ρ = just (Bool b)
interp-atm (Var i) ρ = nth ρ i

interp-mon : Mon → Env Value → Reader Value
interp-mon (Atom atm) ρ = try (interp-atm atm ρ)
interp-mon Read ρ = read-int Int
interp-mon (Sub a₁ a₂) ρ =
  (try (interp-atm a₁ ρ)) then
  λ v₁ → try (interp-atm a₂ ρ) then
  λ v₂ → try (sub v₁ v₂)
interp-mon (Eq a₁ a₂) ρ =
  (try (interp-atm a₁ ρ)) then
  λ v₁ → try (interp-atm a₂ ρ) then
  λ v₂ → try (equal v₁ v₂)
interp-mon (Let e₁ e₂) ρ =
  (interp-mon e₁ ρ) then
  λ v₁ → interp-mon e₂ (v₁ ∷ ρ)
interp-mon (If e₁ e₂ e₃) ρ =
  (interp-mon e₁ ρ) then
  λ { (Bool true) → interp-mon e₂ ρ
    ; (Bool false) → interp-mon e₃ ρ
    ; (Int n) → error }

interp-LMonVar : Mon → Inputs → Maybe Value
interp-LMonVar m s = run (interp-mon m []) s

shift-atm : Atm → ℕ → Atm
shift-atm (Num x) c = Num x
shift-atm (Bool b) c = Bool b
shift-atm (Var x) c = Var (shift-var x c)

shift-mon : Mon → ℕ → Mon
shift-mon (Atom atm) c = Atom (shift-atm atm c)
shift-mon Read c = Read
shift-mon (Sub a₁ a₂) c = Sub (shift-atm a₁ c) (shift-atm a₂ c)
shift-mon (Eq a₁ a₂) c = Eq (shift-atm a₁ c) (shift-atm a₂ c)
shift-mon (Let m₁ m₂) c = Let (shift-mon m₁ c) (shift-mon m₂ (suc c))
shift-mon (If m₁ m₂ m₃) c = If (shift-mon m₁ c) (shift-mon m₂ c) (shift-mon m₃ c)

----------------- Remove Complex Operands ----------------------------

rco : Exp → Mon
rco (Num x) = Atom (Num x)
rco (Bool b) = Atom (Bool b)
rco Read = Read
rco (Sub e₁ e₂) =
   Let (rco e₁)
     (Let (shift-mon (rco e₂) zero)
       (Sub (Var (suc (zero))) (Var zero)))
rco (Eq e₁ e₂) =
   Let (rco e₁)
    (Let (shift-mon (rco e₂) zero)
      (Eq (Var (suc (zero))) (Var zero)))
rco (Var i) = Atom (Var i)
rco (Let e₁ e₂) = Let (rco e₁) (rco e₂)
rco (If e₁ e₂ e₃) = If (rco e₁) (rco e₂) (rco e₃)

----------------- Definition of IL ----------------------------

data IL-Exp : Set where
  Atom : Atm → IL-Exp
  Read : IL-Exp
  Sub : Atm → Atm → IL-Exp
  Eq : Atm → Atm → IL-Exp
  Assign : Id → IL-Exp → IL-Exp → IL-Exp
  If : IL-Exp → IL-Exp → IL-Exp → IL-Exp
  
data IL-Prog : Set where
  Program : ℕ → IL-Exp → IL-Prog

StateIL : Set
StateIL = Inputs × List Value

data _⊢_⇓_⊣_ : StateIL → IL-Exp → Value → StateIL → Set where
  ⇓atom : ∀{s ρ a v}
     → interp-atm a ρ ≡ just v
     → (s , ρ) ⊢ Atom a ⇓ v ⊣ (s , ρ)
  ⇓read : ∀{i f ρ}
     → ((i , f) , ρ) ⊢ Read ⇓ Int (f i) ⊣ ((suc i , f) , ρ)
  ⇓sub : ∀{s ρ a₁ a₂ n₁ n₂ v}
     → interp-atm a₁ ρ ≡ just n₁
     → interp-atm a₂ ρ ≡ just n₂
     → sub n₁ n₂ ≡ just v
     → (s , ρ) ⊢ Sub a₁ a₂ ⇓ v ⊣ (s , ρ)
  ⇓eq : ∀{s ρ a₁ a₂ n₁ n₂ v}
     → interp-atm a₁ ρ ≡ just n₁
     → interp-atm a₂ ρ ≡ just n₂
     → equal n₁ n₂ ≡ just v
     → (s , ρ) ⊢ Eq a₁ a₂ ⇓ v ⊣ (s , ρ)
  ⇓assign : ∀{sρ s′ ρ′ sρ″ x e₁ e₂ n₁ n₂}
     → sρ ⊢ e₁ ⇓ n₁ ⊣ (s′ , ρ′)
     → (s′ , update ρ′ x n₁) ⊢ e₂  ⇓ n₂ ⊣ sρ″ 
     → sρ ⊢ Assign x e₁ e₂ ⇓ n₂ ⊣ sρ″ 
  ⇓if-true : ∀{sρ sρ′ sρ″ e₁ e₂ e₃ v₂}
     → sρ ⊢ e₁ ⇓ (Bool true) ⊣ sρ′ 
     → sρ′ ⊢ e₂ ⇓ v₂ ⊣ sρ″ 
     → sρ ⊢ If e₁ e₂ e₃ ⇓ v₂ ⊣ sρ″ 
  ⇓if-false : ∀{sρ sρ′ sρ″ e₁ e₂ e₃ v₃}
     → sρ ⊢ e₁ ⇓ (Bool false) ⊣ sρ′ 
     → sρ′ ⊢ e₃ ⇓ v₃ ⊣ sρ″ 
     → sρ ⊢ If e₁ e₂ e₃ ⇓ v₃ ⊣ sρ″ 

interp-ilprog : IL-Prog → Inputs → Value → Set
interp-ilprog (Program n e) s v =
    Σ[ sρ′ ∈ Inputs × Env Value ] (s , (replicate n (Int 0ℤ))) ⊢ e ⇓ v ⊣ sρ′ 

----------------- Lift Locals ----------------------------

shifts-atm : Atm → ℕ → ℕ → Atm
shifts-atm (Num x) c n = Num x
shifts-atm (Bool b) c n = Bool b
shifts-atm (Var x) c n = Var (shifts-var x c n)

shifts-ilexp : IL-Exp → ℕ → ℕ → IL-Exp
shifts-ilexp (Atom atm) c n = Atom (shifts-atm atm c n)
shifts-ilexp Read c n = Read
shifts-ilexp (Sub a₁ a₂) c n =
    Sub (shifts-atm a₁ c n) (shifts-atm a₂ c n)
shifts-ilexp (Eq a₁ a₂) c n =
    Eq (shifts-atm a₁ c n) (shifts-atm a₂ c n)
shifts-ilexp (Assign x e₁ e₂) c n =
    Assign (shifts-var x c n) (shifts-ilexp e₁ c n) (shifts-ilexp e₂ c n)
shifts-ilexp (If e₁ e₂ e₃) c n =
    If (shifts-ilexp e₁ c n) (shifts-ilexp e₂ c n) (shifts-ilexp e₃ c n)

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
lift-locals-mon (Eq a₁ a₂) = 0 , (Eq a₁ a₂)
lift-locals-mon (Let m₁ m₂)
    with lift-locals-mon m₁
... | i , e₁
    with lift-locals-mon m₂
... | j , e₂
    = (suc (i + j)) , Assign (i + j) (shifts-ilexp e₁ 0 (suc j)) (shifts-ilexp e₂ j i)
lift-locals-mon (If m₁ m₂ m₃) 
    with lift-locals-mon m₁ 
... | i , e₁
    with lift-locals-mon m₂ 
... | j , e₂
    with lift-locals-mon m₃ 
... | k , e₃
    =
    let e′₁ = shifts-ilexp e₁ 0 (j + k) in
    let e′₂ = shifts-ilexp (shifts-ilexp e₂ 0 k) (k + j) i in
    let e′₃ = shifts-ilexp e₃ k (i + j) in
    (i + j + k) , (If e′₁ e′₂ e′₃)
    
lift-locals : Mon → IL-Prog
lift-locals m
    with lift-locals-mon m
... | n , e = Program n e    

----------------- Definition of CVar ----------------------------

data CExp : Set where
  Atom : Atm → CExp
  Read : CExp
  Sub : Atm → Atm → CExp
  Eq : Atm → Atm → CExp

data CStmt : Set where
  Return : CExp → CStmt
  Assign : Id → CExp → CStmt → CStmt
  IfEq : Atm → Atm → Id → Id → CStmt
  Goto : Id → CStmt

data CProg : Set where
  Program : ℕ → Id → List CStmt → CProg

interp-CExp : CExp → Env Value → Reader Value
interp-CExp (Atom atm) ρ = try (interp-atm atm ρ)
interp-CExp Read ρ = read-int Int
interp-CExp (Sub a₁ a₂) ρ =
  (try (interp-atm a₁ ρ)) then
  λ v₁ → try (interp-atm a₂ ρ) then
  λ v₂ → try (sub v₁ v₂)
interp-CExp (Eq a₁ a₂) ρ =
  (try (interp-atm a₁ ρ)) then
  λ v₁ → try (interp-atm a₂ ρ) then
  λ v₂ → try (equal v₁ v₂)

data _,_⊢ᶜ_⇓_⊣_ : StateIL → List CStmt → CStmt → Value → StateIL → Set where
  ⇓return : ∀{s s' ρ B e v}
     → interp-CExp e ρ s ≡ just (v , s')
     → (s , ρ) , B ⊢ᶜ Return e ⇓ v ⊣ (s' , ρ)
  ⇓assign : ∀{s ρ B s′ sρ″ x e₁ e₂ v₁ v₂}
     → interp-CExp e₁ ρ s ≡ just (v₁ , s′)
     → (s′ , update ρ x v₁) , B ⊢ᶜ e₂  ⇓ v₂ ⊣ sρ″ 
     → (s , ρ) , B ⊢ᶜ Assign x e₁ e₂ ⇓ v₂ ⊣ sρ″ 
  ⇓if-true : ∀{s ρ B s′ a₁ a₂ v₁ v₂ v t thn els}
     → interp-atm a₁ ρ ≡ just v₁
     → interp-atm a₂ ρ ≡ just v₂
     → equal v₁ v₂ ≡ just (Bool true)
     → nth B thn ≡ just t
     → (s , ρ) , B ⊢ᶜ t ⇓ v ⊣ s′
     → (s , ρ) , B ⊢ᶜ IfEq a₁ a₂ thn els ⇓ v ⊣ s′
  ⇓if-false : ∀{s ρ B s′ a₁ a₂ v₁ v₂ v t thn els}
     → interp-atm a₁ ρ ≡ just v₁
     → interp-atm a₂ ρ ≡ just v₂
     → equal v₁ v₂ ≡ just (Bool false)
     → nth B els ≡ just t
     → (s , ρ) , B ⊢ᶜ t ⇓ v ⊣ s′
     → (s , ρ) , B ⊢ᶜ IfEq a₁ a₂ thn els ⇓ v ⊣ s′
  ⇓goto : ∀ {s B l v s′ t}
     → nth B l ≡ just t
     → s , B ⊢ᶜ t ⇓ v ⊣ s′ 
     → s , B ⊢ᶜ Goto l ⇓ v ⊣ s′ 

interp-prog : CProg → Inputs → Value → Set
interp-prog (Program n l B) s v =
    Σ[ s′ ∈ StateIL ] (s , (replicate n (Int 0ℤ))) , B ⊢ᶜ Goto l ⇓ v ⊣ s′ 

----------------- Explicate Control ----------------------------

Blocker : Set → Set
Blocker A = List CStmt → A × List CStmt

returnB : ∀{A : Set} → A → Blocker A
returnB a s = a , s

_thenB_ : ∀{A B : Set} → Blocker A → (A → Blocker B) → Blocker B
(M thenB g) s
    with M s
... | (v , s') = g v s'

create-block : CStmt → Blocker Id
create-block t B = length B , (B ++ [ t ])

explicate-assign : Id → IL-Exp → CStmt → Blocker CStmt
explicate-tail : IL-Exp → Blocker CStmt
explicate-pred : IL-Exp → CStmt → CStmt → Blocker CStmt

explicate-assign x (Atom a) rest = returnB (Assign x (Atom a) rest)
explicate-assign x Read rest = returnB (Assign x Read rest)
explicate-assign x (Sub a₁ a₂) rest = returnB (Assign x (Sub a₁ a₂) rest)
explicate-assign x (Eq a₁ a₂) rest = returnB (Assign x (Eq a₁ a₂) rest)
explicate-assign x (Assign y e₁ e₂) rest =
   (explicate-assign x e₂ rest) thenB
   λ t₂ → explicate-assign y e₁ t₂
explicate-assign y (If e₁ e₂ e₃) rest =
   create-block rest thenB
   λ l → explicate-assign y e₂ (Goto l) thenB
   λ t₂ → explicate-assign y e₃ (Goto l) thenB
   λ t₃ → explicate-pred e₁ t₂ t₃
    
explicate-tail (Atom a) = returnB (Return (Atom a))
explicate-tail Read = returnB (Return Read)
explicate-tail (Sub a₁ a₂) = returnB (Return (Sub a₁ a₂))
explicate-tail (Eq a₁ a₂) = returnB (Return (Eq a₁ a₂))
explicate-tail (Assign x e₁ e₂) =
    (explicate-tail e₂) thenB
    λ t₂ → explicate-assign x e₁ t₂
explicate-tail (If e₁ e₂ e₃) =
  (explicate-tail e₂) thenB
  λ t₂ → (explicate-tail e₃) thenB
  λ t₃ → explicate-pred e₁ t₂ t₃

explicate-pred (Atom a) thn els =
  create-block thn thenB
  λ l₁ → create-block els thenB
  λ l₂ → returnB (IfEq a (Bool true) l₁ l₂)
explicate-pred Read thn els = returnB (Return (Atom (Num 0ℤ)))
explicate-pred (Sub a₁ a₂) thn els = returnB (Return (Atom (Num 0ℤ)))
explicate-pred (Eq a₁ a₂) thn els =
  create-block thn thenB
  λ lbl-thn → create-block els thenB
  λ lbl-els → returnB (IfEq a₁ a₂ lbl-thn lbl-els)
explicate-pred (Assign x e₁ e₂) thn els =
  explicate-pred e₂ thn els thenB
  λ rest' → explicate-assign x e₁ rest'
explicate-pred (If e₁ e₂ e₃) thn els =
    create-block thn thenB
   λ lbl-thn → create-block els thenB
   λ lbl-els → explicate-pred e₂ (Goto lbl-thn) (Goto lbl-els) thenB
   λ t₂ → (explicate-pred e₃ (Goto lbl-thn) (Goto lbl-els)) thenB
   λ t₃ → explicate-pred e₁ t₂ t₃


explicate : IL-Prog → CProg
explicate (Program n e)
    with ((explicate-tail e) thenB
          (λ t → create-block t)) []
... | lbl , B = Program n lbl B
--  ? Program n (explicate-tail e)

----------------- Definition of X86Var ----------------------------

data Arg : Set where
  Num : ℤ → Arg
  Bool : 𝔹 → Arg -- consider removing this and using 0/1 for booleans
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
  CmpQ : Arg → Arg → Inst
  Jmp : Id → Inst
  JmpEq : Id → Inst
  ReadInt : Inst

Block : Set
Block = List Inst

data X86Var : Set where
  Program : ℕ → Id → List Block → X86Var

StateX86 : Set
StateX86 = Inputs × List Value × List Value -- input + registers + variables

interp-arg : Arg → StateX86 → Maybe Value
interp-arg (Num i) s = just (Int i)
interp-arg (Bool b) s = just (Bool b)
interp-arg (Var x) (inputs , regs , ρ) = nth ρ x
interp-arg (Reg x) (inputs , regs , ρ) = nth regs x

interp-dest : Dest → StateX86 → Maybe Value
interp-dest (Var x) (inputs , regs , ρ) = nth ρ x
interp-dest (Reg x) (inputs , regs , ρ) = nth regs x

write : Dest → Value → StateX86 → StateX86
write (Var x) v (inputs , regs , ρ) = (inputs , regs , update ρ x v)
write (Reg x) v (inputs , regs , ρ) = (inputs , update regs x v , ρ)

-- The 𝔹 says whether execution reached the end of the block (true) or halted early (false).
infix 4 _,_⊩_⇓_,_
data _,_⊩_⇓_,_ : StateX86 → List Block → List Inst → StateX86 → 𝔹 → Set 

-- The 𝔹 says whether to fall through to the next instruction or not.
infix 4 _,_⊢_⇓_,_
data _,_⊢_⇓_,_ : StateX86 → List Block → Inst → StateX86 → 𝔹 → Set where
  ⇓movq : ∀{src}{dest}{s}{val}{B}
        → interp-arg src s ≡ just val
        → s , B ⊢ (MovQ src dest) ⇓ write dest val s , true
  ⇓subq : ∀{src}{dest}{s}{x y v}{B}
        → interp-arg src s ≡ just y
        → interp-dest dest s ≡ just x
        → sub x y ≡ just v
        → s , B ⊢ (SubQ src dest) ⇓ write dest v s , true
  ⇓cmpq : ∀{a₁}{a₂}{s}{x y v}{B}
        → interp-arg a₁ s ≡ just x
        → interp-arg a₂ s ≡ just y
        → equal x y ≡ just v
        → s , B ⊢ (CmpQ a₁ a₂) ⇓ write (Reg rax) v s , true   -- Using rax instead of EFLAGS
  ⇓read : ∀{inputs inputs'}{regs}{ρ}{v}{B}
        → read-int Int inputs ≡ just (v , inputs')
        → (inputs , regs , ρ) , B ⊢ ReadInt ⇓ (inputs' , update regs rax v , ρ) , true
  ⇓jmp : ∀{s B l t s′ b}
        → nth B l ≡ just t
        → s , B ⊩ t ⇓ s′ , b
        → s , B ⊢ Jmp l ⇓ s′ , false
  ⇓jmpeq-true : ∀{inputs regs ρ B l t s′ b}
        → nth regs rax ≡ just (Bool true)
        → nth B l ≡ just t
        → (inputs , regs , ρ) , B ⊩ t ⇓ s′ , b
        → (inputs , regs , ρ) , B ⊢ JmpEq l ⇓ s′ , false
  ⇓jmpeq-false : ∀{inputs regs ρ B l}
        → nth regs rax ≡ just (Bool false)
        → (inputs , regs , ρ) , B ⊢ JmpEq l ⇓ (inputs , regs , ρ) , true

data _,_⊩_⇓_,_ where
  ⇓null : ∀{s : StateX86}{B} → s , B ⊩ [] ⇓ s , true
  ⇓cons : ∀{s s′ s″ : StateX86}{i}{is}{B}{b}
      → s , B ⊢ i ⇓ s′ , true
      → s′ , B ⊩ is ⇓ s″ , b
      → s , B ⊩ i ∷ is ⇓ s″ , b
  ⇓cons-halt : ∀{s s′ : StateX86}{i}{is}{B}
      → s , B ⊢ i ⇓ s′ , false
      → s , B ⊩ i ∷ is ⇓ s′ , false
  
interp-x86-var : X86Var → Inputs → Value → Set
interp-x86-var (Program n l B) inputs v =
  Σ[ inputs' ∈ Inputs ] Σ[ regs ∈ List Value ] Σ[ ρ ∈ List Value ] Σ[ b ∈ 𝔹 ]
  (inputs , [ Int 0ℤ ] , replicate n (Int 0ℤ)) , B ⊢ Jmp l ⇓ (inputs' , regs , ρ) , b
  × nth regs 0 ≡ just v

----------------- Instruction Selection ----------------------------

to-arg : Atm → Arg
to-arg (Num n) = Num n
to-arg (Bool b) = Bool b
to-arg (Var x) = Var x

select-exp : CExp → Dest → List Inst
select-exp (Atom a) dest = [ MovQ (to-arg a) dest ]
select-exp Read dest = ReadInt ∷ (MovQ (Reg rax) dest) ∷ []
select-exp (Sub a₁ a₂) dest =
  -- was:
  -- MovQ (to-arg a₁) dest ∷ (SubQ (to-arg a₂) dest) ∷ []
  -- but if dest = a₂, there's a problem.
  MovQ (to-arg a₁) (Reg rax) ∷ (SubQ (to-arg a₂) (Reg rax)) ∷ MovQ (Reg rax) dest ∷ []
select-exp (Eq a₁ a₂) dest =
  CmpQ (to-arg a₁) (to-arg a₂) ∷ MovQ (Reg rax) dest ∷ []
  
select-stmt : CStmt → List Inst
select-stmt (Return e) = select-exp e (Reg rax)
select-stmt (Assign x e rest) = (select-exp e (Var x)) ++ (select-stmt rest)
select-stmt (IfEq a₁ a₂ thn els) =
  CmpQ (to-arg a₁) (to-arg a₂) ∷ JmpEq thn ∷ Jmp els ∷ []
select-stmt (Goto l) = Jmp l ∷ [] 

select-inst : CProg → X86Var
select-inst (Program n l B) =
  Program n l (Data.List.map select-stmt B)

----------------- Compile ----------------------------

compile : Exp → X86Var
compile e =
  let m = rco e in
  let il = lift-locals m in
  let c = explicate il in
  select-inst c
  
