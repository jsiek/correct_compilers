module LIf2 where

open import Agda.Builtin.Unit
open import Data.Nat using (ℕ; zero; suc; _≤ᵇ_; _<_; _+_; _≡ᵇ_)
open import Data.Nat.Properties
open import Data.Product hiding (map)
open import Data.Integer using (ℤ; -_; _-_; 0ℤ)
open import Data.List
open import Data.Maybe hiding (map)
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality
   using (_≡_; refl; trans; sym; cong; cong-app)
open import Agda.Builtin.Bool renaming (Bool to 𝔹)
open import Reader
open import Utilities
open import Relation.Nullary using (Dec; yes; no)

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

----------------- Definition of LMonIf ----------------------------

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

interp-LMonIf : Mon → Inputs → Maybe Value
interp-LMonIf m s = run (interp-mon m []) s

shift-atm : Atm → ℕ → Atm
shift-atm (Num x) c = Num x
shift-atm (Bool b) c = Bool b
shift-atm (Var x) c = Var (shift-var x c)

shifts-atm : Atm → ℕ → ℕ → Atm
shifts-atm (Num x) c n = Num x
shifts-atm (Bool b) c n = Bool b
shifts-atm (Var x) c n = Var (shifts-var x c n)

shift-mon : Mon → ℕ → Mon
shift-mon (Atom atm) c = Atom (shift-atm atm c)
shift-mon Read c = Read
shift-mon (Sub a₁ a₂) c = Sub (shift-atm a₁ c) (shift-atm a₂ c)
shift-mon (Eq a₁ a₂) c = Eq (shift-atm a₁ c) (shift-atm a₂ c)
shift-mon (Let m₁ m₂) c = Let (shift-mon m₁ c) (shift-mon m₂ (suc c))
shift-mon (If m₁ m₂ m₃) c = If (shift-mon m₁ c) (shift-mon m₂ c) (shift-mon m₃ c)

down-atm : Atm → ℕ → Atm
down-atm (Num x) c = Num x
down-atm (Bool b) c = Bool b
down-atm (Var x) c = Var (down-var x c)

down-mon : Mon → ℕ → Mon
down-mon (Atom atm) c = Atom (down-atm atm c)
down-mon Read c = Read
down-mon (Sub a₁ a₂) c = Sub (down-atm a₁ c) (down-atm a₂ c)
down-mon (Eq a₁ a₂) c = Eq (down-atm a₁ c) (down-atm a₂ c)
down-mon (Let m₁ m₂) c = Let (down-mon m₁ c) (down-mon m₂ (suc c))
down-mon (If m₁ m₂ m₃) c = If (down-mon m₁ c) (down-mon m₂ c) (down-mon m₃ c)

----------------- Remove Complex Operands ----------------------------

data Atomic : Mon → Set where
  atomic : ∀ (a : Atm) → Atomic (Atom a)

atomic? : (m : Mon) → Dec (Atomic m)
atomic? (Atom a) = yes (atomic a)
atomic? Read = no λ ()
atomic? (Sub a₁ a₂) = no λ ()
atomic? (Eq a₁ a₂) = no λ ()
atomic? (Let m₁ m₂) = no λ ()
atomic? (If m₁ m₂ m₃) = no λ ()

-- The following isn't quite right because it doesn't shift things properly.
let-complex : Mon → (Atm → Mon) → Mon
let-complex m body
    with atomic? m
... | yes (atomic a) = body a
... | no cmplx = Let m (body (Var 0))

rco : Exp → Mon
rco (Num x) = Atom (Num x)
rco (Bool b) = Atom (Bool b)
rco Read = Read
rco (Sub e₁ e₂)
    -- Fancy version:
    -- let-complex (rco e₁) 
    -- λ a₁ → let-complex (shift-mon (rco e₂) 0) 
    -- λ a₂ → Sub a₁ a₂
    
    -- Complex version:
    with rco e₁ | rco e₂
... | m₁ | m₂
    with atomic? m₁ | atomic? m₂
... | yes (atomic a₁) | yes (atomic a₂) =
      Sub a₁ a₂
... | no cmplx₁ | yes (atomic a₂) =
      Let (rco e₁) (Sub (Var zero) (shift-atm a₂ 0))
... | yes (atomic a₁) | no cmplx₂ =
      Let (rco e₂) (Sub (shift-atm a₁ 0) (Var 0))
... | no cmplx₁ | no cmplx₂ = 
      Let m₁
        (Let (shift-mon m₂ 0)
          (Sub (Var 1) (Var 0)))
          
   -- Simple version:
   -- Let (rco e₁)
   --   (Let (shift-mon (rco e₂) 0)
   --     (Sub (Var 1) (Var 0)))
rco (Eq e₁ e₂) =
   Let (rco e₁)
    (Let (shift-mon (rco e₂) zero)
      (Eq (Var (suc (zero))) (Var zero)))
rco (Var i) = Atom (Var i)
rco (Let e₁ e₂) = Let (rco e₁) (rco e₂)
rco (If e₁ e₂ e₃) = If (rco e₁) (rco e₂) (rco e₃)

----------------- Definition of IL ----------------------------

data Imp-Exp : Set where
  Atom : Atm → Imp-Exp
  Read : Imp-Exp
  Sub : Atm → Atm → Imp-Exp
  Eq : Atm → Atm → Imp-Exp
  Assign : Id → Imp-Exp → Imp-Exp → Imp-Exp
  If : Imp-Exp → Imp-Exp → Imp-Exp → Imp-Exp
  
data Imp-Prog : Set where
  Program : ℕ → Imp-Exp → Imp-Prog

StateImp : Set
StateImp = Inputs × Env Value

data _⊢_⇓_⊣_ : StateImp → Imp-Exp → Value → StateImp → Set where
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

interp-imp : Imp-Prog → Inputs → Value → Set
interp-imp (Program n e) s v = Σ[ s′ ∈ StateImp ] (s , ρ) ⊢ e ⇓ v ⊣ s′
    where
    ρ = replicate n (Int 0ℤ)

----------------- Lift Locals ----------------------------

shifts-imp-exp : Imp-Exp → ℕ → ℕ → Imp-Exp
shifts-imp-exp (Atom atm) c n = Atom (shifts-atm atm c n)
shifts-imp-exp Read c n = Read
shifts-imp-exp (Sub a₁ a₂) c n =
    Sub (shifts-atm a₁ c n) (shifts-atm a₂ c n)
shifts-imp-exp (Eq a₁ a₂) c n =
    Eq (shifts-atm a₁ c n) (shifts-atm a₂ c n)
shifts-imp-exp (Assign x e₁ e₂) c n =
    Assign (shifts-var x c n) (shifts-imp-exp e₁ c n) (shifts-imp-exp e₂ c n)
shifts-imp-exp (If e₁ e₂ e₃) c n =
    If (shifts-imp-exp e₁ c n) (shifts-imp-exp e₂ c n) (shifts-imp-exp e₃ c n)

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

lift-locals-mon : Mon → ℕ × Imp-Exp
lift-locals-mon (Atom a) = 0 , (Atom a)
lift-locals-mon Read = 0 , Read
lift-locals-mon (Sub a₁ a₂) = 0 , (Sub a₁ a₂)
lift-locals-mon (Eq a₁ a₂) = 0 , (Eq a₁ a₂)
lift-locals-mon (Let m₁ m₂)
    with lift-locals-mon m₁
... | i , e₁
    with lift-locals-mon m₂
... | j , e₂
    = (suc (i + j)) , Assign (i + j) (shifts-imp-exp e₁ 0 (suc j)) (shifts-imp-exp e₂ j i)
lift-locals-mon (If m₁ m₂ m₃) 
    with lift-locals-mon m₁ 
... | i , e₁
    with lift-locals-mon m₂ 
... | j , e₂
    with lift-locals-mon m₃ 
... | k , e₃
    =
    let e′₁ = shifts-imp-exp e₁ 0 (j + k) in
    let e′₂ = shifts-imp-exp (shifts-imp-exp e₂ 0 k) (k + j) i in
    let e′₃ = shifts-imp-exp e₃ k (i + j) in
    (i + j + k) , (If e′₁ e′₂ e′₃)
    
lift-locals : Mon → Imp-Prog
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

CFG : Set
CFG = List CStmt

data CProg : Set where
  Program : ℕ → Id → CFG → CProg

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

data _,_⊢ᶜ_⇓_⊣_ : StateImp → CFG → CStmt → Value → StateImp → Set where
  ⇓return : ∀{s s' ρ G e v}
     → interp-CExp e ρ s ≡ just (v , s')
     → (s , ρ) , G ⊢ᶜ Return e ⇓ v ⊣ (s' , ρ)
  ⇓assign : ∀{s ρ G s′ sρ″ x e₁ e₂ v₁ v₂}
     → interp-CExp e₁ ρ s ≡ just (v₁ , s′)
     → (s′ , update ρ x v₁) , G ⊢ᶜ e₂  ⇓ v₂ ⊣ sρ″ 
     → (s , ρ) , G ⊢ᶜ Assign x e₁ e₂ ⇓ v₂ ⊣ sρ″ 
  ⇓if-true : ∀{s ρ G s′ a₁ a₂ v₁ v₂ v t thn els}
     → interp-atm a₁ ρ ≡ just v₁
     → interp-atm a₂ ρ ≡ just v₂
     → equal v₁ v₂ ≡ just (Bool true)
     → nth G thn ≡ just t
     → (s , ρ) , G ⊢ᶜ t ⇓ v ⊣ s′
     → (s , ρ) , G ⊢ᶜ IfEq a₁ a₂ thn els ⇓ v ⊣ s′
  ⇓if-false : ∀{s ρ G s′ a₁ a₂ v₁ v₂ v t thn els}
     → interp-atm a₁ ρ ≡ just v₁
     → interp-atm a₂ ρ ≡ just v₂
     → equal v₁ v₂ ≡ just (Bool false)
     → nth G els ≡ just t
     → (s , ρ) , G ⊢ᶜ t ⇓ v ⊣ s′
     → (s , ρ) , G ⊢ᶜ IfEq a₁ a₂ thn els ⇓ v ⊣ s′
  ⇓goto : ∀ {s G l v s′ t}
     → nth G l ≡ just t
     → s , G ⊢ᶜ t ⇓ v ⊣ s′ 
     → s , G ⊢ᶜ Goto l ⇓ v ⊣ s′ 

interp-prog : CProg → Inputs → Value → Set
interp-prog (Program n l G) s v =
    Σ[ s′ ∈ StateImp ] (s , (replicate n (Int 0ℤ))) , G ⊢ᶜ Goto l ⇓ v ⊣ s′ 

----------------- Explicate Control ----------------------------

Build : Set → Set
Build A = CFG → A × CFG

retB : {A : Set} → A → Build A
retB a s = a , s

_thenB_ : {A B : Set} → Build A → (A → Build B) → Build B
(M thenB g) s
    with M s
... | (v , s') = g v s'

add-node : CStmt → Build Id
add-node c B = length B , (B ++ [ c ])

explicate-assign : Id → Imp-Exp → CStmt → Build CStmt
explicate-tail : Imp-Exp → Build CStmt
explicate-pred : Imp-Exp → CStmt → CStmt → Build CStmt

explicate-assign x (Atom a) c = retB (Assign x (Atom a) c)
explicate-assign x Read c = retB (Assign x Read c)
explicate-assign x (Sub a₁ a₂) c = retB (Assign x (Sub a₁ a₂) c)
explicate-assign x (Eq a₁ a₂) c = retB (Assign x (Eq a₁ a₂) c)
explicate-assign x (Assign y e₁ e₂) c =
   (explicate-assign x e₂ c) thenB
   λ t₂ → explicate-assign y e₁ t₂
explicate-assign y (If e₁ e₂ e₃) c =
   add-node c thenB
   λ l → explicate-assign y e₂ (Goto l) thenB
   λ t₂ → explicate-assign y e₃ (Goto l) thenB
   λ t₃ → explicate-pred e₁ t₂ t₃
    
explicate-tail (Atom a) = retB (Return (Atom a))
explicate-tail Read = retB (Return Read)
explicate-tail (Sub a₁ a₂) = retB (Return (Sub a₁ a₂))
explicate-tail (Eq a₁ a₂) = retB (Return (Eq a₁ a₂))
explicate-tail (Assign x e₁ e₂) =
    (explicate-tail e₂) thenB
    λ t₂ → explicate-assign x e₁ t₂
explicate-tail (If e₁ e₂ e₃) =
  (explicate-tail e₂) thenB
  λ t₂ → (explicate-tail e₃) thenB
  λ t₃ → explicate-pred e₁ t₂ t₃

explicate-pred (Atom (Num x)) thn els = retB (Return (Atom (Num 0ℤ)))
explicate-pred (Atom (Bool false)) thn els = retB els
explicate-pred (Atom (Bool true)) thn els = retB thn
explicate-pred (Atom (Var x)) thn els =
  add-node thn thenB
  λ l₁ → add-node els thenB
  λ l₂ → retB (IfEq (Var x) (Bool true) l₁ l₂)
explicate-pred Read thn els = retB (Return (Atom (Num 0ℤ)))
explicate-pred (Sub a₁ a₂) thn els = retB (Return (Atom (Num 0ℤ)))
explicate-pred (Eq a₁ a₂) thn els =
  add-node thn thenB
  λ lbl-thn → add-node els thenB
  λ lbl-els → retB (IfEq a₁ a₂ lbl-thn lbl-els)
explicate-pred (Assign x e₁ e₂) thn els =
  explicate-pred e₂ thn els thenB
  λ c → explicate-assign x e₁ c
explicate-pred (If e₁ e₂ e₃) thn els =
    add-node thn thenB
   λ lbl-thn → add-node els thenB
   λ lbl-els → explicate-pred e₂ (Goto lbl-thn) (Goto lbl-els) thenB
   λ t₂ → (explicate-pred e₃ (Goto lbl-thn) (Goto lbl-els)) thenB
   λ t₃ → explicate-pred e₁ t₂ t₃

explicate : Imp-Prog → CProg
explicate (Program n e)
    with ((explicate-tail e) thenB
          (λ t → add-node t)) []
... | lbl , B = Program n lbl B

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

select-assign : CExp → Dest → List Inst
select-assign (Atom a) dest = MovQ (to-arg a) dest ∷ []
select-assign Read dest = ReadInt ∷ (MovQ (Reg rax) dest) ∷ []
select-assign (Sub a₁ a₂) dest =
  MovQ (to-arg a₁) (Reg rax) ∷
  SubQ (to-arg a₂) (Reg rax) ∷
  MovQ (Reg rax) dest ∷ []
select-assign (Eq a₁ a₂) dest =
  CmpQ (to-arg a₁) (to-arg a₂) ∷
  MovQ (Reg rax) dest ∷ []
  
select-stmt : CStmt → List Inst
select-stmt (Return e) = select-assign e (Reg rax)
select-stmt (Assign x e c) = select-assign e (Var x) ++ select-stmt c
select-stmt (IfEq a₁ a₂ thn els) =
  CmpQ (to-arg a₁) (to-arg a₂) ∷ JmpEq thn ∷ Jmp els ∷ []
select-stmt (Goto l) = Jmp l ∷ [] 

select-inst : CProg → X86Var
select-inst (Program n l B) =
  Program n l (map select-stmt B)

----------------- Compile ----------------------------

compile : Exp → X86Var
compile e = (select-inst ∘ explicate ∘ lift-locals ∘ rco) e

  
