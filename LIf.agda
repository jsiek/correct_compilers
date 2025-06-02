module LIf where

open import Agda.Builtin.Unit
open import Data.Nat using (ℕ; zero; suc; _<_)
open import Data.Nat.Properties
open import Data.Product
open import Data.Integer using (ℤ; -_; _-_; 0ℤ; _≤ᵇ_)
open import Data.List
open import Data.Maybe
open import Relation.Binary.PropositionalEquality
   using (_≡_; refl; trans; sym; cong; cong-app)
open import Agda.Builtin.Bool renaming (Bool to 𝔹)
open import Data.Bool using (_∧_; _∨_; not)
open import Reader
open import Utilities

----------------- Definition of LIf ----------------------------

data UniOp : Set where
  Neg : UniOp
  Not : UniOp

data BinOp : Set where
  Sub : BinOp
  Eq : BinOp
  LessEq : BinOp
  And : BinOp

data Exp : Set where
  Num : ℤ → Exp
  Bool : 𝔹 → Exp
  Read : Exp
  Uni : UniOp → Exp → Exp
  Bin : BinOp → Exp → Exp → Exp
  Var : (i : Id) → Exp
  Let : Exp → Exp → Exp
  If : Exp → Exp → Exp → Exp

data Value : Set where
  Int : ℤ → Value
  Bool : 𝔹 → Value

toInt : Value → Maybe ℤ
toInt (Int n) = just n
toInt (Bool b) = nothing

toBool : Value → Maybe 𝔹
toBool (Int n) = nothing
toBool (Bool b) = just b

uniop : UniOp → Value → Reader Value
uniop Neg v =
  try (toInt v) then
  (λ n → return (Int (- n)))
uniop Not v =
  try (toBool v) then
  (λ n → return (Bool (not n)))

binop : BinOp → Value → Value → Reader Value
binop Sub v₁ v₂ =
  try (toInt v₁) then
  λ n₁ → try (toInt v₂) then
  λ n₂ → return (Int (n₁ - n₂))
binop Eq v₁ v₂ =
  try (toInt v₁) then
  λ n₁ → try (toInt v₂) then
  λ n₂ → return (Bool ((n₁ ≤ᵇ n₂) ∧ (n₂ ≤ᵇ n₁)))
binop LessEq v₁ v₂ =
  try (toInt v₁) then
  λ n₁ → try (toInt v₂) then
  λ n₂ → return (Bool (n₁ ≤ᵇ n₂))
binop And v₁ v₂ =
  try (toBool v₁) then
  λ b₁ → try (toBool v₂) then
  λ b₂ → return (Bool (b₁ ∧ b₂))

interp-exp : Exp → Env Value → Reader Value
interp-exp (Num n) ρ = return (Int n)
interp-exp (Bool b) ρ = return (Bool b)
interp-exp Read ρ = read-int Int
interp-exp (Uni op e) ρ =
  (interp-exp e ρ) then
  λ v → uniop op v
interp-exp (Bin op e₁ e₂) ρ =
  (interp-exp e₁ ρ) then
  λ v₁ → (interp-exp e₂ ρ) then
  λ v₂ → binop op v₁ v₂
interp-exp (Var i) ρ = try (nth ρ i)
interp-exp (Let e₁ e₂) ρ =
  (interp-exp e₁ ρ) then
  λ v₁ → interp-exp e₂ (v₁ ∷ ρ)
interp-exp (If e₁ e₂ e₃) ρ =
  (interp-exp e₁ ρ) then
  λ v₁ → try (toBool v₁) then
  λ { true → interp-exp e₂ ρ
    ; false → interp-exp e₃ ρ }

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
  Uni : UniOp → Atm → Mon
  Bin : BinOp → Atm → Atm → Mon
  Let : Mon → Mon → Mon
  If : Mon → Mon → Mon → Mon

interp-atm : Atm → Env Value → Maybe Value
interp-atm (Num n) ρ = just (Int n)
interp-atm (Bool b) ρ = just (Bool b)
interp-atm (Var i) ρ = nth ρ i

interp-mon : Mon → Env Value → Reader Value
interp-mon (Atom atm) ρ = try (interp-atm atm ρ)
interp-mon Read ρ = read-int Int
interp-mon (Uni op a) ρ =
  try (interp-atm a ρ) then
  λ v → uniop op v
interp-mon (Bin op a₁ a₂) ρ =
  try (interp-atm a₁ ρ) then
  λ v₁ → try (interp-atm a₂ ρ) then
  λ v₂ → binop op v₁ v₂
interp-mon (Let e₁ e₂) ρ =
  (interp-mon e₁ ρ) then
  λ v₁ → interp-mon e₂ (v₁ ∷ ρ)
interp-mon (If e₁ e₂ e₃) ρ =
  (interp-mon e₁ ρ) then
  λ v₁ → try (toBool v₁) then
  λ { true → interp-mon e₂ ρ
    ; false → interp-mon e₃ ρ }

interp-LMonIf : Mon → Inputs → Maybe Value
interp-LMonIf m s = run (interp-mon m []) s

shift-atm : Atm → ℕ → Atm
shift-atm (Num n) c = Num n
shift-atm (Bool b) c = Bool b
shift-atm (Var x) c = Var (shift-var x c)

shift-mon : Mon → ℕ → Mon
shift-mon (Atom atm) c = Atom (shift-atm atm c)
shift-mon Read c = Read
shift-mon (Uni op a) c = Uni op (shift-atm a c)
shift-mon (Bin op a₁ a₂) c = Bin op (shift-atm a₁ c) (shift-atm a₂ c)
shift-mon (Let m₁ m₂) c =
  Let (shift-mon m₁ c) (shift-mon m₂ (suc c))
shift-mon (If m₁ m₂ m₃) c =
  If (shift-mon m₁ c) (shift-mon m₂ c) (shift-mon m₃ c)

----------------- Remove Complex Operands ----------------------------

rco : Exp → Mon
rco (Num n) = Atom (Num n)
rco (Bool b) = Atom (Bool b)
rco Read = Read
rco (Uni op e) =
   Let (rco e) (Uni op (Var zero))
rco (Bin op e₁ e₂) =
   Let (rco e₁)
   (Let (shift-mon (rco e₂) zero) (Bin op (Var (suc (zero))) (Var zero)))
rco (Var i) = Atom (Var i)
rco (Let e₁ e₂) = Let (rco e₁) (rco e₂)
rco (If e₁ e₂ e₃) = If (rco e₁) (rco e₂) (rco e₃)

----------------- Definition of CIf ----------------------------

data CExp : Set where
  Atom : Atm → CExp
  Read : CExp
  Uni : UniOp → Atm → CExp
  Bin : BinOp → Atm → Atm → CExp

data CTail : Set where
  Return : CExp → CTail
  Let : CExp → CTail → CTail
  If : BinOp → Atm → Atm → Id → Id → CTail
  Goto : Id → CTail

Blocks : Set
Blocks = List CTail

data Type : Set where
  IntT : Type
  BoolT : Type

CProgram : Set
CProgram = List Type × Blocks

--- Interpreter for CIf

interp-CExp : CExp → Env Value → Reader Value
interp-CExp (Atom atm) ρ = try (interp-atm atm ρ)
interp-CExp Read ρ = read-int Int
interp-CExp (Uni op a) ρ =
  try (interp-atm a ρ) then
  λ v → uniop op v
interp-CExp (Bin op a₁ a₂) ρ =
  try (interp-atm a₁ ρ) then
  λ v₁ → try (interp-atm a₂ ρ) then
  λ v₂ → binop op v₁ v₂

interp-tail : ℕ → CTail → Env Value → Blocks → Reader Value
interp-tail 0 e ρ B = timeout
interp-tail (suc n) (Return e) ρ B = interp-CExp e ρ
interp-tail (suc n) (Let e t) ρ B =
  (interp-CExp e ρ) then
  λ v₁ → interp-tail n t (v₁ ∷ ρ) B
interp-tail (suc n) (If op a₁ a₂ thn els) ρ B =
  try (interp-atm a₁ ρ) then
  λ v₁ → try (interp-atm a₂ ρ) then
  λ v₂ → binop op v₁ v₂ then
  λ v₃ → try (toBool v₃) then
  λ { true →
        try (nth B thn) then
        λ t → interp-tail n t ρ B
    ; false →
        try (nth B els) then
        λ t → interp-tail n t ρ B }
interp-tail (suc n) (Goto lbl) ρ B =
     try (nth B lbl) then
     λ t → interp-tail n t ρ B
  
interp-CIf : ℕ → Blocks → Inputs → Maybe Value
interp-CIf n B s = run (try (last B) then
                        λ t → interp-tail n t [] B) s

--- Variable Shifting for CIf

shift-exp : CExp → ℕ → CExp
shift-exp (Atom atm) c = Atom (shift-atm atm c)
shift-exp Read c = Read
shift-exp (Uni op a) c = Uni op (shift-atm a c)
shift-exp (Bin op a₁ a₂) c = Bin op (shift-atm a₁ c) (shift-atm a₂ c)

shift-tail : CTail → ℕ → CTail
shift-tail (Return e) c = Return (shift-exp e c)
shift-tail (Let e t) c = Let (shift-exp e c) (shift-tail t (suc c))
shift-tail (If op a₁ a₂ thn els) c =
  If op (shift-atm a₁ c) (shift-atm a₂ c) thn els
shift-tail (Goto lbl) c = Goto lbl

----------------- Explicate Control ----------------------------

-- Block Monad
-- Next label to use for a new block
-- The list of blocks that have been created

Blocker : Set → Set
Blocker A = Blocks → A × Blocks

returnB : ∀{A : Set} → A → Blocker A
returnB a s = a , s

_thenB_ : ∀{A B : Set} → Blocker A → (A → Blocker B) → Blocker B
(M thenB g) s
    with M s
... | (v , s') = g v s'

create-block : CTail → Blocker Id
create-block (Goto lbl) B = lbl , B
create-block t B = length B , (B ++ [ t ])

explicate-let : Mon → CTail → Blocker CTail
explicate-pred : Mon → CTail → CTail → Blocker CTail
explicate-tail : Mon → Blocker CTail

explicate-let (Atom a) rest = returnB (Let (Atom a) rest  )
explicate-let Read rest = returnB (Let Read rest)
explicate-let (Uni op a) rest = returnB (Let (Uni op a) rest)
explicate-let (Bin op a₁ a₂) rest = returnB (Let (Bin op a₁ a₂) rest)
explicate-let (Let m₁ m₂) rest =
  explicate-let m₂ (shift-tail rest 1) thenB
  λ t₂ → explicate-let m₁ t₂
explicate-let (If m₁ m₂ m₃) rest =
   create-block rest thenB
   λ l → explicate-let m₂ (Goto l) thenB
   λ t₂ → explicate-let m₃ (Goto l) thenB
   λ t₃ → explicate-pred m₁ t₂ t₃

explicate-pred (Atom a) thn els =
  create-block thn thenB
  λ l₁ → create-block els thenB
  λ l₂ → returnB (If Eq a (Bool true) l₁ l₂)
explicate-pred Read thn els = returnB (Return (Atom (Num 0ℤ)))
explicate-pred (Uni Neg a) thn els = returnB (Return (Atom (Num 0ℤ)))
explicate-pred (Uni Not a) thn els = explicate-pred (Atom a) els thn
explicate-pred (Bin op a₁ a₂) thn els =
  create-block thn thenB
  λ lbl-thn → create-block els thenB
  λ lbl-els → returnB (If op a₁ a₂ lbl-thn lbl-els)
explicate-pred (Let m₁ m₂) thn els =
  explicate-pred m₂ (shift-tail thn 1) (shift-tail els 1) thenB
  λ rest' → explicate-let m₁ rest'
explicate-pred (If m₁ m₂ m₃) thn els =
    create-block thn thenB
   λ lbl-thn → create-block els thenB
   λ lbl-els → explicate-pred m₂ (Goto lbl-thn) (Goto lbl-els) thenB
   λ t₂ → (explicate-pred m₃ (Goto lbl-thn) (Goto lbl-els)) thenB
   λ t₃ → explicate-pred m₁ t₂ t₃

explicate-tail (Atom a) = returnB (Return (Atom a))
explicate-tail Read = returnB (Return Read)
explicate-tail (Uni op a) = returnB (Return (Uni op a))
explicate-tail (Bin op a₁ a₂) = returnB (Return (Bin op a₁ a₂))
explicate-tail (Let m₁ m₂) =
  explicate-tail m₂ thenB
  λ t₂ → explicate-let m₁ t₂
explicate-tail (If m₁ m₂ m₃) =
  (explicate-tail m₂) thenB
  λ t₂ → (explicate-tail m₃) thenB
  λ t₃ → explicate-pred m₁ t₂ t₃

explicate : Mon → Blocks
explicate m = proj₂ (((explicate-tail m) thenB
                      (λ t → create-block t)) [])



      
