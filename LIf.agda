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
