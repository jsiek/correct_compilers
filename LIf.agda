module LIf where

open import Agda.Builtin.Unit
open import Data.Nat using (ℕ; zero; suc; _<_; _+_)
open import Data.Nat.Properties
open import Data.Product
open import Data.Integer using (ℤ; -_; _-_; 0ℤ; 1ℤ; -1ℤ; _≤ᵇ_)
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

uniop : UniOp → Value → Maybe Value
uniop Neg (Int n) = just (Int (- n))
uniop Neg (Bool b) = nothing
uniop Not (Int n) = nothing
uniop Not (Bool b) = just (Bool (not b))

_≡ᵇ_ : 𝔹 → 𝔹 → 𝔹
false ≡ᵇ false = true
false ≡ᵇ true = false
true ≡ᵇ false = false
true ≡ᵇ true = true

_maybe-then_ : ∀{A B : Set} → Maybe A → (A → Maybe B) → Maybe B
(M maybe-then g)
    with M
... | nothing = nothing
... | just v = g v

binop : BinOp → Value → Value → Maybe Value
binop Sub v₁ v₂ =
  (toInt v₁) maybe-then
  λ n₁ → (toInt v₂) maybe-then
  λ n₂ → just (Int (n₁ - n₂))
binop Eq (Int n) (Int n′) = just (Bool (n ≤ᵇ n′))
binop Eq (Int n) (Bool b) = just (Bool false)
binop Eq (Bool b) (Int n) = just (Bool false)
binop Eq (Bool b) (Bool b′) = just (Bool (b ≡ᵇ b′))
binop LessEq v₁ v₂ =
  (toInt v₁) maybe-then
  λ n₁ → (toInt v₂) maybe-then
  λ n₂ → just (Bool (n₁ ≤ᵇ n₂))
binop And v₁ v₂ =
  (toBool v₁) maybe-then
  λ b₁ → (toBool v₂) maybe-then
  λ b₂ → just (Bool (b₁ ∧ b₂))

interp-exp : Exp → Env Value → Reader Value
interp-exp (Num n) ρ = return (Int n)
interp-exp (Bool b) ρ = return (Bool b)
interp-exp Read ρ = read-int Int
interp-exp (Uni op e) ρ =
  (interp-exp e ρ) then
  λ v → try (uniop op v)
interp-exp (Bin op e₁ e₂) ρ =
  (interp-exp e₁ ρ) then
  λ v₁ → (interp-exp e₂ ρ) then
  λ v₂ → try (binop op v₁ v₂)
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

