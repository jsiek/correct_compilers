module LMonIf where

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
open import LIf

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
  λ v → try (uniop op v)
interp-mon (Bin op a₁ a₂) ρ =
  try (interp-atm a₁ ρ) then
  λ v₁ → try (interp-atm a₂ ρ) then
  λ v₂ → try (binop op v₁ v₂)
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
