module IL1 where

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
open import Utilities
open import LIf
open import LMonIf

----------------- Definition of IL1If ----------------------------

open import State (Inputs × Env Value)

ret : ∀{A : Set} → Maybe A → Inputs → Env Value → Maybe (A × Inputs × Env Value)
ret (just v) s ρ = just (v , s , ρ)
ret nothing s ρ = nothing

pure : ∀{A : Set}(f : Env Value → Maybe A) → Monad A
pure f (s , ρ) = ret (f ρ) s ρ

input : Monad Value
input ((i , f) , ρ) = just (Int (f i) , (suc i , f) , ρ)

write : Id → Value → Monad ⊤
write x v (s , ρ) = just (tt , s , update ρ x v)

data IL1-Exp : Set where
  Atom : Atm → IL1-Exp
  Read : IL1-Exp
  Uni : UniOp → Atm → IL1-Exp
  Bin : BinOp → Atm → Atm → IL1-Exp
  Assign : Id → IL1-Exp → IL1-Exp → IL1-Exp
  If : IL1-Exp → IL1-Exp → IL1-Exp → IL1-Exp

data IL1-Prog : Set where
  Program : ℕ → IL1-Exp → IL1-Prog

interp-il1-exp : IL1-Exp → Monad Value
interp-il1-exp (Atom atm) = pure (interp-atm atm)
interp-il1-exp Read = input
interp-il1-exp (Uni op a) =
  pure (interp-atm a) then
  λ v → try (uniop op v)
interp-il1-exp (Bin op a₁ a₂) =
  pure (interp-atm a₁) then
  λ v₁ → pure (interp-atm a₂) then
  λ v₂ → try (binop op v₁ v₂)
interp-il1-exp (Assign x e₁ e₂) =
  (interp-il1-exp e₁) then
  λ v₁ → (write x v₁) then
  λ _ → interp-il1-exp e₂
interp-il1-exp (If e₁ e₂ e₃) =
  (interp-il1-exp e₁) then
  λ v₁ → try (toBool v₁) then
  λ { true → interp-il1-exp e₂
    ; false → interp-il1-exp e₃ }

interp-IL1 : IL1-Prog → Inputs → Maybe Value
interp-IL1 (Program n e) s =
    run (interp-il1-exp e) (s , replicate n (Int 0ℤ))

