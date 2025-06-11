module LVarInterpILShifts where

open import Agda.Builtin.Unit
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using ()
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; _≤ᵇ_; _∸_; _+_; s≤s)
open import Data.Nat.Properties
open import Data.Product
open import Data.Sum
open import Data.Integer using (ℤ; -_; _-_; 0ℤ)
open import Data.List
open import Data.List.Properties -- using (++-assoc; length-replicate; ++-identityʳ; length-++)
open import Data.Maybe
open import Relation.Binary.PropositionalEquality
   using (_≡_; refl; trans; sym; cong; cong-app)
open import Agda.Builtin.Bool
open import Relation.Nullary.Negation.Core using (¬_; contradiction)
open import Function.Base using (case_of_; case_returning_of_)

open import Reader
open import Utilities
open import LVar
open import LVarRCOCorrect

--------------- Proof of correctness for Lift Locals -------------------

interp-shifts-atm : ∀ (a : Atm) (ρ₁ ρ₂ ρ₃ : Env ℤ)
  → interp-atm (shifts-atm a (length ρ₁) (length ρ₂)) (ρ₁ ++ ρ₂ ++ ρ₃)
  ≡ interp-atm a (ρ₁ ++ ρ₃)
interp-shifts-atm (Num x) ρ₁ ρ₂ ρ₃ = refl
interp-shifts-atm (Var x) ρ₁ ρ₂ ρ₃
    with length ρ₁ ≤ᵇ x in lt
... | true
    with m≤n⇒-+ (length ρ₁) x (≤ᵇ⇒≤ (length ρ₁) x (eq-true-top lt))
... | k , eq
    rewrite sym eq
    | sym (+-assoc (length ρ₂) (length ρ₁) k)
    | +-comm (length ρ₂) (length ρ₁)
    | (+-assoc (length ρ₁) (length ρ₂) k)
    | nth-++-+ ρ₁ (ρ₂ ++ ρ₃) (length ρ₂ + k)
    | nth-++-+ ρ₂ ρ₃ k
    | nth-++-+ ρ₁ ρ₃ k
    = refl
interp-shifts-atm (Var x) ρ₁ ρ₂ ρ₃ | false
    rewrite nth-++-< ρ₁ (ρ₂ ++ ρ₃) x (≰⇒> λ x₁ → (eq-false-not-top lt) (≤⇒≤ᵇ x₁))
    | nth-++-< ρ₁ ρ₃ x (≰⇒> λ x₁ → (eq-false-not-top lt) (≤⇒≤ᵇ x₁))
    = refl

⇓atom-elim : ∀{s s′ ρ ρ′ a v}
   → (s , ρ) ⊢ Atom a ⇓ v ⊣ (s′ , ρ′)
   → interp-atm a ρ ≡ just v × s ≡ s′ × ρ ≡ ρ′
⇓atom-elim (⇓atom eq) = eq , (refl , refl)

⇓read-elim : ∀{i f i' f' ρ ρ′ v}
   → ((i , f) , ρ) ⊢ Read ⇓ v ⊣ ((i' , f') , ρ′)
   → i' ≡ suc i × f' ≡ f × v ≡ f i × ρ′ ≡ ρ
⇓read-elim ⇓read = refl , refl , refl , refl

⇓sub-elim : ∀{s s' ρ ρ'}
   → (s , ρ) ⊢ Sub a₁ a₂ ⇓ (s' , ρ')

⇓shifts : ∀ {e : IL-Exp}{v : ℤ} {s s′ : Inputs} {ρ₁ ρ′₁ ρ₂ ρ₃ ρ′₃ : Env ℤ} 
  → (s , ρ₁ ++ ρ₃) ⊢ e ⇓ v ⊣ (s′ , ρ′₁ ++ ρ′₃)
  → length ρ′₁ ≡ length ρ₁
  → Σ[ ρ′₂ ∈ Env ℤ ] (s , ρ₁ ++ ρ₂ ++ ρ₃) ⊢
      shifts-ilexp e (length ρ₁) (length ρ₂) ⇓ v ⊣ (s′ , ρ′₁ ++ ρ′₂ ++ ρ′₃)
    × length ρ′₂ ≡ length ρ₂
⇓shifts {Atom a} {v} {s} {s′}{ρ₁}{ρ′₁}{ρ₂}{ρ₃}{ρ′₃} e⇓v lρ1
    with ⇓atom-elim e⇓v
... | ia , refl , eq2 
    with length≡++{ℤ}{ρ₁}{ρ′₁}{ρ₃}{ρ′₃} (sym lρ1) eq2
... | refl , refl
    =
    ρ₂ , ⇓atom Subgoal , refl
    where
    Subgoal : interp-atm (shifts-atm a (length ρ₁) (length ρ₂)) (ρ₁ ++ ρ₂ ++ ρ₃) ≡ just v
    Subgoal rewrite interp-shifts-atm a ρ₁ ρ₂ ρ₃ = ia

⇓shifts {Read} {v} {i , f} {i' , f'}{ρ₁}{ρ′₁}{ρ₂}{ρ₃}{ρ′₃} e⇓v lρ1
    with ⇓read-elim e⇓v
... | refl , refl , refl , eq4
    with length≡++{ℤ}{ρ₁}{ρ′₁}{ρ₃}{ρ′₃} (sym lρ1) (sym eq4)
... | refl , refl
    = ρ₂ , (⇓read , refl)

⇓shifts {Sub a₁ a₂} {v} {s} {s′} e⇓v lρ1 = {!!}

⇓shifts {Assign x e₁ e₂} {v} {s} {s′} e⇓v lρ1 = {!!}
