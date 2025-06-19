module LVarExplicateCorrect where

open import Data.Nat using (ℕ)
open import Data.Product
open import Data.Integer using (ℤ; _-_; 0ℤ)
open import Data.List using (replicate)
open import Data.Maybe
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Reader
open import Utilities
open import LVar

--------------- Proof of correctness for Explicate Control -------------------

explicate-assign-correct : ∀(x : Id)(e : IL-Exp)(t : CStmt) (ρ ρ′ ρ″ : Env ℤ) (s s′ s″ : Inputs)
    (n v : ℤ)
  → (s , ρ) ⊢ e ⇓ n ⊣ (s′ , ρ′)
  → (s′ , update ρ′ x n) ⊢ᶜ t ⇓ v ⊣ (s″ , ρ″)
  → (s , ρ) ⊢ᶜ explicate-assign x e t ⇓ v ⊣ (s″ , ρ″)
explicate-assign-correct x (Atom a) t ρ ρ′ ρ″ s s′ s″ n v (⇓atom ia) t⇓v =
  ⇓assign Goal t⇓v
  where
  Goal : try (interp-atm a ρ) s ≡ just (n , s)
  Goal rewrite ia = refl
explicate-assign-correct x Read t ρ ρ′ ρ″ s s′ s″ n v ⇓read t⇓v = ⇓assign refl t⇓v
explicate-assign-correct x (Sub a₁ a₂) t ρ ρ′ ρ″ s s′ s″ n v (⇓sub{n₁ = n₁}{n₂} ia₁ ia₂) t⇓v =
    ⇓assign Goal t⇓v
    where
    Goal : (try (interp-atm a₁ ρ) then
            (λ v₁ → try (interp-atm a₂ ρ) then (λ v₂ → return (v₁ - v₂)))) s
            ≡ just (n₁ - n₂ , s)
    Goal rewrite ia₁ | ia₂ = refl
explicate-assign-correct x (Assign y e₁ e₂) t ρ ρ′ ρ″ s s′ s″ n v
   (⇓assign {ρ′ = ρ′₁}{n₁ = n₁} e₁⇓n₁ e₂⇓v) t⇓v =
   let ee₂⇓v = explicate-assign-correct x e₂ t (update ρ′₁ y n₁) ρ′ ρ″ _ s′ s″ n v e₂⇓v t⇓v in
   explicate-assign-correct y e₁ (explicate-assign x e₂ t)  ρ ρ′₁ ρ″ s _ s″ n₁ v e₁⇓n₁ ee₂⇓v

explicate-tail-correct : ∀ (e : IL-Exp) (ρ ρ' : Env ℤ) (s s' : Inputs) (v : ℤ)
  → (s , ρ) ⊢ e ⇓ v ⊣ (s' , ρ')
  → (s , ρ) ⊢ᶜ explicate-tail e ⇓ v ⊣ (s' , ρ')
explicate-tail-correct (Atom a) ρ ρ' s s' v (⇓atom ia) = ⇓return Goal
  where Goal : try (interp-atm a ρ) s ≡ just (v , s)
        Goal rewrite ia = refl
explicate-tail-correct Read ρ ρ' s s' v ⇓read = ⇓return refl
explicate-tail-correct (Sub a₁ a₂) ρ ρ' s s' v (⇓sub{n₁ = n₁}{n₂} ia1 ia2) = ⇓return Goal
  where Goal : (try (interp-atm a₁ ρ) then
               (λ v₁ → try (interp-atm a₂ ρ) then (λ v₂ → return (v₁ - v₂)))) s
                ≡ just (n₁ - n₂ , s)
        Goal rewrite ia1 | ia2 = refl
explicate-tail-correct (Assign x e₁ e₂) ρ ρ' s s' v (⇓assign {s′ = s′}{ρ′}{n₁ = n₁} e₁⇓n₁ e₂⇓v) =
  let IH2 = explicate-tail-correct e₂ (update ρ′ x n₁) ρ' s′ s' v e₂⇓v in
  explicate-assign-correct x e₁ (explicate-tail e₂) ρ ρ′ ρ' s s′ s' n₁ v e₁⇓n₁ IH2

explicate-correct : ∀ (p : IL-Prog) (s : Inputs) (v : ℤ)
  → interp-imp p s v
  → interp-prog (explicate p) s v
explicate-correct (Program n e) s v ((s' , ρ') , e⇓v) =
    ((s' , ρ')) , explicate-tail-correct e (replicate n 0ℤ) ρ' s s' v e⇓v
    

