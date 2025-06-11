module LVarExplicateCorrect where

open import Agda.Builtin.Unit
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using ()
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; _≤ᵇ_; _∸_; _+_; s≤s)
open import Data.Nat.Properties
open import Data.Product
open import Data.Sum
open import Data.Integer using (ℤ; -_; _-_; 0ℤ)
open import Data.List
open import Data.List.Properties using (++-assoc; length-replicate; ++-identityʳ; length-++)
open import Data.Maybe
open import Relation.Binary.PropositionalEquality
   using (_≡_; refl; trans; sym; cong; cong-app)
open import Agda.Builtin.Bool
open import Relation.Nullary.Negation.Core using (¬_; contradiction)
open import Function.Base using (case_of_; case_returning_of_)

open import Reader
open import Utilities
open import LVar

--------------- Proof of correctness for Explicate Control -------------------

-- explicate-assign-correct : ∀ (x : Id) (m : IL-Exp) (c : CTail) (ρ : Env ℤ)
--    → interp-tail (explicate-assign x m c) ρ
--      ≡ (interp-mon m ρ then (λ v₁ → interp-tail c (v₁ ∷ ρ)))
-- explicate-assign-correct x (Assign y m₁ m₂) c ρ = ?
--   -- where
--   -- Goal : (s : Inputs)
--   --  → interp-tail (explicate-assign (Let m₁ m₂) c) ρ s
--   --    ≡ (interp-mon (Let m₁ m₂) ρ then (λ v₁ → interp-tail c (v₁ ∷ ρ))) s
--   -- Goal s
--   --     rewrite explicate-assign-correct m₁ (explicate-assign m₂ (shift-tail c 1)) ρ
--   --     with interp-mon m₁ ρ s
--   -- ... | nothing = refl
--   -- ... | just (v₁ , s1)
--   --     rewrite explicate-assign-correct m₂ (shift-tail c 1) (v₁ ∷ ρ)
--   --     with interp-mon m₂ (v₁ ∷ ρ) s1
--   -- ... | nothing = refl
--   -- ... | just (v₂ , s2)
--   --     rewrite interp-shift-tail c v₁ [ v₂ ] ρ 
--   --     = refl
-- explicate-assign-correct x (Atom a) c ρ = refl
-- explicate-assign-correct x Read c ρ = refl
-- explicate-assign-correct x (Sub a₁ a₂) m₂ ρ = refl

-- explicate-tail-correct : ∀ (m : IL-Exp) (ρ : Env ℤ) (s : Inputs)
--    → interp-tail (explicate m) ρ ≡ interp-mon m ρ
-- explicate-tail-correct (Atom x) ρ = refl
-- explicate-tail-correct Read ρ = refl
-- explicate-tail-correct (Sub a₁ a₂) ρ = refl
-- explicate-tail-correct (Assign y m₁ m₂) ρ = ?
--   --   where
--   -- Goal : (s : Inputs)
--   --   → interp-tail (explicate (Let m₁ m₂)) ρ s ≡ interp-mon (Let m₁ m₂) ρ s
--   -- Goal s
--   --     rewrite explicate-assign-correct m₁ (explicate m₂) ρ
--   --     with interp-mon m₁ ρ s
--   -- ... | nothing = refl
--   -- ... | just (v₁ , s1)
--   --     rewrite explicate-tail-correct m₂ (v₁ ∷ ρ)
--   --     = refl

explicate-correct : ∀ (p : IL-Prog) (s : Inputs) (v : ℤ)
  → interp-ilprog p s v
  → interp-prog (explicate p) s v
explicate-correct p s v ip = ?
 --rewrite explicate-tail-correct m [] = refl

