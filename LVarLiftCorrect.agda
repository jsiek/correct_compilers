module LVarLiftCorrect where

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
open import LVarInterpILShifts

--------------- Proof of correctness for Lift Locals -------------------

lift-locals-mon-correct : ∀ (m : Mon) (e : IL-Exp) (s s′ : Inputs) (v : ℤ) (ρ₁ ρ₂ : Env ℤ) (n : ℕ)
  → interp-mon m ρ₂ s ≡ just (v , s′)
  → lift-locals-mon m ≡ (n , e)
  → length ρ₁ ≡ n
  → Σ[ ρ′₁ ∈ Env ℤ ] (s , ρ₁ ++ ρ₂) ⊢ e ⇓ v ⊣ (s′ , ρ′₁ ++ ρ₂) × n ≡ length ρ′₁
lift-locals-mon-correct (Atom a) e s s′ v [] ρ₂ n im refl refl
    with interp-atm a ρ₂ in ia | im
... | just v | refl =
    [] , ⇓atom ia , refl
lift-locals-mon-correct Read e (i , f) s′ v [] ρ₂ n refl refl refl =
    [] , ⇓read , refl
lift-locals-mon-correct (Sub a₁ a₂) e s s′ v [] ρ₂ n im refl refl
    with interp-atm a₁ ρ₂ in ia₁ | im
... | just v₁ | im′
    with interp-atm a₂ ρ₂ in ia₂ | im′
... | just v₂ | refl
    = [] , ⇓sub ia₁ ia₂ , refl
lift-locals-mon-correct (Let m₁ m₂) e s s′ v ρ₁ ρ₂ n im lm lρ₁
    with lift-locals-mon m₁ in lm1 | lm
... | i , e₁ | lm′ 
    with lift-locals-mon m₂ in lm2 | lm′ 
... | j , e₂ | refl
    with interp-mon m₁ ρ₂ s in im1 | im
... | just (v₁ , s₁) | im2
    with ++-length ρ₁ (j + 1) i (trans lρ₁ (suc-i-j i j))
... | ρ′₁ , ρ₁₂ , refl , ρ′₁j1 , refl
    with ++-length ρ′₁ j 1 ρ′₁j1
... | ρ₁₁ , v′ ∷ [] , refl , refl , refl
    with lift-locals-mon-correct m₁ e₁ s s₁ v₁ ρ₁₂ ρ₂ (length ρ₁₂) im1 lm1 refl
... | ρ′₁₂ , e₁⇓v₁ , lρ′₁₂
--e₁⇓v₁ : (s , ρ₁₂ ++ ρ₂) ⊢ e₁ ⇓ v₁ ⊣ (s₁ , ρ′₁₂ ++ ρ₂)
    with ⇓shifts {ρ₁ = []}{[]}{ρ₂ = ρ₁₁ ++ [ v′ ]}{ρ₃ = ρ₁₂ ++ ρ₂} e₁⇓v₁
... | ρ′₁₁ , se1⇓v₁ , refl , lρ′₁₁
    rewrite (++-assoc (ρ₁₁ ++ v′ ∷ []) ρ₁₂ ρ₂)
    | length-++ ρ₁₁ {v′ ∷ []} | +-comm (length ρ₁₁) 1
-- se1⇓v₁ : (s , ρ₁₁ ++ [ v′ ] ++ ρ₁₂ ++ ρ₂) ⊢
--         shifts-ilexp e₁ 0 (length (ρ₁₁ ++ [ v′ ])) ⇓ v₁
--        ⊣ (s₁ , ρ′₁₁ ++ ρ′₁₂ ++ ρ₂)
    with ++-length (ρ′₁₁ ++ ρ′₁₂) (length ρ₁₁ + length ρ₁₂) 1
... | lenr11_r12 
    rewrite length-++ ρ′₁₁ {ρ′₁₂} | lρ′₁₂ | lρ′₁₁ | +-comm 1 (length ρ₁₁ + length ρ′₁₂)
    with lenr11_r12  refl
... | ρ″ , v″ ∷ [] , ρ″-eq , lρ″ , refl
    rewrite sym (++-assoc  ρ′₁₁ ρ′₁₂ ρ₂)
    | ρ″-eq
    with ++-length ρ″ (length ρ₁₁) (length ρ′₁₂) lρ″
... | ρ″₁₁ , ρ″₁₂ , refl , lρ″₁₁ , lρ″₁₂
    rewrite ++-assoc (ρ″₁₁ ++ ρ″₁₂) [ v″ ] ρ₂ | +-comm (length ρ′₁₂) (length ρ₁₁)
    | sym lρ″₁₁ | sym lρ″₁₂ | sym (length-++ ρ″₁₁ {ρ″₁₂})
    | sym (+-identityʳ (length (ρ″₁₁ ++ ρ″₁₂)))
    with lift-locals-mon-correct m₂ e₂ s₁ s′ v ρ″₁₁ (v₁ ∷ ρ₂) (length ρ″₁₁) im2 lm2 refl
... | ρ‴ , e₂⇓v₂ , lρ‴
--e₂⇓v₂  : (s₁ , ρ″₁₁ ++ v₁ ∷ ρ₂) ⊢ e₂ ⇓ v ⊣ (s′ , ρ‴ ++ v₁ ∷ ρ₂)
    with ⇓shifts {ρ₁ = ρ″₁₁}{ρ‴}{ρ₂ = ρ″₁₂}{ρ₃ = v₁ ∷ ρ₂} e₂⇓v₂
... | ρ₄ , se2⇓v₂ , eq11 , lρ₄        
    rewrite sym (++-assoc ρ″₁₁ ρ″₁₂ (v₁ ∷ ρ₂))
    | sym (update-++-+ (ρ″₁₁ ++ ρ″₁₂) (v″ ∷ ρ₂) 0 v₁)
    | sym (++-assoc ρ₄ [ v₁ ] ρ₂)
    | sym (++-assoc ρ‴ (ρ₄ ++ v₁ ∷ []) ρ₂)
    =
    ρ‴ ++ ρ₄ ++ [ v₁ ] , ⇓assign se1⇓v₁ se2⇓v₂ , Goal
    where
    Goal : suc (length (ρ″₁₁ ++ ρ″₁₂) + 0) ≡ length (ρ‴ ++ ρ₄ ++ [ v₁ ])
    Goal
        rewrite +-identityʳ (length (ρ″₁₁ ++ ρ″₁₂))
        | length-++ ρ″₁₁ {ρ″₁₂}
        | length-++ ρ‴ {ρ₄ ++ v₁ ∷ []}
        | length-++ ρ₄ {v₁ ∷ []}
        | sym lρ‴ | lρ₄
        | +-comm (length ρ″₁₂) 1
        | sym (+-assoc (length ρ″₁₁) 1 (length ρ″₁₂))
        | +-comm (length ρ″₁₁) 1
        = refl

lift-locals-correct : ∀ (m : Mon) (s : Inputs) (v : ℤ)
  → interp-LMonVar m s ≡ just v
  → interp-ilprog (lift-locals m) s v
lift-locals-correct m s v im
    with lift-locals-mon m in lm
... | n , e
    with interp-mon m [] s in im2 | im
... | just (v , s′) | refl
    with lift-locals-mon-correct m e s s′ v (replicate n 0ℤ) [] n im2 lm
           (length-replicate n)
... | ρ′₁ , e⇓ , n-eq
    rewrite ++-identityʳ (replicate n (ℤ.pos 0))
    = (s′ , ρ′₁ ++ []) , e⇓

