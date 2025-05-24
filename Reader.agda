module Reader where

open import Data.Nat using (ℕ; zero; suc; _≤ᵇ_)
open import Data.Product
open import Data.Maybe
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
   using (_≡_; refl; trans; sym; cong; cong-app)

----------------- Reader (ish) Monad ----------------------------

Reader : Set → Set
Reader A = ℕ → (ℕ → A) → (Maybe A) × ℕ × (ℕ → A)

read : ∀{A} → Reader A
read i f = just (f i) , suc i , f

return : ∀{A : Set} → A → Reader A
return a i f = just a , i , f

try : ∀{A : Set} → Maybe A → Reader A
try a i f = a , i , f

_then_ : ∀{A : Set} → Reader A → (A → Reader A) → Reader A
(M then g) i f
    with M i f
... | nothing , i' , f' = nothing , i' , f'
... | just v , i' , f' = g v i' f'

_⨟_ : ∀{A : Set} → Reader A → Reader A → Reader A
(M₁ ⨟ M₂) i f
    with M₁ i f
... | nothing , i' , f' = nothing , i' , f'
... | just v , i' , f' = M₂ i' f'

ret-then : ∀{A : Set} → (v : A) → (f : A → Reader A)
         → (return v) then f ≡ f v
ret-then {A} v f = refl

--caseR : ∀{X A B C : Set} (M : Reader X) → (A → C) → (B → C) → C
--caseR M good bad = {!!}

_returns_ : ∀{A} → Reader A → A → ℕ → (ℕ → A) → Set
(M returns v) i f
      with M i f
... | just v' , i' , f' = v ≡ v'
... | nothing , i' , f' = ⊥

fails : ∀{A} → Reader A → ℕ → (ℕ → A) → Set
fails M i f
      with M i f
... | just v' , i' , f' = ⊥
... | nothing , i' , f' = ⊤

ret-then-seq : ∀{A} → (M₁ : Reader A) (v : A) (g : A → Reader A)
  → (i : ℕ) → (f : ℕ → A)
  → (M₁ returns v) i f
  → (M₁ then g) i f ≡ (M₁ ⨟ g v) i f
ret-then-seq {V} M₁ v g i f M₁v
    with M₁ i f
... | nothing , i' , f' = refl
... | just v , i' , f'
    with M₁v
... | refl = refl

fail-then : ∀{A} → (M₁ : Reader A) (g : A → Reader A)
  → (i : ℕ) → (f : ℕ → A)
  → (fails M₁) i f
  → (M₁ then g) i f ≡ M₁ i f
fail-then {V} M₁ g i f M₁v
    with M₁ i f
... | nothing , i' , f' = refl
... | just v , i' , f'
    with M₁v
... | ()


-- → (∀ v → M returns v × P (M for-effect (f v)))
  -- → P nothing
  -- → P (M then f)
