module Reader where

open import Data.Nat using (ℕ; zero; suc; _≤ᵇ_)
open import Data.Integer using (ℤ)
open import Data.Product
open import Data.Sum
open import Data.Maybe
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
   using (_≡_; _≢_; refl; trans; sym; cong; cong-app)

----------------- Reader (ish) Monad ----------------------------

-- stream of integers
Inputs : Set
Inputs = ℕ × (ℕ → ℤ)

Reader : Set → Set
Reader A = Inputs → Maybe (A × Inputs)

_then_ : ∀{A B : Set} → Reader A → (A → Reader B) → Reader B
(M then g) s
    with M s
... | nothing = nothing
... | just (v , s') = g v s'

read : Reader ℤ
read (i , f) = just (f i , (suc i , f))

return : ∀{A : Set} → A → Reader A
return a s = just (a , s)

try : ∀{A : Set} → Maybe A → Reader A
try (just x) s = just (x , s)
try nothing s = nothing

_⨟_ : ∀{A : Set} → Reader A → Reader A → Reader A
(M₁ ⨟ M₂) s
    with M₁ s
... | nothing = nothing
... | just (v , s') = M₂ s'

run : ∀{A : Set} → Reader A → Inputs → Maybe A
run r s
    with r s
... | nothing = nothing
... | just (v , s) = just v
