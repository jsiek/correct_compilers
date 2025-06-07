module State (St : Set) where

open import Data.Nat using (ℕ; zero; suc; _≤ᵇ_)
open import Data.Integer using (ℤ)
open import Data.Product
open import Data.List
open import Data.Sum
open import Data.Maybe
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
   using (_≡_; _≢_; refl; trans; sym; cong; cong-app)

----------------- State and Maybe Monad ----------------------------

Monad : Set → Set
Monad A = St  → Maybe (A × St)

_then_ : ∀{A B : Set} → Monad A → (A → Monad B) → Monad B
(M then g) s
    with M s
... | nothing = nothing
... | just (v , s') = g v s'

return : ∀{A : Set} → A → Monad A
return a s = just (a , s)

try : ∀{A : Set} → Maybe A → Monad A
try (just x) s = just (x , s)
try nothing s = nothing

run : ∀{A : Set} → Monad A → St → Maybe A
run r s
    with r s
... | nothing = nothing
... | just (v , s) = just v


