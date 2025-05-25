module Reader where

open import Data.Nat using (ℕ; zero; suc; _≤ᵇ_)
open import Data.Product
open import Data.Sum
open import Data.Maybe
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
   using (_≡_; _≢_; refl; trans; sym; cong; cong-app)

----------------- Reader (ish) Monad ----------------------------

StateR : Set → Set
StateR A = ℕ × (ℕ → A)

Reader : Set → Set
Reader A = StateR A → Maybe (A × StateR A)

_then_ : ∀{A : Set} → Reader A → (A → Reader A) → Reader A
(M then g) s
    with M s
... | nothing = nothing
... | just (v , s') = g v s'

read : ∀{A} → Reader A
read (i , f) = just (f i , suc i , f)

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

data Succeed (A : Set) : (Reader A) → (StateR A) → Set where
  good : ∀ {M s} → M s ≢ nothing → Succeed A M s

value : ∀ {A : Set} (M : Reader A) (s : StateR A) → (Succeed A M s) → A
value {A} M s (good not-noth)
    with M s
... | nothing = ⊥-elim (not-noth refl)
... | just (v , s') = v

effect : ∀ {A : Set} (M : Reader A) (s : StateR A) → (Succeed A M s) → StateR A
effect {A} M s (good not-noth)
    with M s
... | nothing = ⊥-elim (not-noth refl)
... | just (v , s') = s'


-- Proof pattern for using succeed-or-fail and succeed-val-eff:
-- 
--     with succeed-or-fail M s
-- ... | inj₂ eq-noth rewrite eq-noth = ?
-- ... | inj₁ g
--     rewrite succeed-val-eff M s g = ?

succeed-or-fail : ∀{A} (M : Reader A) (s : StateR A)
  → (Succeed A M s) ⊎ M s ≡ nothing
succeed-or-fail{A} M s
    with M s in eq
... | nothing = inj₂ refl
... | just (v , s') = inj₁ (good λ {x → contra{A}{M} x eq})
  where
  contra : ∀{A}{M : Reader A}{ s s' v}
         → (M s ≡ nothing) → (M s ≡ just (v , s')) → ⊥
  contra a b rewrite b
      with a
  ... | ()

succeed-val-eff : ∀ {A : Set} (M : Reader A) (s : StateR A) → (g : Succeed A M s)
  → M s ≡ just (value M s g , effect M s g)
succeed-val-eff M s (good not-noth)
    with M s
... | nothing = ⊥-elim (not-noth refl)
... | just (v , s') = refl
