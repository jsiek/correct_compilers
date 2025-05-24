module Reader where

open import Data.Nat using (ℕ; zero; suc; _≤ᵇ_)
open import Data.Product
open import Data.Sum
open import Data.Maybe
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
   using (_≡_; refl; trans; sym; cong; cong-app)

----------------- Reader (ish) Monad ----------------------------

abstract
  StateR : Set → Set
  StateR A = ℕ × (ℕ → A)

Reader : Set → Set
Reader A = StateR A → Maybe (A × StateR A)

abstract
  read : ∀{A} → Reader A
  read (i , f) = just (f i , suc i , f)

  return : ∀{A : Set} → A → Reader A
  return a s = just (a , s)

  try : ∀{A : Set} → Maybe A → Reader A
  try (just x) s = just (x , s)
  try nothing (i , s) = nothing

  _then_ : ∀{A : Set} → Reader A → (A → Reader A) → Reader A
  (M then g) s
      with M s
  ... | nothing = nothing
  ... | just (v , s') = g v s'

  _⨟_ : ∀{A : Set} → Reader A → Reader A → Reader A
  (M₁ ⨟ M₂) s
      with M₁ s
  ... | nothing = nothing
  ... | just (v , s') = M₂ s'

  try-just : ∀{A : Set} (v : A)
      → try (just v) ≡ return v
  try-just {A} v = refl

  ret-then : ∀{A : Set} → (v : A) → (f : A → Reader A)
           → (return v) then f ≡ f v
  ret-then {A} v f = refl

  _returns_ : ∀{A} → Reader A → A → StateR A → Set
  (M returns v) s
      with M s
  ... | just (v' , s') = v ≡ v'
  ... | nothing = ⊥

  fails : ∀{A : Set} → Reader A → StateR A → Set
  fails M s
      with M s
  ... | just (v' , s') = ⊥
  ... | nothing = ⊤

  return-or-fail : ∀{A : Set} (M : Reader A) (s : StateR A)
    → (Σ[ v ∈ A ] (M returns v) s) ⊎ (fails M s)
  return-or-fail{A} M s
      with M s
  ... | nothing = inj₂ tt
  ... | just (v , s') = inj₁ (v , refl)

  ret-then-seq : ∀{A} {M₁ : Reader A} {v : A}{s : StateR A}
    → (M₁ returns v) s
    → (g : A → Reader A)
    → (M₁ then g) s ≡ (M₁ ⨟ g v) s
  ret-then-seq {A}{M₁}{v}{s} M₁v g 
      with M₁ s
  ... | nothing = refl
  ... | just (v , s')
      with M₁v
  ... | refl = refl

  fail-then : ∀{A}{s}
     → (M₁ : Reader A)
    → (fails M₁) s
    → (g : A → Reader A)
    → (M₁ then g) s ≡ M₁ s
  fail-then {A}{s} M₁ M₁v g 
      with M₁ s
  ... | nothing = refl
  ... | just (v , s')
      with M₁v
  ... | ()

  seq-same-start : ∀{A}{s : StateR A} (M₁ : Reader A) {M₂ M₃}
    → (∀ (s' : StateR A) → M₂ s' ≡ M₃ s')
    → (M₁ ⨟ M₂) s ≡ (M₁ ⨟ M₃) s
  seq-same-start {A}{s} M₁ M23
      with M₁ s
  ... | just (v , s') = M23 s'
  ... | nothing = refl
