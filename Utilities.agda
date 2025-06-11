module Utilities where

open import Agda.Builtin.Unit
import Data.Bool
open import Data.Nat using (ℕ; zero; suc; _≤ᵇ_; _≤_; _<_; _+_; s≤s; _∸_)
open import Data.Nat.Properties
open import Data.Product
open import Data.Integer using (ℤ; -_; _-_; 0ℤ)
open import Data.List
open import Data.List.Properties -- using (++-assoc)
open import Data.Maybe
open import Relation.Binary.PropositionalEquality
   using (_≡_; refl; trans; sym; cong; cong-app; cong₂)
open import Agda.Builtin.Bool
open import Relation.Nullary.Negation.Core using (¬_)

----------------- Variables and Environments ----------------------------

Id : Set
Id = ℕ

Env : Set → Set
Env A = List A

-- stream of integers for input
Inputs : Set
Inputs = ℕ × (ℕ → ℤ)

nth : ∀{A : Set} → Env A → Id → Maybe A
nth [] i = nothing
nth (x ∷ xs) zero    = just x
nth (x ∷ xs) (suc i) = nth xs i

update : ∀{A : Set} → Env A → Id → A → Env A
update [] i v = []
update (x ∷ xs) zero v = v ∷ xs
update (x ∷ xs) (suc i) v = x ∷ update xs i v

shift-var : Id → ℕ → Id
shift-var x c
    with c Data.Nat.≤ᵇ x
... | true = suc x
... | false = x

shifts-var : Id → ℕ → ℕ → Id
shifts-var x c n
    with c Data.Nat.≤ᵇ x
... | true = n + x
... | false = x

--- Properties

update-correct : ∀ {A} (xs ys : List A) (v v' : A)
  → update (xs ++ v ∷ ys) (length xs) v' ≡ xs ++ v' ∷ ys
update-correct [] ys v v' = refl
update-correct (x ∷ xs) ys v v' rewrite update-correct xs ys v v' = refl

++-length : ∀ {A : Set} (xs : List A) (m n : ℕ)
  → length xs ≡ (m + n)
  → Σ[ ys ∈ List A ] Σ[ zs ∈ List A ] (xs ≡ ys ++ zs × length ys ≡ m × length zs ≡ n)
++-length xs zero n len_mn = [] , xs , refl , refl , len_mn
++-length (x ∷ xs) (suc m) n len_mn
    with ++-length xs m n (suc-injective len_mn)
... | ys , zs , refl , refl , refl
    = x ∷ ys , zs , refl , refl , refl

++-length-+-1 : ∀ {A : Set} (xs : List A) (m : ℕ)
  → length xs ≡ (m + 1)
  → Σ[ ys ∈ List A ] Σ[ z ∈ A ] (xs ≡ ys ++ [ z ] × length ys ≡ m)
++-length-+-1 xs m eq
    with ++-length xs m 1 eq
... | ys , z ∷ [] , refl , refl , eq2
    = ys , z , refl , refl

m≤n⇒-+ : ∀ (m n : ℕ)
  → m ≤ n
  → Σ[ l ∈ ℕ ] m + l ≡ n
m≤n⇒-+ zero n mn = n , refl
m≤n⇒-+ (suc m) (suc n) (s≤s mn)
    with m≤n⇒-+ m n mn
... | l , refl = l , refl

nth-++-< : ∀{A : Set} → (xs ys : List A) (x : ℕ)
       → x < length xs
       → nth (xs ++ ys) x ≡ nth xs x
nth-++-< {A} (x₁ ∷ xs) ys zero lt = refl
nth-++-< {A} (x₁ ∷ xs) ys (suc x) (_≤_.s≤s lt) = nth-++-< xs ys x lt

-- TODO: replace uses of nth-++-≤ with nth-++-+
nth-++-≤ : ∀{A : Set} → (xs ys : List A) (x : ℕ)
       → length xs ≤ x
       → nth (xs ++ ys) x ≡ nth ys (x ∸ length xs)
nth-++-≤ {A} [] ys x lt = refl
nth-++-≤ {A} (x₁ ∷ xs) ys (suc x) (_≤_.s≤s lt) = nth-++-≤ xs ys x lt

nth-++-+ : ∀{A : Set} → (xs ys : List A) (n : ℕ)
       → nth (xs ++ ys) (length xs + n) ≡ nth ys n
nth-++-+ {A} [] ys n = refl
nth-++-+ {A} (x ∷ xs) ys n = nth-++-+ xs ys n

nth-++-length : ∀{A : Set} → (xs ys : List A) (y : A)
       → nth (xs ++ y ∷ ys) (length xs) ≡ just y
nth-++-length {A} [] ys y = refl
nth-++-length {A} (x ∷ xs) ys y = nth-++-length xs ys y

nth-++-1 : ∀ {A : Set} (B : List A) (t : A)
  → nth (B ++ [ t ]) (length B) ≡ just t
nth-++-1 B t rewrite sym (+-identityʳ (length B))
    | nth-++-+ B [ t ] 0
    = refl

nth-++-just : ∀{A : Set} (xs ys : List A) (i : ℕ) (v : A)
  → nth xs i ≡ just v
  → nth (xs ++ ys) i ≡ just v
nth-++-just (x ∷ xs) ys zero v eq = eq
nth-++-just (x ∷ xs) ys (suc i) v eq = nth-++-just xs ys i v eq

nth-update : ∀ {A : Set} (ρ : List A) (x : Id) (v : A)
  → x < length ρ
  → nth (update ρ x v) x ≡ just v
nth-update (v' ∷ ρ) zero v lt = refl
nth-update (v' ∷ ρ) (suc x) v (s≤s lt) = nth-update ρ x v lt

update-length : ∀ {A : Set} (ρ : List A) (x : Id) (v : A)
  → length (update ρ x v) ≡ length ρ
update-length [] x v = refl
update-length (z ∷ ρ) zero v = refl
update-length (z ∷ ρ) (suc x) v rewrite update-length ρ x v = refl

eq-true-top : ∀{P} → P ≡ true → Data.Bool.T P
eq-true-top {P} eq rewrite eq = tt

eq-false-not-top : ∀{P} → P ≡ false → ¬ Data.Bool.T P
eq-false-not-top {P} eq rewrite eq = λ {()}

nth-++-shift-var : ∀{A : Set} (ρ₁ ρ₂ : List A) (v : A) (x : Id)
  → nth (ρ₁ ++ v ∷ ρ₂) (shift-var x (length ρ₁))
    ≡ nth (ρ₁ ++ ρ₂) x
nth-++-shift-var ρ₁ ρ₂ v x
    with (length ρ₁) ≤ᵇ x in lt
... | true
    rewrite nth-++-≤ ρ₁ ρ₂ x (≤ᵇ⇒≤ (length ρ₁) x (eq-true-top lt))
    | nth-++-≤ ρ₁ (v ∷ ρ₂) (suc x) (≤-trans ((≤ᵇ⇒≤ (length ρ₁) x (eq-true-top lt))) (n≤1+n x))
    | +-∸-assoc 1 {x}{length ρ₁} (≤ᵇ⇒≤ (length ρ₁) x (eq-true-top lt)) =
      refl
... | false
    rewrite nth-++-< ρ₁ ρ₂ x (≰⇒> λ x₁ → (eq-false-not-top lt) (≤⇒≤ᵇ x₁))
    | nth-++-< ρ₁ (v ∷ ρ₂) x ((≰⇒> λ x₁ → (eq-false-not-top lt) (≤⇒≤ᵇ x₁))) =
   refl  

nth-++-shifts-var : ∀{A : Set} (ρ₁ ρ₂ ρ₃ : List A) (x : Id)
  → nth (ρ₁ ++ (ρ₂ ++ ρ₃)) (shifts-var x (length ρ₁) (length ρ₂))
    ≡ nth (ρ₁ ++ ρ₃) x
nth-++-shifts-var ρ₁ ρ₂ ρ₃ x
    with (length ρ₁) ≤ᵇ x in lt
... | true
    with m≤n⇒-+ (length ρ₁) x (≤ᵇ⇒≤ (length ρ₁) x (eq-true-top lt))
... | i , refl
    rewrite sym (+-assoc (length ρ₂) (length ρ₁) i)
    | +-comm (length ρ₂) (length ρ₁)
    | +-assoc (length ρ₁) (length ρ₂) i
    | nth-++-+ ρ₁ (ρ₂ ++ ρ₃) (length ρ₂ + i)
    | nth-++-+ ρ₂ ρ₃ i
    | nth-++-+ ρ₁ ρ₃ i
    = refl
nth-++-shifts-var ρ₁ ρ₂ ρ₃ x
    | false
    rewrite nth-++-< ρ₁ (ρ₂ ++ ρ₃) x (≰⇒> λ x₁ → (eq-false-not-top lt) (≤⇒≤ᵇ x₁))
    | nth-++-< ρ₁ ρ₃ x (≰⇒> λ x₁ → (eq-false-not-top lt) (≤⇒≤ᵇ x₁))
    = refl

update-++-< : ∀{A : Set} → (xs ys : List A) (n : ℕ) (v : A)
       → n < length xs
       → update (xs ++ ys) n v ≡ update xs n v ++ ys
update-++-< {A} (x₁ ∷ xs) ys zero v lt = refl
update-++-< {A} (x₁ ∷ xs) ys (suc x) v (_≤_.s≤s lt)
  rewrite update-++-< xs ys x v lt = refl

update-++-+ : ∀{A : Set} → (xs ys : List A) (n : ℕ) (v : A)
  → update (xs ++ ys) (length xs + n) v ≡ xs ++ update ys n v
update-++-+ [] ys n v = refl
update-++-+ (x ∷ xs) ys n v = cong (x ∷_) (update-++-+ xs ys n v)

update-+ : ∀{A : Set} (xs : List A) (i : ℕ) (v : A)
    → update xs (length xs + i) v ≡ xs
update-+ [] i v = refl
update-+ (x ∷ xs) i v = cong (x ∷_) (update-+ xs i v)

cons-++ : ∀ {A : Set}(x : A)(xs ys zs : List A)
  → x ∷ xs ≡ zs
  → x ∷ xs ++ ys ≡ zs ++ ys
cons-++ x xs ys zs refl = refl

replicate-+ : ∀ {A : Set} (m n : ℕ) (v : A)
  → replicate (m + n) v ≡ replicate m v ++ replicate n v
replicate-+ zero n v = refl
replicate-+ (suc m) n v rewrite replicate-+ m n v = refl

suc-i-j : ∀ (i j : ℕ)
    → suc (i + j) ≡ j + 1 + i
suc-i-j i j
  rewrite +-comm i j | +-comm j 1 = refl

length≡++ : ∀{A : Set}{xs xs′ ys ys′ : List A}
  → length xs ≡ length xs′
  → xs ++ ys ≡ xs′ ++ ys′
  → xs ≡ xs′ × ys ≡ ys′
length≡++ {A} {[]} {[]} refl refl = refl , refl
length≡++ {A} {x ∷ xs} {x₁ ∷ xs′}{ys}{ys′} len app≡
    with ∷-injective app≡
... | refl , eq =
  let IH = length≡++{A}{xs}{xs′}{ys}{ys′} (suc-injective len)  eq in
  (cong₂ _∷_ refl (proj₁ IH) ) , proj₂ IH

postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------------------
    → f ≡ g
