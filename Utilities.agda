module Utilities where

open import Agda.Builtin.Unit
import Data.Bool
open import Data.Nat using (ℕ; zero; suc; _≤ᵇ_; _≤_; _<_; _+_; s≤s; _∸_)
open import Data.Nat.Properties
open import Data.Product
open import Data.Integer using (ℤ; -_; _-_; 0ℤ)
open import Data.List
open import Data.Maybe
open import Relation.Binary.PropositionalEquality
   using (_≡_; refl; trans; sym; cong; cong-app)
open import Agda.Builtin.Bool
open import Relation.Nullary.Negation.Core using (¬_)

----------------- Variables and Environments ----------------------------

Id : Set
Id = ℕ

Env : Set → Set
Env A = List A

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

nth-++-shift-var : ∀{A : Set} (ρ₁ ρ₂ : Env A) (v : A) (x : Id)
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

postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------------------
    → f ≡ g
