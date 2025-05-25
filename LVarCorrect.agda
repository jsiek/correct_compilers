module LVarCorrect where

open import Agda.Builtin.Unit
open import Data.Bool using ()
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; _≤ᵇ_; _∸_)
open import Data.Nat.Properties
open import Data.Product
open import Data.Sum
open import Data.Integer using (ℤ; -_; _-_; _+_)
open import Data.List
open import Data.Maybe
open import Relation.Binary.PropositionalEquality
   using (_≡_; refl; trans; sym; cong; cong-app)
open import Agda.Builtin.Bool
open import Relation.Nullary.Negation.Core using (¬_; contradiction)
open import Function.Base using (case_of_; case_returning_of_)

open import LVar
open import Reader

nth-++-< : ∀{A : Set} → (xs ys : List A) (x : ℕ)
       → x < length xs
       → nth (xs ++ ys) x ≡ nth xs x
nth-++-< {A} (x₁ ∷ xs) ys zero lt = refl
nth-++-< {A} (x₁ ∷ xs) ys (suc x) (_≤_.s≤s lt) = nth-++-< xs ys x lt

nth-++-≤ : ∀{A : Set} → (xs ys : List A) (x : ℕ)
       → length xs ≤ x
       → nth (xs ++ ys) x ≡ nth ys (x ∸ length xs)
nth-++-≤ {A} [] ys x lt = refl
nth-++-≤ {A} (x₁ ∷ xs) ys (suc x) (_≤_.s≤s lt) = nth-++-≤ xs ys x lt

eq-true-top : ∀{P} → P ≡ true → Data.Bool.T P
eq-true-top {P} eq rewrite eq = tt

eq-false-not-top : ∀{P} → P ≡ false → ¬ Data.Bool.T P
eq-false-not-top {P} eq rewrite eq = λ {()}

postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------------------
    → f ≡ g

interp-shift-atm : ∀ (a : Atm) (v : ℤ) (ρ₁ : Env) (ρ₂ : Env)
  → interp-atm (shift-atm a (length ρ₁)) (ρ₁ ++ v ∷ ρ₂) 
    ≡ interp-atm a (ρ₁ ++ ρ₂) 
interp-shift-atm a v ρ₁ ρ₂ = extensionality (Goal a)
  where
  Goal : (a : Atm )(s : StateR ℤ) →
      interp-atm (shift-atm a (length ρ₁)) (ρ₁ ++ v ∷ ρ₂) s ≡
      interp-atm a (ρ₁ ++ ρ₂) s
  Goal (Num x) s = refl
  Goal (Var x) s
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

interp-shift-mon : ∀ (m : Mon) (v : ℤ) (ρ₁ : Env) (ρ₂ : Env)
  → interp-mon (shift-mon m (length ρ₁)) (ρ₁ ++ (v ∷ ρ₂))
    ≡ interp-mon m (ρ₁ ++ ρ₂)
interp-shift-mon (Atom a) v ρ₁ ρ₂ = interp-shift-atm a v ρ₁ ρ₂
interp-shift-mon Read v ρ₁ ρ₂ = refl
interp-shift-mon (Sub a₁ a₂) v ρ₁ ρ₂ 
    rewrite interp-shift-atm a₁ v ρ₁ ρ₂ | interp-shift-atm a₂ v ρ₁ ρ₂ =
    extensionality Goal
    where
    Goal : (s : StateR ℤ) →
      (interp-atm a₁ (ρ₁ ++ ρ₂) then
      (λ v₁ → interp-atm a₂ (ρ₁ ++ ρ₂) then (λ v₂ → return (v₁ + - v₂)))) s
      ≡ (interp-atm a₁ (ρ₁ ++ ρ₂) then
         (λ v₁ → interp-atm a₂ (ρ₁ ++ ρ₂) then (λ v₂ → return (v₁ + - v₂)))) s
    Goal s
        with succeed-or-fail (interp-atm a₁ (ρ₁ ++ ρ₂)) s
    ... | inj₂ eq-noth rewrite eq-noth = refl
    ... | inj₁ g
        rewrite succeed-val-eff (interp-atm a₁ (ρ₁ ++ ρ₂)) s g
        = refl
interp-shift-mon (Let m₁ m₂) v ρ₁ ρ₂ 
  rewrite interp-shift-mon m₁ v ρ₁ ρ₂ = extensionality Goal
  where
  Goal : (s : StateR ℤ) →
          (interp-mon m₁ (ρ₁ ++ ρ₂) then
            (λ v₁ → interp-mon (shift-mon m₂ (suc (foldr (λ _ → suc) 0 ρ₁))) (v₁ ∷ ρ₁ ++ v ∷ ρ₂))) s
          ≡ (interp-mon m₁ (ρ₁ ++ ρ₂) then
             (λ v₁ → interp-mon m₂ (v₁ ∷ ρ₁ ++ ρ₂))) s
  Goal s
      with succeed-or-fail (interp-mon m₁ (ρ₁ ++ ρ₂)) s
  ... | inj₂ eq-noth rewrite eq-noth = refl
  ... | inj₁ g
      rewrite succeed-val-eff (interp-mon m₁ (ρ₁ ++ ρ₂)) s g
      | interp-shift-mon m₂ v ((value (interp-mon m₁ (ρ₁ ++ ρ₂)) s g) ∷ ρ₁) ρ₂
      = refl

rco-correct : ∀ (e : Exp) (ρ : Env)
  → interp-mon (rco e) ρ ≡ interp e ρ
rco-correct (Num x) ρ = refl
rco-correct Read ρ = refl
rco-correct (Sub e₁ e₂) ρ = extensionality Goal
  where
  Goal : (s : StateR ℤ) →
      (interp-mon (rco e₁) ρ then
       (λ v₁ → interp-mon (shift-mon (rco e₂) 0) (v₁ ∷ ρ) then
       (λ v₂ → return (v₁ - v₂)))) s
      ≡ (interp e₁ ρ then
        (λ v₁ → interp e₂ ρ then
        (λ v₂ → return (v₁ - v₂)))) s
  Goal s
      rewrite rco-correct e₁ ρ
      with succeed-or-fail (interp e₁ ρ) s
  ... | inj₂ eq-noth rewrite eq-noth = refl
  ... | inj₁ g
      rewrite succeed-val-eff (interp e₁ ρ) s g
      | interp-shift-mon (rco e₂) (value (interp e₁ ρ) s g) [] ρ
      | rco-correct e₂ ρ
      = refl
rco-correct (Var i₁) ρ = refl
rco-correct (Let e₁ e₂) ρ = extensionality Goal
  where
  Goal : (s : StateR ℤ) →
        (interp-mon (rco e₁) ρ then (λ v₁ → interp-mon (rco e₂) (v₁ ∷ ρ))) s
      ≡ (interp e₁ ρ then (λ v₁ → interp e₂ (v₁ ∷ ρ))) s
  Goal s
      rewrite rco-correct e₁ ρ
      with succeed-or-fail (interp e₁ ρ) s
  ... | inj₂ eq-noth rewrite eq-noth = refl
  ... | inj₁ g
      rewrite succeed-val-eff (interp e₁ ρ) s g
      | rco-correct e₂ (value (interp e₁ ρ) s g ∷ ρ)
      = refl
