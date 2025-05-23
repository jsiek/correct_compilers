module LVarCorrect where

open import Agda.Builtin.Unit
open import Data.Bool using ()
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; _≤ᵇ_; _∸_)
open import Data.Nat.Properties
open import Data.Product
open import Data.Integer using (ℤ; -_; _-_)
open import Data.List
open import Data.Maybe
open import Relation.Binary.PropositionalEquality
   using (_≡_; refl; trans; sym; cong; cong-app)
open import Agda.Builtin.Bool
open import Relation.Nullary.Negation.Core using (¬_; contradiction)

open import LVar

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
  extensionality2 : ∀ {A B C : Set} {f g : A → B → C}
    → (∀ (x : A) (y : B) → f x y ≡ g x y)
      -----------------------------------
    → f ≡ g

interp-shift-atm : ∀ (a : Atm) (v : ℤ) (ρ₁ : Env) (ρ₂ : Env)
  → interp-atm (shift-atm a (length ρ₁)) (ρ₁ ++ v ∷ ρ₂) 
    ≡ interp-atm a (ρ₁ ++ ρ₂) 
interp-shift-atm a v ρ₁ ρ₂ = extensionality2 (Goal a)
  where
  Goal : (a : Atm )(i : ℕ) (f : ℕ → ℤ) →
      interp-atm (shift-atm a (length ρ₁)) (ρ₁ ++ v ∷ ρ₂) i f ≡
      interp-atm a (ρ₁ ++ ρ₂) i f
  Goal (Num x) i f = refl
  Goal (Var x) i f
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
interp-shift-mon (Sub a₁ a₂) v ρ₁ ρ₂  = extensionality2 Goal
  where
  Goal : (i : ℕ) (f : ℕ → ℤ) →
      (interp-atm (shift-atm a₁ (length ρ₁)) (ρ₁ ++ v ∷ ρ₂) then
       (λ v₁ → interp-atm (shift-atm a₂ (length ρ₁)) (ρ₁ ++ v ∷ ρ₂) then
       (λ v₂ → return (v₁ - v₂)))) i f
      ≡ (interp-atm a₁ (ρ₁ ++ ρ₂) then
        (λ v₁ → interp-atm a₂ (ρ₁ ++ ρ₂) then (λ v₂ → return (v₁ - v₂)))) i f
  Goal i f
      rewrite interp-shift-atm a₁ v ρ₁ ρ₂
      | interp-shift-atm a₂ v ρ₁ ρ₂ 
      with interp-atm a₁ (ρ₁ ++ ρ₂) i f
  ... | nothing , i' , f' = refl
  ... | just v₁ , i' , f'
      with interp-atm a₂ (ρ₁ ++ ρ₂) i' f'
  ... | nothing , i'' , f'' = refl
  ... | just v₂ , i'' , f'' = refl
interp-shift-mon (Let m₁ m₂) v ρ₁ ρ₂ 
  rewrite interp-shift-mon m₁ v ρ₁ ρ₂ = extensionality2 Goal
  where
  Goal : (i : ℕ) (f : ℕ → ℤ) →
       ((interp-mon m₁ (ρ₁ ++ ρ₂) then
        (λ v₁ → interp-mon (shift-mon m₂ (suc (foldr (λ _ → suc) 0 ρ₁))) (v₁ ∷ ρ₁ ++ v ∷ ρ₂)))) i f
         ≡ ((interp-mon m₁ (ρ₁ ++ ρ₂) then (λ v₁ → interp-mon m₂ (v₁ ∷ ρ₁ ++ ρ₂)))) i f
  Goal i f
      with interp-mon m₁ (ρ₁ ++ ρ₂) i f
  ... | nothing , i' , f' = refl
  ... | just v₁ , i' , f'
      rewrite interp-shift-mon m₂ v (v₁ ∷ ρ₁) ρ₂ =
     refl

rco-correct : ∀ (e : Exp) (ρ : Env)
  → interp-mon (rco e) ρ ≡ interp e ρ
rco-correct (Num x) ρ = refl
rco-correct Read ρ = refl
rco-correct (Sub e₁ e₂) ρ 
  rewrite rco-correct e₁ ρ = extensionality2 Goal
  where
  Goal : (i : ℕ) (f : ℕ → ℤ) →
      ((interp e₁ ρ then
        (λ v₁ i f → (interp-mon (shift-mon (rco e₂) 0) (v₁ ∷ ρ) then
        (λ v₂ i₁ f₁ → just (v₁ Data.Integer.+ - v₂) , i₁ , f₁)) i f)) i f)
      ≡ ((interp e₁ ρ then
        (λ v₁ i f → (interp e₂ ρ then
        (λ v₂ i₁ f₁ → just (v₁ Data.Integer.+ - v₂) , i₁ , f₁)) i f)) i f)
  Goal i f
      with interp e₁ ρ i f
  ... | nothing , i' , f' = refl
  ... | just v₁ , i' , f'
      rewrite interp-shift-mon (rco e₂) v₁ [] ρ
      | rco-correct e₂ ρ = refl

rco-correct (Var i₁) ρ = refl
rco-correct (Let e₁ e₂) ρ
  rewrite rco-correct e₁ ρ = extensionality2 Goal
  where
  Goal : (i : ℕ) (f : ℕ → ℤ) →
      ((interp e₁ ρ then (λ v₁ → interp-mon (rco e₂) (v₁ ∷ ρ))) i f)
      ≡ ((interp e₁ ρ then (λ v₁ → interp e₂ (v₁ ∷ ρ))) i f)
  Goal i f
      with interp e₁ ρ i f
  ... | nothing , i1 , f1 = refl
  ... | just v₁ , i1 , f2
      rewrite rco-correct e₂ (v₁ ∷ ρ) = refl
