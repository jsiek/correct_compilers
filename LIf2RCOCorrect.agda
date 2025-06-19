module LIf2RCOCorrect where

open import Agda.Builtin.Bool
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; _≤ᵇ_; _∸_; _+_; s≤s)
open import Data.Product
open import Data.Integer using (ℤ; _-_; 0ℤ)
open import Data.List
open import Data.Maybe
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Relation.Nullary using (Dec; yes; no)
open import Utilities
open import LIf2

--------------- Proof of correctness for RCO ------------------------

interp-shift-atm : ∀ (a : Atm) (v : Value) (ρ₁ ρ₂ : Env Value)
  → interp-atm (shift-atm a (length ρ₁)) (ρ₁ ++ v ∷ ρ₂) 
    ≡ interp-atm a (ρ₁ ++ ρ₂) 
interp-shift-atm (Num n) v ρ₁ ρ₂ = refl
interp-shift-atm (Bool b) v ρ₁ ρ₂ = refl
interp-shift-atm (Var x) v ρ₁ ρ₂ = nth-++-shift-var ρ₁ ρ₂ v x

interp-shift-mon : ∀ (m : Mon) (v : Value) (ρ₁ ρ₂ : Env Value)
  → interp-mon (shift-mon m (length ρ₁)) (ρ₁ ++ (v ∷ ρ₂))
    ≡ interp-mon m (ρ₁ ++ ρ₂)
interp-shift-mon (Atom a) v ρ₁ ρ₂ rewrite interp-shift-atm a v ρ₁ ρ₂ = refl
interp-shift-mon Read v ρ₁ ρ₂ = refl
interp-shift-mon (Sub a₁ a₂) v ρ₁ ρ₂ 
    rewrite interp-shift-atm a₁ v ρ₁ ρ₂
    | interp-shift-atm a₂ v ρ₁ ρ₂
    = refl
interp-shift-mon (Eq a₁ a₂) v ρ₁ ρ₂ 
    rewrite interp-shift-atm a₁ v ρ₁ ρ₂
    | interp-shift-atm a₂ v ρ₁ ρ₂
    = refl
interp-shift-mon (Let m₁ m₂) v ρ₁ ρ₂ 
  = extensionality Goal
  where
  e = (Let m₁ m₂)
  Goal : (s : Inputs) →
     interp-mon (shift-mon e (length ρ₁)) (ρ₁ ++ (v ∷ ρ₂)) s
     ≡ interp-mon e (ρ₁ ++ ρ₂) s
  Goal s
      rewrite interp-shift-mon m₁ v ρ₁ ρ₂
      with interp-mon m₁ (ρ₁ ++ ρ₂) s
  ... | nothing = refl
  ... | just (v₁ , s')
      rewrite interp-shift-mon m₂ v (v₁ ∷ ρ₁) ρ₂
      = refl
interp-shift-mon (If m₁ m₂ m₃) v ρ₁ ρ₂
  = extensionality Goal
  where
  e =  (If m₁ m₂ m₃)
  Goal : (s : Inputs) →
     interp-mon (shift-mon e (length ρ₁)) (ρ₁ ++ (v ∷ ρ₂)) s
     ≡ interp-mon e (ρ₁ ++ ρ₂) s
  Goal s
      rewrite interp-shift-mon m₁ v ρ₁ ρ₂
      with interp-mon m₁ (ρ₁ ++ ρ₂) s
  ... | nothing = refl
  ... | just (Int n , s') = refl
  ... | just (Bool true , s')
      rewrite interp-shift-mon m₂ v ρ₁ ρ₂
      = refl
  ... | just (Bool false , s')
      rewrite interp-shift-mon m₃ v ρ₁ ρ₂
      = refl

rco-correct-exp : ∀ (e : Exp) (ρ : Env Value)
  → interp-mon (rco e) ρ ≡ interp-exp e ρ
rco-correct-exp (Num x) ρ = refl
rco-correct-exp (Bool b) ρ = refl
rco-correct-exp Read ρ = refl
rco-correct-exp (Sub e₁ e₂) ρ = extensionality Goal
  where
  Goal : (s : Inputs) →
         interp-mon (rco (Sub e₁ e₂)) ρ s ≡ interp-exp (Sub e₁ e₂) ρ s
  Goal s
  -- Complex version
      with rco e₁ in m1 | rco e₂ in m2
  ... | m₁ | m₂
      with atomic? m₁ | atomic? m₂
  ... | yes (atomic a₁) | yes (atomic a₂)
      rewrite sym (rco-correct-exp e₁ ρ) | sym (rco-correct-exp e₂ ρ)
      | m1 | m2
      = refl
  Goal s | m₁ | m₂
      | no cmplx₁ | yes (atomic a₂)
      rewrite sym m1 | rco-correct-exp e₁ ρ
      with interp-exp e₁ ρ s
  ... | nothing = refl
  ... | just (v₁ , s')
      rewrite sym (rco-correct-exp e₂ ρ) | m2
      rewrite interp-shift-atm a₂ v₁ [] ρ
      = refl
  Goal s | m₁ | m₂
      | yes (atomic a₁) | no cmplx₂
      rewrite sym (rco-correct-exp e₁ ρ) | m1
      rewrite sym m2 | rco-correct-exp e₂ ρ
      with interp-atm a₁ ρ in ia1
  ... | nothing
      with interp-exp e₂ ρ s
  ... | nothing = refl
  ... | just (v₂ , s')
      rewrite interp-shift-atm a₁ v₂ [] ρ | ia1
      = refl
  Goal s | m₁ | m₂
      | yes (atomic a₁) | no cmplx₂
      | just v₁
      with interp-exp e₂ ρ s
  ... | nothing = refl
  ... | just (v₂ , s')
      rewrite interp-shift-atm a₁ v₂ [] ρ | ia1
      = refl
  Goal s | m₁ | m₂
      | no cmplx₁ | no cmplx₂
      rewrite sym m1 | sym m2 | rco-correct-exp e₁ ρ
      with interp-exp e₁ ρ s
  ... | nothing = refl
  ... | just (v₁ , s')
      rewrite interp-shift-mon (rco e₂) v₁ [] ρ
      | rco-correct-exp e₂ ρ
      = refl

  -- Simple version
  --     rewrite rco-correct-exp e₁ ρ
  --     with interp-exp e₁ ρ s
  -- ... | nothing = refl
  -- ... | just (v₁ , s')
  --     rewrite interp-shift-mon (rco e₂) v₁ [] ρ
  --     | rco-correct-exp e₂ ρ
  --     = refl
rco-correct-exp (Eq e₁ e₂) ρ = extensionality Goal
  where
  Goal : (s : Inputs) →
         interp-mon (rco (Eq e₁ e₂)) ρ s ≡ interp-exp (Eq e₁ e₂) ρ s
  Goal s
      rewrite rco-correct-exp e₁ ρ
      with interp-exp e₁ ρ s
  ... | nothing = refl
  ... | just (v₁ , s')
      rewrite interp-shift-mon (rco e₂) v₁ [] ρ
      | rco-correct-exp e₂ ρ
      = refl
rco-correct-exp (Var i₁) ρ = refl
rco-correct-exp (Let e₁ e₂) ρ = extensionality Goal
  where
  e = (Let e₁ e₂)
  Goal : (s : Inputs) →
         interp-mon (rco e) ρ s ≡ interp-exp e ρ s  
  Goal s
      rewrite rco-correct-exp e₁ ρ
      with interp-exp e₁ ρ s
  ... | nothing = refl
  ... | just (v₁ , s')
      rewrite rco-correct-exp e₂ (v₁ ∷ ρ)
      = refl
rco-correct-exp (If e₁ e₂ e₃) ρ = extensionality Goal
  where
  e = (If e₁ e₂ e₃)
  Goal : (s : Inputs) →
         interp-mon (rco e) ρ s ≡ interp-exp e ρ s  
  Goal s
      rewrite rco-correct-exp e₁ ρ
      with interp-exp e₁ ρ s
  ... | nothing = refl
  ... | just (Int n , s') = refl
  ... | just (Bool true , s')
      rewrite rco-correct-exp e₂ ρ
      = refl
  ... | just (Bool false , s')
      rewrite rco-correct-exp e₃ ρ
      = refl

rco-correct : ∀ (e : Exp) (s : Inputs)
  → interp-LMonIf (rco e) s ≡ interp-LIf e s 
rco-correct e s rewrite rco-correct-exp e [] = refl
