module LIfCorrect where

open import Agda.Builtin.Unit
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using ()
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; _≤ᵇ_; _∸_; _+_; s≤s; _⊔_)
open import Data.Nat.Properties
open import Data.Product
open import Data.Sum
open import Data.Integer using (ℤ; -_; _-_; 0ℤ)
open import Data.List
open import Data.List.Properties using (++-assoc; length-replicate; ++-identityʳ; length-++)
open import Data.Maybe
open import Relation.Binary.PropositionalEquality
   using (_≡_; refl; trans; sym; cong; cong-app)
open import Agda.Builtin.Bool
open import Relation.Nullary.Negation.Core using (¬_; contradiction)
open import Function.Base using (case_of_; case_returning_of_)

open import Reader
open import Utilities
open import LIf
open import LIfTypePres

--------------- Proof of correctness for RCO ------------------------

interp-shift-atm : ∀ (a : Atm) (v : Value) (ρ₁ ρ₂ : Env Value)
  → interp-atm (shift-atm a (length ρ₁)) (ρ₁ ++ v ∷ ρ₂) 
    ≡ interp-atm a (ρ₁ ++ ρ₂) 
interp-shift-atm (Num x) v ρ₁ ρ₂ = refl
interp-shift-atm (Bool x) v ρ₁ ρ₂ = refl
interp-shift-atm (Var x) v ρ₁ ρ₂ = nth-++-shift-var ρ₁ ρ₂ v x

interp-shift-mon : ∀ (m : Mon) (v : Value) (ρ₁ ρ₂ : Env Value)
  → interp-mon (shift-mon m (length ρ₁)) (ρ₁ ++ (v ∷ ρ₂))
    ≡ interp-mon m (ρ₁ ++ ρ₂)
interp-shift-mon (Atom a) v ρ₁ ρ₂ rewrite interp-shift-atm a v ρ₁ ρ₂ = refl
interp-shift-mon Read v ρ₁ ρ₂ = refl
interp-shift-mon (Uni op a) v ρ₁ ρ₂ 
    rewrite interp-shift-atm a v ρ₁ ρ₂
    = refl
interp-shift-mon (Bin op a₁ a₂) v ρ₁ ρ₂ 
    rewrite interp-shift-atm a₁ v ρ₁ ρ₂
    | interp-shift-atm a₂ v ρ₁ ρ₂
    = refl
interp-shift-mon (Let m₁ m₂) v ρ₁ ρ₂ 
  = extensionality Goal
  where
  Goal : (s : Inputs) →
    interp-mon (shift-mon (Let m₁ m₂) (length ρ₁)) (ρ₁ ++ (v ∷ ρ₂)) s
    ≡ interp-mon (Let m₁ m₂) (ρ₁ ++ ρ₂) s
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
  Goal : (s : Inputs) →
    interp-mon (shift-mon (If m₁ m₂ m₃) (length ρ₁)) (ρ₁ ++ (v ∷ ρ₂)) s
    ≡ interp-mon (If m₁ m₂ m₃) (ρ₁ ++ ρ₂) s
  Goal s
      rewrite interp-shift-mon m₁ v ρ₁ ρ₂
      with interp-mon m₁ (ρ₁ ++ ρ₂) s
  ... | nothing = refl
  ... | just (Int n₁ , s') = refl
  ... | just (Bool true , s')
      rewrite interp-shift-mon m₂ v ρ₁ ρ₂
      = refl
  ... | just (Bool false , s')
      rewrite interp-shift-mon m₃ v ρ₁ ρ₂
      = refl

rco-correct-exp : ∀ (e : Exp) (ρ : Env Value)
  → interp-mon (rco e) ρ ≡ interp-exp e ρ
rco-correct-exp (Num n) ρ = refl
rco-correct-exp (Bool b) ρ = refl
rco-correct-exp Read ρ = refl
rco-correct-exp (Uni op e) ρ = extensionality Goal
  where
  Goal : (s : Inputs) →
         interp-mon (rco (Uni op e)) ρ s ≡ interp-exp (Uni op e) ρ s
  Goal s
      rewrite rco-correct-exp e ρ
      with interp-exp e ρ s
  ... | nothing = refl
  ... | just (v₁ , s')
      = refl
rco-correct-exp (Bin op e₁ e₂) ρ = extensionality Goal
  where
  Goal : (s : Inputs) →
         interp-mon (rco (Bin op e₁ e₂)) ρ s ≡ interp-exp (Bin op e₁ e₂) ρ s
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
  Goal : (s : Inputs) →
         interp-mon (rco (Let e₁ e₂)) ρ s ≡ interp-exp (Let e₁ e₂) ρ s  
  Goal s
      rewrite rco-correct-exp e₁ ρ
      with interp-exp e₁ ρ s
  ... | nothing = refl
  ... | just (v₁ , s')
      rewrite rco-correct-exp e₂ (v₁ ∷ ρ)
      = refl
rco-correct-exp (If e₁ e₂ e₃) ρ = extensionality Goal
  where
  Goal : (s : Inputs) →
         interp-mon (rco (If e₁ e₂ e₃)) ρ s ≡ interp-exp (If e₁ e₂ e₃) ρ s  
  Goal s
      rewrite rco-correct-exp e₁ ρ
      with interp-exp e₁ ρ s
  ... | nothing = refl
  ... | just (Int n₁ , s') = refl
  ... | just (Bool true , s') rewrite rco-correct-exp e₂ ρ = refl
  ... | just (Bool false , s') rewrite rco-correct-exp e₃ ρ = refl

rco-correct : ∀ (e : Exp) (s : Inputs)
  → interp-LMonIf (rco e) s ≡ interp-LIf e s 
rco-correct e s rewrite rco-correct-exp e [] = refl

--------------- Proof of correctness for Lift Locals -------------------

interp-shifts-atm : ∀ (a : Atm) (ρ₁ ρ₂ ρ₃ : Env Value)
  → interp-atm (shifts-atm a  (length ρ₁) (length ρ₂)) (ρ₁ ++ ρ₂ ++ ρ₃)
  ≡ interp-atm a (ρ₁ ++ ρ₃)
interp-shifts-atm (Num x) ρ₁ ρ₂ ρ₃ = refl
interp-shifts-atm (Atm.Bool x) ρ₁ ρ₂ ρ₃ = refl
interp-shifts-atm (Var x) ρ₁ ρ₂ ρ₃ = nth-++-shifts-var ρ₁ ρ₂ ρ₃ x

interp-shifts-il1-exp : ∀ (e : IL1-Exp) (ρ₁ ρ₂ ρ₃ : Env Value)
  → interp-il1-exp (shifts-il1-exp e (length ρ₁) (length ρ₂)) (ρ₁ ++ ρ₂ ++ ρ₃)
  ≡ interp-il1-exp e (ρ₁ ++ ρ₃)
interp-shifts-il1-exp (Atom a) ρ₁ ρ₂ ρ₃
    rewrite interp-shifts-atm a ρ₁ ρ₂ ρ₃ = refl
interp-shifts-il1-exp Read ρ₁ ρ₂ ρ₃ = refl
interp-shifts-il1-exp (Uni op a) ρ₁ ρ₂ ρ₃
    rewrite interp-shifts-atm a ρ₁ ρ₂ ρ₃
    = refl
interp-shifts-il1-exp (Bin op a₁ a₂) ρ₁ ρ₂ ρ₃
    rewrite interp-shifts-atm a₁ ρ₁ ρ₂ ρ₃
    | interp-shifts-atm a₂ ρ₁ ρ₂ ρ₃
    = refl
interp-shifts-il1-exp (Assign x e₁ e₂) ρ₁ ρ₂ ρ₃ = extensionality Goal
    where
    Goal : (s : Inputs) →
             interp-il1-exp (shifts-il1-exp (Assign x e₁ e₂) (length ρ₁) (length ρ₂)) (ρ₁ ++ ρ₂ ++ ρ₃) s
           ≡ interp-il1-exp (Assign x e₁ e₂) (ρ₁ ++ ρ₃) s
    Goal s
        rewrite nth-++-shifts-var ρ₁ ρ₂ ρ₃ x
        | interp-shifts-il1-exp e₁ ρ₁ ρ₂ ρ₃
        with interp-il1-exp e₁ (ρ₁ ++ ρ₃) s
    ... | nothing = refl
    ... | just (v₁ , s₁)
        with length ρ₁ ≤ᵇ x in lt
    ... | true
        with m≤n⇒-+ (length ρ₁) x (≤ᵇ⇒≤ (length ρ₁) x (eq-true-top lt))
    ... | i , refl
        rewrite update-++-+ ρ₁ ρ₃ i v₁
        | sym (+-assoc (length ρ₂) (length ρ₁) i)
        | +-comm (length ρ₂) (length ρ₁)
        | (+-assoc (length ρ₁) (length ρ₂) i)
        | update-++-+ ρ₁ (ρ₂ ++ ρ₃) (length ρ₂ + i) v₁
        | update-++-+ ρ₂ ρ₃ i v₁
        | interp-shifts-il1-exp e₂ ρ₁ ρ₂ (update ρ₃ i v₁)
        = refl
    Goal s | just (v₁ , s₁) | false
        rewrite update-++-< ρ₁ ρ₃ x v₁ (≰⇒> λ x₁ → (eq-false-not-top lt) (≤⇒≤ᵇ x₁))
        | update-++-< ρ₁ (ρ₂ ++ ρ₃) x v₁ (≰⇒> λ x₁ → (eq-false-not-top lt) (≤⇒≤ᵇ x₁))
        with interp-shifts-il1-exp e₂ (update ρ₁ x v₁) ρ₂ ρ₃
    ... | IH2
        rewrite update-length ρ₁ x v₁
        | IH2
        = refl
    
interp-shifts-il1-exp (If e₁ e₂ e₃) ρ₁ ρ₂ ρ₃ = extensionality Goal
    where
    Goal : (s : Inputs) →
             interp-il1-exp (shifts-il1-exp (If e₁ e₂ e₃) (length ρ₁) (length ρ₂)) (ρ₁ ++ ρ₂ ++ ρ₃) s
           ≡ interp-il1-exp (If e₁ e₂ e₃) (ρ₁ ++ ρ₃) s
    Goal s
        rewrite interp-shifts-il1-exp e₁ ρ₁ ρ₂ ρ₃
        with interp-il1-exp e₁ (ρ₁ ++ ρ₃) s
    ... | nothing = refl
    ... | just (Int n , s₁) = refl
    ... | just (Bool true , s₁)
        rewrite interp-shifts-il1-exp e₂ ρ₁ ρ₂ ρ₃
        = refl
    ... | just (Bool false , s₁)
        rewrite interp-shifts-il1-exp e₃ ρ₁ ρ₂ ρ₃
        = refl
        
suc-i-j : ∀ (i j : ℕ)
    → suc (i + j) ≡ j + 1 + i
suc-i-j i j
  rewrite +-comm i j | +-comm j 1 = refl

-- ρ₁ is for the bound variables in m, which become free and are initialized to 0
-- ρ₂ is for the free variables in m
lift-mon-correct-aux : ∀ (m : Mon) (ρ₁ ρ₂ : Env Value)
  → proj₁ (lift-locals-mon m) ≡ length ρ₁
  → interp-mon m ρ₂ ≡ interp-il1-exp (proj₂ (lift-locals-mon m)) (ρ₁ ++ ρ₂) 
lift-mon-correct-aux (Atom a) [] ρ₂ prem = refl
lift-mon-correct-aux Read ρ₁ ρ₂ prem = refl
lift-mon-correct-aux (Uni op a) [] ρ₂ prem = refl
lift-mon-correct-aux (Bin op a₁ a₂) [] ρ₂ prem = refl
lift-mon-correct-aux (Let m₁ m₂) ρ₁ ρ₂ prem = extensionality Goal
    where
    Goal : (s : Inputs)
      → interp-mon (Let m₁ m₂) ρ₂ s
      ≡ interp-il1-exp (proj₂ (lift-locals-mon (Let m₁ m₂))) (ρ₁ ++ ρ₂) s
    Goal s
        with lift-locals-mon m₁ in l1
    ... | i , e₁
        with lift-locals-mon m₂ in l2
    ... | j , e₂
        with ++-length ρ₁ (j + 1) i (trans (sym prem) (suc-i-j i j))
    ... | ρ′₁ , ρ₁₂ , refl , ρ′₁j1 , refl
        with ++-length ρ′₁ j 1 ρ′₁j1
    ... | ρ₁₁ , v′ ∷ [] , refl , refl , refl
        with interp-shifts-il1-exp e₁ [] (ρ₁₁ ++ [ v′ ]) (ρ₁₂ ++ ρ₂)
    ... | is1
        rewrite length-++ ρ₁₁ {v′ ∷ []} | +-comm (length ρ₁₁) 1
        | ++-assoc (ρ₁₁ ++ v′ ∷ []) ρ₁₂ ρ₂
        | is1
        with lift-mon-correct-aux m₁ ρ₁₂ ρ₂
    ... | IH1
        rewrite l1 | sym (IH1 refl)
        | ++-assoc ρ₁₁ (v′ ∷ []) (ρ₁₂ ++ ρ₂)
        with ++-length (v′ ∷ ρ₁₂) (length ρ₁₂) 1
    ... | len12
        rewrite +-comm (length ρ₁₂) 1
        with len12 refl
    ... | ρ′₁₂ , (v′₁ ∷ []) , r12-eq , len-r12 , refl
        with interp-mon m₁ ρ₂ s in im1
    ... | nothing = refl
    ... | just (v₁ , s1)
        rewrite cons-++ v′ ρ₁₂ ρ₂ (ρ′₁₂ ++ v′₁ ∷ []) r12-eq
        | ++-assoc ρ′₁₂ (v′₁ ∷ []) ρ₂
        | +-comm (length ρ₁₂) (length ρ₁₁)
        | update-++-+ ρ₁₁ (ρ′₁₂ ++ v′₁ ∷ ρ₂) (length ρ₁₂) v₁
        | sym len-r12
        | sym (+-identityʳ (length ρ′₁₂))
        | update-++-+ ρ′₁₂ (v′₁ ∷ ρ₂) 0 v₁
        | +-identityʳ (length ρ′₁₂)
        | interp-shifts-il1-exp e₂ ρ₁₁ ρ′₁₂ (v₁ ∷ ρ₂)
        with lift-mon-correct-aux m₂ ρ₁₁ (v₁ ∷ ρ₂)
    ... | IH2
        rewrite l2 | sym (IH2 refl)
        with interp-mon m₂ (v₁ ∷ ρ₂) s1 in im2
    ... | nothing = refl
    ... | just (v₂ , s2)
        = refl

lift-mon-correct-aux (If m₁ m₂ m₃) ρ₁ ρ₂ prem = extensionality Goal
    where
    Goal : (s : Inputs)
      → interp-mon (If m₁ m₂ m₃) ρ₂ s
      ≡ interp-il1-exp (proj₂ (lift-locals-mon (If m₁ m₂ m₃))) (ρ₁ ++ ρ₂) s
    Goal s
        with lift-locals-mon m₁ in l1
    ... | i , e₁
        with lift-locals-mon m₂ in l2
    ... | j , e₂
        with lift-locals-mon m₃ in l3
    ... | k , e₃
        rewrite (+-assoc i j k) | +-comm i (j + k)
        with ++-length ρ₁ (j + k) i (sym prem)
    ... | ρ₁₁ , ρ₁₂ , refl , ρ₁₁≡j+k , refl
        rewrite ++-assoc ρ₁₁ ρ₁₂ ρ₂ | sym ρ₁₁≡j+k
        | interp-shifts-il1-exp e₁ [] ρ₁₁ (ρ₁₂ ++ ρ₂)
        with lift-mon-correct-aux m₁ ρ₁₂ ρ₂
    ... | IH1
        rewrite l1 | sym (IH1 refl)
        with interp-mon m₁ ρ₂ s
    ... | nothing = refl
    ... | just (Int n , s1) = refl
    ... | just (Bool true , s1)
        rewrite +-comm k j | sym ρ₁₁≡j+k
        | interp-shifts-il1-exp (shifts-il1-exp e₂ 0 k) ρ₁₁ ρ₁₂ ρ₂
        with ++-length ρ₁₁ k j
    ... | split2
        rewrite +-comm k j
        with split2 ρ₁₁≡j+k
    ... | ρ′₁₁ , ρ″₁₁ , eq11 , ρ′₁₁≡k , ρ″₁₁≡j
        rewrite eq11 | ++-assoc ρ′₁₁ ρ″₁₁ ρ₂ | sym ρ′₁₁≡k
        | interp-shifts-il1-exp e₂ [] ρ′₁₁ (ρ″₁₁ ++ ρ₂)
        with lift-mon-correct-aux m₂ ρ″₁₁ ρ₂
    ... | IH2
        rewrite l2 | sym ρ″₁₁≡j | sym (IH2 refl)
        = refl
    Goal s | i , e₁ | j , e₂ | k , e₃ | ρ₁₁ , ρ₁₂ , refl , ρ₁₁≡j+k , refl | IH1
        | just (Bool false , s1)
        with ++-length ρ₁₁ k j
    ... | split2
        rewrite +-comm k j
        with split2 ρ₁₁≡j+k
    ... | ρ′₁₁ , ρ″₁₁ , eq11 , ρ′₁₁≡k , ρ″₁₁≡j
        rewrite eq11 | ++-assoc ρ′₁₁ ρ″₁₁ (ρ₁₂ ++ ρ₂) | sym ρ″₁₁≡j | sym ρ′₁₁≡k
        with interp-shifts-il1-exp e₃ ρ′₁₁ (ρ″₁₁ ++ ρ₁₂) ρ₂
    ... | is3
        rewrite ++-assoc ρ″₁₁ ρ₁₂ ρ₂ | length-++ ρ″₁₁ {ρ₁₂} | +-comm (length ρ₁₂) (length ρ″₁₁)
        | is3
        with lift-mon-correct-aux m₃ ρ′₁₁ ρ₂
    ... | IH3
        rewrite l3 | sym (IH3 refl)
        = refl

lift-mon-correct : ∀ (m : Mon) (ρ : Env Value)
  → proj₁ (lift-locals-mon m) ≡ length ρ
  → interp-mon m [] ≡ interp-il1-exp (proj₂ (lift-locals-mon m)) ρ
lift-mon-correct m ρ prem
  rewrite lift-mon-correct-aux m ρ [] prem
  | ++-identityʳ ρ = refl

lift-locals-correct : ∀ (m : Mon) (s : Inputs)
  → interp-IL1 (lift-locals m) s ≡ interp-LMonIf m s
lift-locals-correct m s
  rewrite lift-mon-correct m (replicate (lift-locals-mon m .proj₁) (Int 0ℤ))
              (sym (length-replicate (proj₁ (lift-locals-mon m))))
  = refl
