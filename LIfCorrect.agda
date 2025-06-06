module LIfCorrect where

open import Agda.Builtin.Unit
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (if_then_else_)
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
open import Agda.Builtin.Bool renaming (Bool to 𝔹)
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

--------------- Proof of correctness for Explicate Control -------------------

_↝_ : Blocks → Blocks → Set
B₁ ↝ B₂ = Σ[ B ∈ Blocks ] B₁ ++ B ≡ B₂

↝-trans : ∀ {B₁ B₂ B₃ : Blocks}
  → B₁ ↝ B₂  → B₂ ↝ B₃
  → B₁ ↝ B₃
↝-trans {B₁}{B₂}{B₃} (B , eq12) (B' , eq23)
  rewrite sym eq12 | sym eq23  | ++-assoc B₁ B B'
  = B ++ B' , refl

↝-create-block : (t : CTail) (B B' : Blocks) (lbl : ℕ)
  → create-block t B ≡ (lbl , B')
  → B ↝ B'
↝-create-block (Return x) B B' lbl refl = [ Return x ] , refl
↝-create-block (Assign x e t) B B' lbl refl = [ Assign x e t ] , refl
↝-create-block (If x x₁ x₂ x₃ x₄) B B' lbl refl = [ If x x₁ x₂ x₃ x₄ ] , refl
↝-create-block (Goto lbl) B B lbl refl = [] , (++-identityʳ B)

explicate-tail-blocks : ∀ (m : IL1-Exp) (B₁ B₂ : Blocks) (t : CTail)
  → explicate-tail m B₁ ≡ (t , B₂)
  → B₁ ↝ B₂
explicate-assign-blocks : ∀ (x : Id) (m : IL1-Exp) (t t' : CTail) (B₁ B₂ : Blocks)
  → explicate-assign x m t B₁ ≡ (t' , B₂)
  → B₁ ↝ B₂
explicate-pred-blocks : ∀ (m : IL1-Exp) (t₁ t₂ t : CTail) (B₁ B₂ : Blocks)
  → explicate-pred m t₁ t₂ B₁ ≡ (t , B₂)
  → B₁ ↝ B₂

explicate-tail-blocks (Atom a) B₁ B₂ t refl = [] , (++-identityʳ B₁)
explicate-tail-blocks Read B₁ B₂ t refl = [] , (++-identityʳ B₁)
explicate-tail-blocks (Uni op a) B₁ B₂ t refl = [] , ++-identityʳ B₁
explicate-tail-blocks (Bin op a₁ a₂) B₁ B₂ t refl = [] , ++-identityʳ B₁
explicate-tail-blocks (Assign x m₁ m₂) B₁ B₂ t refl
    with explicate-tail m₂ B₁ in et
... | (t₂ , B)
    with explicate-assign x m₁ t₂ B in el
... | (t₁ , B') =
  let B₁↝B = explicate-tail-blocks m₂ B₁ B t₂ et in
  let B↝B' = explicate-assign-blocks x m₁ t₂ t₁ B B' el in
  ↝-trans B₁↝B B↝B'
explicate-tail-blocks (If m₁ m₂ m₃) B₁ B₂ t et
    with explicate-tail m₂ B₁ in et2
... | (t₂ , B)
    with explicate-tail m₃ B in et3
... | (t₃ , B') =
    let B₁↝B = explicate-tail-blocks m₂ B₁ B t₂ et2 in
    let B↝B' = explicate-tail-blocks m₃ B B' t₃ et3 in
    let B'↝B₂ = explicate-pred-blocks m₁ t₂ t₃ t B' B₂ et in
    ↝-trans B₁↝B (↝-trans B↝B' B'↝B₂)

explicate-assign-blocks y (Atom a) t t' B₁ B₂ refl = [] , ++-identityʳ B₁
explicate-assign-blocks y Read t t' B₁ B₂ refl = [] , (++-identityʳ B₁)
explicate-assign-blocks y (Uni op a) t t' B₁ B₂ refl = [] , ++-identityʳ B₁
explicate-assign-blocks y (Bin op a₁ a₂) t t' B₁ B₂ refl = [] , ++-identityʳ B₁
explicate-assign-blocks y (Assign x m₁ m₂) t t' B₁ B₂ el1
    with explicate-assign y m₂ t B₁ in el2
... | (t₂ , B) =
  let B₁↝B = explicate-assign-blocks y m₂ t t₂ B₁ B el2 in
  let B↝B₂ = explicate-assign-blocks x m₁ t₂ t' B B₂ el1 in
  ↝-trans B₁↝B B↝B₂ 
explicate-assign-blocks y (If m₁ m₂ m₃) t t' B₁ B₂ el
    with create-block t B₁ in cb1
... | cont , B
    with explicate-assign y m₂ (Goto cont) B in el2
... | t₂ , B'
    with explicate-assign y m₃ (Goto cont) B' in el3
... | t₃ , B'' =
    let B₁↝B = ↝-create-block t B₁ B cont cb1 in
    let B↝B' = explicate-assign-blocks y m₂ (Goto cont) t₂ B B' el2 in
    let B'↝B'' = explicate-assign-blocks y m₃ (Goto cont) t₃ B' B'' el3 in
    let B''↝B₂ = explicate-pred-blocks m₁ t₂ t₃ t' B'' B₂ el in
    ↝-trans B₁↝B (↝-trans B↝B' (↝-trans B'↝B'' B''↝B₂))

explicate-pred-blocks (Atom a) t₁ t₂ t B₁ B₂ ep
    with create-block t₁ B₁ in cb1
... | l1 , B
    with create-block t₂ B in cb2
... | l2 , B'
    with ep
... | refl =
    let B₁↝B = ↝-create-block t₁ B₁ B l1 cb1 in
    let B↝B' = ↝-create-block t₂ B B' l2 cb2 in
    ↝-trans B₁↝B B↝B'
explicate-pred-blocks Read t₁ t₂ t B₁ B₂ refl = [] , ++-identityʳ B₁ 
explicate-pred-blocks (Uni Neg a) t₁ t₂ t B₁ B₂ refl = [] , (++-identityʳ B₁)
explicate-pred-blocks (Uni Not a) t₁ t₂ t B₁ B₂ ep
    with create-block t₂ B₁ in cb2
... | l2 , B
    with create-block t₁ B in cb1
... | l1 , B'
    with ep
... | refl =
    let B₁↝B = ↝-create-block t₂ B₁ B l2 cb2 in
    let B↝B' = ↝-create-block t₁ B B' l1 cb1 in
    ↝-trans B₁↝B B↝B'
explicate-pred-blocks (Bin op a₁ a₂) t₁ t₂ t B₁ B₂ ep
    with create-block t₁ B₁ in cb1
... | l1 , B
    with create-block t₂ B in cb2
... | l2 , B'
    with ep
... | refl =
    let B₁↝B = ↝-create-block t₁ B₁ B l1 cb1 in
    let B↝B' = ↝-create-block t₂ B B' l2 cb2 in
    ↝-trans B₁↝B B↝B'
explicate-pred-blocks (Assign x m₁ m₂) thn els t B₁ B₂ ep
    with explicate-pred m₂ thn els B₁ in el2
... | (t₂ , B)
    =
    let B₁↝B = explicate-pred-blocks m₂ thn els t₂ B₁ B el2 in
    let B↝B₂ = explicate-assign-blocks x m₁ t₂ t B B₂ ep in
    ↝-trans B₁↝B B↝B₂ 
explicate-pred-blocks (If m₁ m₂ m₃) thn els t B₁ B₂ ep
    with create-block thn B₁ in cb1
... | lbl-thn , B
    with create-block els B in cb2
... | lbl-els , B'
    with explicate-pred m₂ (Goto lbl-thn) (Goto lbl-els) B' in ep2
... | t₂ , B''
    with explicate-pred m₃ (Goto lbl-thn) (Goto lbl-els) B'' in ep3
... | t₃ , B'''
    =
    let B₁↝B = ↝-create-block thn B₁ B lbl-thn cb1 in
    let B↝B' = ↝-create-block els B B' lbl-els cb2 in
    let B'↝B'' = explicate-pred-blocks m₂ (Goto lbl-thn) (Goto lbl-els) t₂ B' B'' ep2 in
    let B''↝B''' = explicate-pred-blocks m₃ (Goto lbl-thn) (Goto lbl-els) t₃ B'' B''' ep3 in
    let B'''↝B₂ = explicate-pred-blocks m₁ t₂ t₃ t B''' B₂ ep in
    ↝-trans B₁↝B (↝-trans B↝B' (↝-trans B'↝B'' (↝-trans B''↝B''' B'''↝B₂)))

nth-blocks : ∀ {B₁ B₂ : Blocks} {l : ℕ} {t : CTail}
  → B₁ ↝ B₂
  → nth B₁ l ≡ just t
  → nth B₂ l ≡ just t
nth-blocks {B₁}{l = l}{t} (B , refl) n1 = nth-++-just B₁ B l t n1

eval-tail-blocks : ∀ (t : CTail) (ρ : Env Value) (B₁ B₂ : Blocks) (s s' : Inputs) (v : Value)
  → B₁ ↝ B₂
  → ρ , s , B₁ ⊢ t ⇓ (v , s')
  → ρ , s , B₂ ⊢ t ⇓ (v , s')
eval-tail-blocks (Return e) ρ B₁ B₂ s s' v B12 (return-⇓ eq) =
  return-⇓ eq
eval-tail-blocks (Assign x e t) ρ B₁ B₂ s s' v B12 (assign-⇓ ie t⇓) =
  assign-⇓ ie (eval-tail-blocks t _ B₁ B₂ _ s' v B12 t⇓)
eval-tail-blocks (If op a₁ a₂ thn els) ρ B₁ B₂ s s' v B12 (if-⇓-true iop nth t⇓) =
  if-⇓-true iop (nth-blocks B12 nth) (eval-tail-blocks _ ρ B₁ B₂ _ s' v B12 t⇓)
eval-tail-blocks (If op a₁ a₂ thn els) ρ B₁ B₂ s s' v B12 (if-⇓-false iop nth t⇓) =
  if-⇓-false iop (nth-blocks B12 nth) (eval-tail-blocks _ ρ B₁ B₂ _ s' v B12 t⇓)
eval-tail-blocks (Goto l) ρ B₁ B₂ s s' v B12 (goto-⇓ nth t⇓) =
  goto-⇓ (nth-blocks B12 nth) (eval-tail-blocks _ ρ B₁ B₂ s s' v B12 t⇓)

explicate-assign-correct : ∀(y : Id)(e : IL1-Exp) (t t' : CTail) (ρ : Env Value)
   (B₂ B₃ : Blocks) (s s1 : Inputs) (v : Value) (r : Value × Inputs)
  → explicate-assign y e t B₂ ≡ (t' , B₃)
  → interp-il1-exp e ρ s ≡ just (v , s1)
  → (update ρ y v) , s1 , B₃ ⊢ t ⇓ r
  → ρ , s , B₃ ⊢ t' ⇓ r
explicate-assign-correct y e t t' ρ B₂ B₃ s ea ie t⇓ = {!!}

explicate-tail-correct : ∀ (e : IL1-Exp) (ρ : Env Value) (B B' : Blocks) (t : CTail) (s : Inputs) (r : Value × Inputs)
  → explicate-tail e B ≡ (t , B')
  → interp-il1-exp e ρ s ≡ just r
  →  ρ , s , B' ⊢ t ⇓ r
explicate-tail-correct e ρ B B' t s et ie = {!!}

explicate-pred-correct : ∀ (e₁ : IL1-Exp) (t₁ t₂ t₃ : CTail) (ρ : Env Value) (B₄ B₅ : Blocks) (s s1 : Inputs) (r : Value × Inputs) (b : 𝔹)
  → explicate-pred e₁ t₂ t₃ B₄ ≡ (t₁ , B₅)
  → interp-il1-exp e₁ ρ s ≡ just (Value.Bool b , s1)
  → ρ , s1 , B₅ ⊢ (if b then t₂ else t₃) ⇓ r
  → ρ , s , B₅ ⊢ t₁ ⇓ r
explicate-pred-correct e₁ t₂ t₃ ρ B₄ B₅ s ep = {!!}

create-block-correct : ∀ (t : CTail) (B B' : Blocks) (lbl : Id)
    (ρ : Env Value) (s : Inputs) (r : Value × Inputs)
  → create-block t B ≡ (lbl , B')
  → ρ , s , B ⊢ t ⇓ r
  → ρ , s , B' ⊢ Goto lbl ⇓ r
create-block-correct (Return e) B B' lbl ρ s r refl t⇓ =
  goto-⇓ (nth-++-1 B t) (eval-tail-blocks t ρ B (B ++ [ t ]) s (r .proj₂) (r .proj₁)
           ([ t ] , refl) t⇓)
  where
  t = Return e
create-block-correct (Assign x e t′) B B' lbl ρ s r refl t⇓ =
  goto-⇓ (nth-++-1 B t) (eval-tail-blocks t ρ B (B ++ [ t ]) s (r .proj₂) (r .proj₁)
           ([ t ] , refl) t⇓)
  where
  t = Assign x e t′
create-block-correct (If op a₁ a₂ e₁ e₂) B B' lbl ρ s r refl t⇓ =
  goto-⇓ (nth-++-1 B t) (eval-tail-blocks t ρ B (B ++ [ t ]) s (r .proj₂) (r .proj₁)
           ([ t ] , refl) t⇓)
  where
  t = If op a₁ a₂ e₁ e₂
create-block-correct (Goto lbl) B B lbl ρ s r refl t⇓ = t⇓

explicate-correct : ∀ (p : IL1-Prog) (s : Inputs) (v : Value)
  → interp-IL1 p s ≡ just v
  → eval-CIf (explicate p) s  v
explicate-correct (Program n e) s v ip
    with explicate-tail e [] in ete
... | t , B
    with create-block t B in cb
... | lbl , B'    
    with interp-il1-exp e (replicate n (Int (ℤ.pos 0))) s in ie | ip
... | nothing | ()
... | just (v , s1) | refl
    =
    let ρ₀ = replicate n (Int (ℤ.pos 0)) in
    let t⇓ = explicate-tail-correct e ρ₀ [] B t s (v , s1) ete ie in
    let goto⇓ = create-block-correct t B B' lbl ρ₀ s (v , s1) cb t⇓ in
    s1 , goto⇓

