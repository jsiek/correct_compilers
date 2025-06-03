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
open import Data.List.Properties using (++-assoc; length-replicate; ++-identityʳ)
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
↝-create-block (Let x t) B B' lbl refl = [ Let x t ] , refl
↝-create-block (If x x₁ x₂ x₃ x₄) B B' lbl refl = [ If x x₁ x₂ x₃ x₄ ] , refl
↝-create-block (Goto lbl) B B lbl refl = [] , (++-identityʳ B)


explicate-tail-blocks : ∀ (m : Mon) (B₁ B₂ : Blocks) (t : CTail)
  → explicate-tail m B₁ ≡ (t , B₂)
  → B₁ ↝ B₂

explicate-let-blocks : ∀ (m : Mon) (t t' : CTail) (B₁ B₂ : Blocks)
  → explicate-let m t B₁ ≡ (t' , B₂)
  → B₁ ↝ B₂

explicate-pred-blocks : ∀ (m : Mon) (t₁ t₂ t : CTail) (B₁ B₂ : Blocks)
  → explicate-pred m t₁ t₂ B₁ ≡ (t , B₂)
  → B₁ ↝ B₂

explicate-tail-blocks (Atom a) B₁ B₂ t refl = [] , (++-identityʳ B₁)
explicate-tail-blocks Read B₁ B₂ t refl = [] , (++-identityʳ B₁)
explicate-tail-blocks (Uni op a) B₁ B₂ t refl = [] , ++-identityʳ B₁
explicate-tail-blocks (Bin op a₁ a₂) B₁ B₂ t refl = [] , ++-identityʳ B₁
explicate-tail-blocks (Let m₁ m₂) B₁ B₂ t refl
    with explicate-tail m₂ B₁ in et
... | (t₂ , B)
    with explicate-let m₁ t₂ B in el
... | (t₁ , B') =
  let B₁↝B = explicate-tail-blocks m₂ B₁ B t₂ et in
  let B↝B' = explicate-let-blocks m₁ t₂ t₁ B B' el in
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

explicate-let-blocks (Atom a) t t' B₁ B₂ refl = [] , ++-identityʳ B₁
explicate-let-blocks Read t t' B₁ B₂ refl = [] , (++-identityʳ B₁)
explicate-let-blocks (Uni op a) t t' B₁ B₂ refl = [] , ++-identityʳ B₁
explicate-let-blocks (Bin op a₁ a₂) t t' B₁ B₂ refl = [] , ++-identityʳ B₁
explicate-let-blocks (Let m₁ m₂) t t' B₁ B₂ el1
    with explicate-let m₂ (shift-tail t 1) B₁ in el2
... | (t₂ , B) =
  let B₁↝B = explicate-let-blocks m₂ (shift-tail t 1) t₂ B₁ B el2 in
  let B↝B₂ = explicate-let-blocks m₁ t₂ t' B B₂ el1 in
  ↝-trans B₁↝B B↝B₂ 
explicate-let-blocks (If m₁ m₂ m₃) t t' B₁ B₂ el
    with create-block t B₁ in cb1
... | cont , B
    with explicate-let m₂ (Goto cont) B in el2
... | t₂ , B'
    with explicate-let m₃ (Goto cont) B' in el3
... | t₃ , B'' =
    let B₁↝B = ↝-create-block t B₁ B cont cb1 in
    let B↝B' = explicate-let-blocks m₂ (Goto cont) t₂ B B' el2 in
    let B'↝B'' = explicate-let-blocks m₃ (Goto cont) t₃ B' B'' el3 in
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
explicate-pred-blocks (Let m₁ m₂) thn els t B₁ B₂ ep
    with explicate-pred m₂ (shift-tail thn 1) (shift-tail els 1) B₁ in el2
... | (t₂ , B)
    =
    let B₁↝B = explicate-pred-blocks m₂ (shift-tail thn 1) (shift-tail els 1) t₂ B₁ B el2 in
    let B↝B₂ = explicate-let-blocks m₁ t₂ t B B₂ ep in
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

-- TODO: add the premise: B₁ is a prefix of B₂
postulate interp-tail-blocks : ∀ (n : ℕ) (t : CTail) (ρ : Env Value) (B₁ B₂ : Blocks) (s : Inputs) → interp-tail n t ρ B₁ s ≡ interp-tail n t ρ B₂ s

-- Problem: this isn't true... increasing the gas could turn a timeout into a good result...
postulate interp-tail-mono : ∀ (n n' : ℕ)(t : CTail) (ρ : Env Value) (B : Blocks) (s : Inputs) → n ≤ n' → interp-tail n t ρ B s ≡ interp-tail n' t ρ B s

postulate interp-shift-tail : ∀ (n : ℕ) (t : CTail) (v : Value) (ρ₁ ρ₂ : Env Value) (B : Blocks) (s : Inputs) → interp-tail n (shift-tail t (length ρ₁)) (ρ₁ ++ (v ∷ ρ₂)) B s ≡ interp-tail n t (ρ₁ ++ ρ₂) B s

interp-tail-def : ∀ n (e : CExp) (t : CTail) ρ B s
    → interp-tail (suc n) (Let e t) ρ B s
     ≡ ((interp-CExp e ρ) then λ v₁ → interp-tail n t (v₁ ∷ ρ) B) s
interp-tail-def zero e t ρ B s rewrite then-timeout{B = Value} (interp-CExp e ρ) s = refl
interp-tail-def (suc n) e t ρ B s = refl

explicate-let-correct :  ∀ (m : Mon) (t t' : CTail) (ρ : Env Value) (B₂ B₃ : Blocks) (s : Inputs)
  → explicate-let m t B₂ ≡ (t' , B₃)
  → Σ[ n ∈ ℕ ] interp-tail (suc n) t' ρ B₃ s
      ≡ ((interp-mon m ρ) then λ v → interp-tail n t (v ∷ ρ) B₃) s
explicate-let-correct (Atom a) t t' ρ B B₂ s refl = 0 , refl
explicate-let-correct Read t t' ρ B B₂ s refl = 0 , refl
explicate-let-correct (Uni op a) t t' ρ B B₂ s refl = 0 , refl
explicate-let-correct (Bin op a₁ a₂) t t' ρ B B₂ s refl = 0 , refl
explicate-let-correct (Let m₁ m₂) t t' ρ B₂ B₃ s el
    with explicate-let m₂ (shift-tail t 1) B₂ in et2
... | t₂ , B₄
    with explicate-let-correct m₁ t₂ t' ρ B₄ B₃ s el
... | n , IH1
    = n , Goal
    where
    Goal : interp-tail (suc n) t' ρ B₃ s ≡
          (((λ s₁ →
           (interp-mon m₁ ρ then (λ v₁ → interp-mon m₂ (v₁ ∷ ρ))) s₁)
            then (λ v → interp-tail n t (v ∷ ρ) B₃)) s)
    Goal rewrite IH1
        with interp-mon m₁ ρ s
    ... | nothing = refl
    ... | just (v₁ , s1)
        with explicate-let-correct m₂ (shift-tail t 1) t₂ (v₁ ∷ ρ) B₂ B₄ s1 et2
    ... | k , IH2
        rewrite interp-tail-mono n ((suc k) ⊔ n) t₂ (v₁ ∷ ρ) B₃ s1 (m≤n⊔m (suc k) n)
        | interp-tail-mono (suc k) ((suc k) ⊔ n) t₂ (v₁ ∷ ρ) B₄ s1 (m≤m⊔n (suc k) n)
        | interp-tail-blocks (suc k ⊔ n) t₂ (v₁ ∷ ρ) B₄ B₃ s1
        | IH2
        with interp-mon m₂ (v₁ ∷ ρ) s1
    ... | nothing = refl
    ... | just (v₂ , s2)
        rewrite interp-tail-mono k (k ⊔ n) (shift-tail t 1) (v₂ ∷ v₁ ∷ ρ) B₄ s2 (m≤m⊔n k n)
        | interp-tail-blocks (k ⊔ n) (shift-tail t 1) (v₂ ∷ v₁ ∷ ρ) B₄ B₃ s2
        | interp-tail-mono n (k ⊔ n) t (v₂ ∷ ρ) B₃ s2 (m≤n⊔m k n)
        | interp-shift-tail (k ⊔ n) t v₁ [ v₂ ] ρ B₃ s2
        = refl
explicate-let-correct (If m₁ m₂ m₃) t t' ρ B B₂ s el = {!!}

explicate-pred-correct : ∀ (m₁ : Mon) (t₁ t₂ t₃ : CTail) (ρ : Env Value) (B₄ B₅ : Blocks) (s : Inputs)
  → explicate-pred m₁ t₂ t₃ B₄ ≡ (t₁ , B₅)
  → Σ[ n ∈ ℕ ] interp-tail n t₁ ρ B₅ s
      ≡ ((interp-mon m₁ ρ) then
        λ v → try (toBool v) then
        λ { true →  interp-tail n t₂ ρ B₅
          ; false → interp-tail n t₃ ρ B₅ }) s
explicate-pred-correct m₁ t₂ t₃ ρ B₄ B₅ s ep = {!!}

explicate-tail-correct : ∀ (m : Mon) (ρ : Env Value) (B B' : Blocks) (t : CTail) (s : Inputs)
  → explicate-tail m B ≡ (t , B')
  → Σ[ n ∈ ℕ ] interp-tail n t ρ B' s ≡ interp-mon m ρ s
explicate-tail-correct (Atom a) ρ B B' t s refl = 1 , refl 
explicate-tail-correct Read ρ B B' t s refl = 1 , refl
explicate-tail-correct (Uni op a) ρ B B' t s refl = 1 , refl
explicate-tail-correct (Bin op a₁ a₂) ρ B B' t s refl = 1 , refl
explicate-tail-correct (Let m₁ m₂) ρ B B' t s et
    with explicate-tail m₂ B in et2
... | t₂ , B₂
    with explicate-let m₁ t₂ B₂ in el
... | t₁ , B₃
    with et
... | refl
    with explicate-let-correct m₁ t₂ t₁ ρ B₂ B₃ s el
... | n , it1
    with interp-mon m₁ ρ s
... | nothing = suc n , it1
... | just (v , s') 
    with explicate-tail-correct m₂ (v ∷ ρ) B B₂ t₂ s' et2
... | n' , it2
    = (suc n) ⊔ n' , Goal
   where
   Goal : interp-tail ((suc n) ⊔ n') t₁ ρ B₃ s ≡ interp-mon m₂ (v ∷ ρ) s'
   Goal
     rewrite interp-tail-mono (suc n) ((suc n) ⊔ n') t₁ ρ B₃ s (m≤m⊔n (suc n) n') -- upgrade it1
     | it1
     | interp-tail-mono n' ((suc n) ⊔ n') t₂ (v ∷ ρ) B₂ s' (m≤n⊔m (suc n) n')
     | interp-tail-mono n ((suc n) ⊔ n') t₂ (v ∷ ρ) B₃ s' (≤-trans (n≤1+n _) (m≤m⊔n (suc n) n')) -- upgrade the goal
     | interp-tail-blocks ((suc n) ⊔ n') t₂ (v ∷ ρ) B₂ B₃ s'
     | it2
     = refl
explicate-tail-correct (If m₁ m₂ m₃) ρ B B' t s et
    with explicate-tail m₂ B in et2
... | t₂ , B₂
    with explicate-tail m₃ B₂ in et3
... | t₃ , B₃
    with explicate-pred m₁ t₂ t₃ B₃ in ep
... | t₁ , B₄    
    with et
... | refl
    with explicate-pred-correct m₁ t₁ t₂ t₃ ρ B₃ B₄ s ep
... | n , it1    
    with interp-mon m₁ ρ s
... | nothing = n , it1
... | just (Int m , s') = n , it1
... | just (Bool true , s')
    with explicate-tail-correct m₂ ρ B B₂ t₂ s' et2
... | n' , it2 = n ⊔ n' , Goal
    where
    Goal : interp-tail (n ⊔ n') t₁ ρ B₄ s ≡ interp-mon m₂ ρ s'
    Goal
        rewrite interp-tail-mono n (n ⊔ n') t₁ ρ B₄ s (m≤m⊔n n n')
        | it1
        | interp-tail-mono n (n ⊔ n') t₂ ρ B₄ s' (m≤m⊔n n n')
        | interp-tail-mono n' (n ⊔ n') t₂ ρ B₂ s' (m≤n⊔m n n')
        | interp-tail-blocks (n ⊔ n') t₂ ρ B₂ B₄ s'
        | it2
        = refl
explicate-tail-correct (If m₁ m₂ m₃) ρ B B' t s et | t₂ , B₂ | t₃ , B₃ | t₁ , B₄ | refl | n , it1    
    | just (Bool false , s')
    with explicate-tail-correct m₃ ρ B₂ B₃ t₃ s' et3
... | n' , it3 = n ⊔ n' , Goal
    where
    Goal : interp-tail (n ⊔ n') t₁ ρ B₄ s ≡ interp-mon m₃ ρ s'
    Goal
        rewrite interp-tail-mono n (n ⊔ n') t₁ ρ B₄ s (m≤m⊔n n n')
        | it1
        | interp-tail-mono n (n ⊔ n') t₃ ρ B₄ s' (m≤m⊔n n n')
        | interp-tail-mono n' (n ⊔ n') t₃ ρ B₃ s' (m≤n⊔m n n')
        | interp-tail-blocks (n ⊔ n') t₃ ρ B₃ B₄ s'
        | it3
        = refl

explicate-correct : ∀ (m : Mon) (s : Inputs)
  → Σ[ n ∈ ℕ ] interp-CIf n (explicate m) s ≡ interp-LMonIf m s
explicate-correct m s
    with explicate-tail m []
... | t , B' = {!!} -- rewrite explicate-tail-correct m [] s = refl
