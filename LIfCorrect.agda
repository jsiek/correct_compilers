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
↝-create-block t B B' lbl refl = [ t ] , refl

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
explicate-assign-blocks y (Assign x m₁ m₂) t t' B₁ B₂ refl =
    let (t₂ , B) = explicate-assign y m₂ t B₁ in 
    let B₁↝B = explicate-assign-blocks y m₂ t t₂ B₁ B refl in
    let B↝B₂ = explicate-assign-blocks x m₁ t₂ t' B B₂ refl in
    ↝-trans B₁↝B B↝B₂ 
explicate-assign-blocks y (If m₁ m₂ m₃) t t' B₁ B₂ el =
    let (cont , B) = create-block t B₁ in
    let (t₂ , B') = explicate-assign y m₂ (Goto cont) B in 
    let (t₃ , B'') = explicate-assign y m₃ (Goto cont) B' in 
    let B₁↝B = ↝-create-block t B₁ B cont refl in
    let B↝B' = explicate-assign-blocks y m₂ (Goto cont) t₂ B B' refl in
    let B'↝B'' = explicate-assign-blocks y m₃ (Goto cont) t₃ B' B'' refl in
    let B''↝B₂ = explicate-pred-blocks m₁ t₂ t₃ t' B'' B₂ el in
    ↝-trans B₁↝B (↝-trans B↝B' (↝-trans B'↝B'' B''↝B₂))

explicate-pred-blocks (Atom a) t₁ t₂ t B₁ B₂ refl =
    let (l1 , B) = create-block t₁ B₁ in 
    let (l2 , B') = create-block t₂ B in 
    let B₁↝B = ↝-create-block t₁ B₁ B l1 refl in
    let B↝B' = ↝-create-block t₂ B B' l2 refl in
    ↝-trans B₁↝B B↝B'
explicate-pred-blocks Read t₁ t₂ t B₁ B₂ refl = [] , ++-identityʳ B₁ 
explicate-pred-blocks (Uni Neg a) t₁ t₂ t B₁ B₂ refl = [] , (++-identityʳ B₁)
explicate-pred-blocks (Uni Not a) t₁ t₂ t B₁ B₂ refl =
    let (l2 , B) = create-block t₂ B₁ in
    let (l1 , B') = create-block t₁ B in 
    let B₁↝B = ↝-create-block t₂ B₁ B l2 refl in
    let B↝B' = ↝-create-block t₁ B B' l1 refl in
    ↝-trans B₁↝B B↝B'
explicate-pred-blocks (Bin op a₁ a₂) t₁ t₂ t B₁ B₂ refl =
    let (l1 , B) = create-block t₁ B₁ in 
    let (l2 , B') = create-block t₂ B in 
    let B₁↝B = ↝-create-block t₁ B₁ B l1 refl in
    let B↝B' = ↝-create-block t₂ B B' l2 refl in
    ↝-trans B₁↝B B↝B'
explicate-pred-blocks (Assign x m₁ m₂) thn els t B₁ B₂ ep =
    let (t₂ , B) = explicate-pred m₂ thn els B₁ in 
    let B₁↝B = explicate-pred-blocks m₂ thn els t₂ B₁ B refl in
    let B↝B₂ = explicate-assign-blocks x m₁ t₂ t B B₂ ep in
    ↝-trans B₁↝B B↝B₂ 
explicate-pred-blocks (If m₁ m₂ m₃) thn els t B₁ B₂ refl =
    let (lbl-thn , B) = create-block thn B₁ in 
    let (lbl-els , B') = create-block els B in 
    let (t₂ , B'') = explicate-pred m₂ (Goto lbl-thn) (Goto lbl-els) B' in 
    let (t₃ , B''') = explicate-pred m₃ (Goto lbl-thn) (Goto lbl-els) B'' in 
    let B₁↝B = ↝-create-block thn B₁ B lbl-thn refl in
    let B↝B' = ↝-create-block els B B' lbl-els refl in
    let B'↝B'' = explicate-pred-blocks m₂ (Goto lbl-thn) (Goto lbl-els) t₂ B' B'' refl in
    let B''↝B''' = explicate-pred-blocks m₃ (Goto lbl-thn) (Goto lbl-els) t₃ B'' B''' refl in
    let B'''↝B₂ = explicate-pred-blocks m₁ t₂ t₃ t B''' B₂ refl in
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
eval-tail-blocks (If op a₁ a₂ thn els) ρ B₁ B₂ s s' v B12 (if-⇓-true iop t⇓) =
  if-⇓-true iop (eval-tail-blocks _ ρ B₁ B₂ _ s' v B12 t⇓)
eval-tail-blocks (If op a₁ a₂ thn els) ρ B₁ B₂ s s' v B12 (if-⇓-false iop t⇓) =
  if-⇓-false iop (eval-tail-blocks _ ρ B₁ B₂ _ s' v B12 t⇓)
eval-tail-blocks (Goto l) ρ B₁ B₂ s s' v B12 (goto-⇓ nth t⇓) =
  goto-⇓ (nth-blocks B12 nth) (eval-tail-blocks _ ρ B₁ B₂ s s' v B12 t⇓)

create-block-nth : ∀ (t : CTail) (B B' : Blocks) (lbl : Id)
  → create-block t B ≡ (lbl , B')
  → nth B' lbl ≡ just t
create-block-nth t B B' lbl refl rewrite nth-++-1 B t = refl


explicate-pred-correct : ∀ (e : IL1-Exp) {thn els : CTail}{ρ : Env Value}{s₁ s₂ s₃ : Inputs}
   → explicate-pred e thn els B ≡ (t , B')
   → interp-il1-exp e ρ s₁ ≡ just (Value.Bool b , s₂)
   → B' , ρ , s₁ ⊢ t ⟶ step t' , ρ' , s''
   (if b then thn else els)

-- explicate-pred-correct : ∀ (e₁ : IL1-Exp) (t₁ t₂ t₃ : CTail) (ρ : Env Value)
--     (B₄ B₅ : Blocks) (s s1 : Inputs) (r : Value × Inputs) (b : 𝔹)
--   → explicate-pred e₁ t₂ t₃ B₄ ≡ (t₁ , B₅)
--   → interp-il1-exp e₁ ρ s ≡ just (Value.Bool b , s1)
--   -- Problem! ρ is incorrect below, if e₁ is Assign, ρ changes!
--   → ρ , s1 , B₅ ⊢ (if b then t₂ else t₃) ⇓ r
--   → ρ , s , B₅ ⊢ t₁ ⇓ r

-- explicate-assign-correct : ∀{y : Id}{e : IL1-Exp} {t t' : CTail}{ρ : Env Value}
--    {B₂ B₃ : Blocks} {s s1 : Inputs} {v : Value}{r : Value × Inputs}
--   → explicate-assign y e t B₂ ≡ (t' , B₃)
--   → interp-il1-exp e ρ s ≡ just (v , s1)
--   → (update ρ y v) , s1 , B₃ ⊢ t ⇓ r
--   → ρ , s , B₃ ⊢ t' ⇓ r

-- explicate-tail-correct : ∀ {e : IL1-Exp}{ρ : Env Value}{B B' : Blocks}{t : CTail}{s : Inputs}{r : Value × Inputs}
--   → explicate-tail e B ≡ (t , B')
--   → interp-il1-exp e ρ s ≡ just r
--   →  ρ , s , B' ⊢ t ⇓ r
  


