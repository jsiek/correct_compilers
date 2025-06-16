module LIf2ExplicateCorrect where

open import Agda.Builtin.Bool using (true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ)
open import Data.Product
open import Data.Integer using (ℤ; _-_; 0ℤ)
open import Data.List
open import Data.List.Properties
open import Data.Maybe
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Reader
open import Utilities
open import LIf2

--------------- Proof of correctness for Explicate Control -------------------

Blocks = List CStmt

_↝_ : Blocks → Blocks → Set
B₁ ↝ B₂ = Σ[ B ∈ Blocks ] B₁ ++ B ≡ B₂

↝-trans : ∀ {B₁ B₂ B₃ : Blocks}
  → B₁ ↝ B₂  → B₂ ↝ B₃
  → B₁ ↝ B₃
↝-trans {B₁}{B₂}{B₃} (B , eq12) (B' , eq23)
  rewrite sym eq12 | sym eq23  | ++-assoc B₁ B B'
  = B ++ B' , refl

↝-create-block : (t : CStmt) (B B' : Blocks) (lbl : ℕ)
  → create-block t B ≡ (lbl , B')
  → B ↝ B'
↝-create-block t B B' lbl refl = [ t ] , refl

nth-blocks : ∀ {B₁ B₂ : Blocks} {l : ℕ} {t : CStmt}
  → B₁ ↝ B₂
  → nth B₁ l ≡ just t
  → nth B₂ l ≡ just t
nth-blocks {B₁}{l = l}{t} (B , refl) n1 = nth-++-just B₁ B l t n1

postulate explicate-tail-blocks : ∀ (m : IL-Exp) (B₁ B₂ : Blocks) (t : CStmt) → explicate-tail m B₁ ≡ (t , B₂) → B₁ ↝ B₂
postulate explicate-assign-blocks : ∀ (x : Id) (m : IL-Exp) (t t' : CStmt) (B₁ B₂ : Blocks) → explicate-assign x m t B₁ ≡ (t' , B₂) → B₁ ↝ B₂
postulate explicate-pred-blocks : ∀ (m : IL-Exp) (t₁ t₂ t : CStmt) (B₁ B₂ : Blocks) → explicate-pred m t₁ t₂ B₁ ≡ (t , B₂) → B₁ ↝ B₂

postulate eval-tail-blocks : ∀ (t : CStmt) (ρ ρ′ : Env Value) (B₁ B₂ : Blocks) (s s′ : Inputs) (v : Value) → B₁ ↝ B₂ → (s , ρ) , B₁ ⊢ᶜ t ⇓ v ⊣ (s′ , ρ′) → (s , ρ) , B₂ ⊢ᶜ t ⇓ v ⊣ (s′ , ρ′)


sub-not-bool : ∀ (n₁ n₂ : Value)
  → sub n₁ n₂ ≡ just (Bool true)
  → ⊥
sub-not-bool (Int x) (Int x₁) ()
sub-not-bool (Int x) (Bool x₁) ()

explicate-assign-correct : ∀(x : Id)(e : IL-Exp)(t : CStmt) (ρ ρ′ ρ″ : Env Value) (s s′ s″ : Inputs) (B B′ : List CStmt) (c : CStmt)
    (n v : Value)
  → (s , ρ) ⊢ e ⇓ n ⊣ (s′ , ρ′)
  → (s′ , update ρ′ x n) , B ⊢ᶜ t ⇓ v ⊣ (s″ , ρ″)
  → explicate-assign x e t B ≡ (c , B′)
  → (s , ρ) , B′ ⊢ᶜ c ⇓ v ⊣ (s″ , ρ″)

explicate-pred-correct-true : ∀ (e₁ : IL-Exp) (c₂ c₃ c : CStmt) (v : Value) (s s₁ s″ : Inputs) (ρ ρ₁ ρ″ : Env Value) (B′ B″ B‴ : Blocks)
  → (s , ρ) ⊢ e₁ ⇓ Bool true ⊣ (s₁ , ρ₁)
  → (s₁ , ρ₁) , B′ ⊢ᶜ c₂ ⇓ v ⊣ (s″ , ρ″)
  → B′ ↝ B″
  → explicate-pred e₁ c₂ c₃ B″ ≡ (c , B‴)
  → (s , ρ) , B‴ ⊢ᶜ c ⇓ v ⊣ (s″ , ρ″)
explicate-pred-correct-true (Atom a) c₂ c₃ c v s s₁ s″ ρ ρ₁ ρ″ B′ B″ B‴ (⇓atom ia) c₂⇓v B′↝B″ refl =
    let B₂ = B″ ++ [ c₂ ] in
    let B₃ = B₂ ++ [ c₃ ] in
    let B″↝B₂ : B″ ↝ B₂
        B″↝B₂ = [ c₂ ] , refl in
    let B₂↝B₃ : B₂ ↝ B₃
        B₂↝B₃ = [ c₃ ] , refl in
    let c₂⇓v′ = eval-tail-blocks c₂ ρ ρ″ B′ B″ s s″ v B′↝B″ c₂⇓v in
    let c₂⇓v″ = eval-tail-blocks c₂ ρ ρ″ B″ B₂ s s″ v B″↝B₂ c₂⇓v′ in
    let c₂⇓v‴ = eval-tail-blocks c₂ ρ ρ″ B₂ B₃ s s″ v B₂↝B₃ c₂⇓v″ in
    let nth2 : nth B₂ (length B″) ≡ just c₂
        nth2 = nth-++-length B″ [] c₂ in
    let nth3 : nth B₃ (length B″) ≡ just c₂
        nth3 = nth-blocks B₂↝B₃ nth2 in
    ⇓if-true ia refl refl nth3 c₂⇓v‴
explicate-pred-correct-true (Sub a₁ a₂) c₂ c₃ c v s s₁ s″ ρ ρ₁ ρ″ B′ B″ B‴ (⇓sub{n₁ = n₁}{n₂} x x₁ subv) c₂⇓v B′↝B″ refl
    with sub-not-bool n₁ n₂ subv
... | ()
explicate-pred-correct-true (Eq a₁ a₂) c₂ c₃ c v s s₁ s″ ρ ρ₁ ρ″ B′ B″ B‴ (⇓eq ia1 ia2 eq) c₂⇓v B′↝B″ refl =
    let B₂ = B″ ++ [ c₂ ] in
    let B₃ = B₂ ++ [ c₃ ] in
    let B″↝B₂ : B″ ↝ B₂
        B″↝B₂ = [ c₂ ] , refl in
    let B₂↝B₃ : B₂ ↝ B₃
        B₂↝B₃ = [ c₃ ] , refl in
    let c₂⇓v′ = eval-tail-blocks c₂ ρ ρ″ B′ B″ s s″ v B′↝B″ c₂⇓v in
    let c₂⇓v″ = eval-tail-blocks c₂ ρ ρ″ B″ B₂ s s″ v B″↝B₂ c₂⇓v′ in
    let c₂⇓v‴ = eval-tail-blocks c₂ ρ ρ″ B₂ B₃ s s″ v B₂↝B₃ c₂⇓v″ in
    let nth2 : nth B₂ (length B″) ≡ just c₂
        nth2 = nth-++-length B″ [] c₂ in
    let nth3 : nth B₃ (length B″) ≡ just c₂
        nth3 = nth-blocks B₂↝B₃ nth2 in
   ⇓if-true ia1 ia2 eq nth3 c₂⇓v‴
explicate-pred-correct-true (Assign x e₁ e₂) c-thn c-els c v s s₁ s″ ρ ρ₁ ρ″ B′ B″ B⁗ (⇓assign{s′ = s′}{ρ′}{n₁ = n₁}{n₂} e₁⇓ e₂⇓) c-thn⇓v B′↝B″ ea1
    with explicate-pred e₂ c-thn c-els B″ in ep2
... | c₂ , B‴ =
  let IH2 : (s′ , update ρ′ x n₁) , B‴ ⊢ᶜ c₂ ⇓ v ⊣ (s″ , ρ″)
      IH2 = explicate-pred-correct-true e₂ c-thn c-els c₂ v s′ s₁ s″ (update ρ′ x n₁) ρ₁ ρ″ B′ B″ B‴ e₂⇓ c-thn⇓v B′↝B″ ep2 in
  explicate-assign-correct x e₁ c₂ ρ ρ′ ρ″ s s′ s″ B‴ B⁗ c n₁ v e₁⇓ IH2 ea1 
  
explicate-pred-correct-true (If e₁ e₂ e₃) c₂ c₃ c v s s₁ s″ ρ ρ₁ ρ″ B′ B″ B‴ e₁⇓ c₂⇓v B′↝B″ ep = {!!}



explicate-pred-correct-false : ∀ (e₁ : IL-Exp) (c₂ c₃ c : CStmt) (v : Value) (s s₁ s″ : Inputs) (ρ ρ₁ ρ″ : Env Value) (B′ B″ B‴ : Blocks)
  → (s , ρ) ⊢ e₁ ⇓ Bool false ⊣ (s₁ , ρ₁)
  → (s₁ , ρ₁) , B′ ⊢ᶜ c₃ ⇓ v ⊣ (s″ , ρ″)
  → explicate-pred e₁ c₂ c₃ B″ ≡ (c , B‴)
  → (s , ρ) , B‴ ⊢ᶜ c ⇓ v ⊣ (s″ , ρ″)
explicate-pred-correct-false e₁ c₂ c₃ c v s s₁ s″ ρ ρ₁ ρ″ B′ B″ e₁⇓ c₂⇓v ep = {!!}



explicate-assign-correct x (Atom a) t ρ ρ′ ρ″ s s′ s″ B B′ c n v (⇓atom ia) t⇓v refl =
  ⇓assign Goal t⇓v
  where
  Goal : try (interp-atm a ρ) s ≡ just (n , s)
  Goal rewrite ia = refl
explicate-assign-correct x Read t ρ ρ′ ρ″ s s′ s″ B B′ c n v ⇓read t⇓v refl = ⇓assign refl t⇓v
explicate-assign-correct x (Sub a₁ a₂) t ρ ρ′ ρ″ s s′ s″ B B′ c n v (⇓sub{n₁ = n₁}{n₂} ia₁ ia₂ subv) t⇓v refl =
    ⇓assign Goal t⇓v
    where
    Goal : (try (interp-atm a₁ ρ) then
            (λ v₁ → try (interp-atm a₂ ρ) then (λ v₂ → try (sub v₁ v₂)))) s
            ≡ just (n , s)
    Goal rewrite ia₁ | ia₂ | subv = refl
explicate-assign-correct x (Eq a₁ a₂) t ρ ρ′ ρ″ s s′ s″ B B′ c n v (⇓eq{n₁ = n₁}{n₂} ia₁ ia₂ eqv) t⇓v refl =
    ⇓assign Goal t⇓v
    where
    Goal : (try (interp-atm a₁ ρ) then
            (λ v₁ → try (interp-atm a₂ ρ) then (λ v₂ → try (equal v₁ v₂)))) s
            ≡ just (n , s)
    Goal rewrite ia₁ | ia₂ | eqv = refl
    
explicate-assign-correct x (Assign y e₁ e₂) t ρ ρ′ ρ″ s s′ s″ B B″ c₁ n v
   (⇓assign {ρ′ = ρ′₁}{n₁ = n₁} e₁⇓n₁ e₂⇓v) t⇓v ea1
   with explicate-assign x e₂ t B in ea2
... | c₂ , B′ =
   let ee₂⇓v = explicate-assign-correct x e₂ t (update ρ′₁ y n₁) ρ′ ρ″ _ s′ s″ B B′ c₂ n v e₂⇓v t⇓v ea2 in
   explicate-assign-correct y e₁ c₂  ρ ρ′₁ ρ″ s _ s″ B′ B″ c₁ n₁ v e₁⇓n₁ ee₂⇓v ea1

explicate-assign-correct x (If e₁ e₂ e₃) t ρ ρ′ ρ″ s s′ s″ B B‴ c n v (⇓if-true{sρ′ = (s₁ , ρ₁)} e₁⇓v₁ e₂⇓v₂) t⇓v ep1
    with explicate-assign x e₂ (Goto (length B)) (B ++ [ t ]) in ea2
... | c₂ , B′
    with explicate-assign x e₃ (Goto (length B)) B′ in ea3
... | c₃ , B″
    =
    let t⇓v′ = eval-tail-blocks t (update ρ′ x n) ρ″ B (B ++ [ t ]) s′ s″ v ([ t ] , refl) t⇓v in
    let IH2 = explicate-assign-correct x e₂ (Goto (length B)) ρ₁ ρ′ ρ″ s₁ s′ s″ (B ++ [ t ]) B′ c₂ n v e₂⇓v₂ (⇓goto (nth-++-length B [] t) t⇓v′) ea2 in
    let B′↝B″ = explicate-assign-blocks x e₃ (Goto (length B)) c₃ B′ B″ ea3 in
    explicate-pred-correct-true e₁ c₂ c₃ c v s s₁ s″ ρ ρ₁ ρ″ B′ B″ B‴ e₁⇓v₁ IH2 B′↝B″ ep1

explicate-assign-correct x (If e₁ e₂ e₃) t ρ ρ′ ρ″ s s′ s″ B B‴ c n v (⇓if-false{sρ′ = (s₁ , ρ₁)} e₁⇓v₁ e₃⇓v₃) t⇓v ep1
    with explicate-assign x e₂ (Goto (length B)) (B ++ [ t ]) in ea2
... | c₂ , B′
    with explicate-assign x e₃ (Goto (length B)) B′ in ea3
... | c₃ , B″
    =
    let B₁ = (B ++ t ∷ []) in
    let B↝B₁ : B ↝ B₁
        B↝B₁ = ([ t ] , refl) in
    let B₁↝B′ = explicate-assign-blocks x e₂ (Goto (length B)) c₂ B₁ B′ ea2 in
    let B↝B′ = ↝-trans B↝B₁ B₁↝B′ in
    let t⇓v′ = eval-tail-blocks t (update ρ′ x n) ρ″ B B′ s′ s″ v B↝B′ t⇓v in
    let nth1 : nth B₁ (length B) ≡ just t
        nth1 = nth-++-length B [] t in
    let nth2 : nth B′ (length B) ≡ just t
        nth2 = nth-blocks B₁↝B′ nth1 in
    let IH3 = explicate-assign-correct x e₃ (Goto (length B)) ρ₁ ρ′ ρ″ s₁ s′ s″ B′ B″ c₃ n v e₃⇓v₃ (⇓goto nth2 t⇓v′) ea3 in
    explicate-pred-correct-false e₁ c₂ c₃ c v s s₁ s″ ρ ρ₁ ρ″ B″ B″ B‴ e₁⇓v₁ IH3 ep1

explicate-tail-correct : ∀ (e : IL-Exp) (ρ ρ' : Env Value) (s s' : Inputs) (B B′ : List CStmt) (c : CStmt) (v : Value)
  → (s , ρ) ⊢ e ⇓ v ⊣ (s' , ρ')
  → explicate-tail e B ≡ (c , B′)
  → (s , ρ) , B′ ⊢ᶜ c ⇓ v ⊣ (s' , ρ')
explicate-tail-correct (Atom a) ρ ρ' s s' B B′ c v (⇓atom ia) refl = ⇓return Goal
  where Goal : try (interp-atm a ρ) s ≡ just (v , s)
        Goal rewrite ia = refl
explicate-tail-correct Read ρ ρ' s s' B B′ c v ⇓read refl = ⇓return refl
explicate-tail-correct (Sub a₁ a₂) ρ ρ' s s' B B′ c v (⇓sub{n₁ = n₁}{n₂} ia1 ia2 subv) refl = ⇓return Goal
  where Goal : (try (interp-atm a₁ ρ) then
               (λ v₁ → try (interp-atm a₂ ρ) then (λ v₂ → try (sub v₁ v₂)))) s
                ≡ just (v , s)
        Goal rewrite ia1 | ia2 | subv = refl
explicate-tail-correct (Eq a₁ a₂) ρ ρ' s s' B B′ c v (⇓eq{n₁ = n₁}{n₂} ia1 ia2 subv) refl = ⇓return Goal
  where Goal : (try (interp-atm a₁ ρ) then
               (λ v₁ → try (interp-atm a₂ ρ) then (λ v₂ → try (equal v₁ v₂)))) s
                ≡ just (v , s)
        Goal rewrite ia1 | ia2 | subv = refl
explicate-tail-correct (Assign x e₁ e₂) ρ ρ″ s s″ B B′ c v (⇓assign {s′ = s′}{ρ′}{n₁ = n₁} e₁⇓n₁ e₂⇓v) et
    with explicate-tail e₂ B in et2
... | c₂ , B₂ =
  let IH2 = explicate-tail-correct e₂ (update ρ′ x n₁) ρ″ s′ s″ B B₂ c₂ v e₂⇓v et2 in
  explicate-assign-correct x e₁ c₂ ρ ρ′ ρ″ s s′ s″ B₂ B′ c n₁ v e₁⇓n₁ IH2 et
explicate-tail-correct (If e₁ e₂ e₃) ρ ρ″ s s″ B B′ c v (⇓if-true e₁⇓v₁ e₂⇓v₂) et = {!!}
explicate-tail-correct (If e₁ e₂ e₃) ρ ρ″ s s″ B B′ c v (⇓if-false e₁⇓v₁ e₃⇓v₃) et = {!!}

explicate-correct : ∀ (p : IL-Prog) (s : Inputs) (v : Value)
  → interp-ilprog p s v
  → interp-prog (explicate p) s v
explicate-correct (Program n e) s v ((s' , ρ') , e⇓v)
    with explicate-tail e [] in et
... | c , B =
    let c⇓v = explicate-tail-correct e (replicate n (Int 0ℤ)) ρ' s s' [] B c v e⇓v et in
    let c⇓v′ = eval-tail-blocks c (replicate n (Int 0ℤ)) ρ' B (B ++ (c ∷ [])) s s' v (c ∷ [] , refl) c⇓v in
    ((s' , ρ')) , ⇓goto (nth-++-length B [] c) c⇓v′
    

