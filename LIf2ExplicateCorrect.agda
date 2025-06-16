module LIf2ExplicateCorrect where

open import Agda.Builtin.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _+_)
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

↝-refl : ∀ {B : Blocks}
  → B ↝ B
↝-refl {B} = [] , (++-identityʳ B)

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

nth-create-block : ∀ {B : Blocks}{c : CStmt}
  → nth (proj₂ (create-block c B)) (proj₁ (create-block c B)) ≡ just c
nth-create-block {B}{c}
  rewrite nth-++-length B [] c = refl

nth-blocks : ∀ {B₁ B₂ : Blocks} {l : ℕ} {t : CStmt}
  → B₁ ↝ B₂
  → nth B₁ l ≡ just t
  → nth B₂ l ≡ just t
nth-blocks {B₁}{l = l}{t} (B , refl) n1 = nth-++-just B₁ B l t n1

postulate explicate-tail-blocks : ∀ (m : IL-Exp) (B₁ B₂ : Blocks) (t : CStmt) → explicate-tail m B₁ ≡ (t , B₂) → B₁ ↝ B₂
postulate explicate-assign-blocks : ∀ (x : Id) (m : IL-Exp) (t t' : CStmt) (B₁ B₂ : Blocks) → explicate-assign x m t B₁ ≡ (t' , B₂) → B₁ ↝ B₂
postulate explicate-pred-blocks : ∀ (m : IL-Exp) (t₁ t₂ t : CStmt) (B₁ B₂ : Blocks) → explicate-pred m t₁ t₂ B₁ ≡ (t , B₂) → B₁ ↝ B₂

postulate eval-blocks : ∀ {t : CStmt}{ ρ ρ′ : Env Value}{B₁ B₂ : Blocks}{s s′ : Inputs}{v : Value} → B₁ ↝ B₂ → (s , ρ) , B₁ ⊢ᶜ t ⇓ v ⊣ (s′ , ρ′) → (s , ρ) , B₂ ⊢ᶜ t ⇓ v ⊣ (s′ , ρ′)


sub-not-bool : ∀ {n₁ n₂ : Value}{b : 𝔹}
  → sub n₁ n₂ ≡ just (Bool b)
  → ⊥
sub-not-bool {Int x}{Int x₁} ()
sub-not-bool {Int x}{Bool x₁} ()

explicate-assign-correct : ∀{x : Id}{e : IL-Exp}{t : CStmt}{ρ ρ′ ρ″ : Env Value}{s s′ s″ : Inputs}{B B′ : List CStmt}{c : CStmt}
    {n v : Value}
  → (s , ρ) ⊢ e ⇓ n ⊣ (s′ , ρ′)
  → (s′ , update ρ′ x n) , B ⊢ᶜ t ⇓ v ⊣ (s″ , ρ″)
  → explicate-assign x e t B ≡ (c , B′)
  → (s , ρ) , B′ ⊢ᶜ c ⇓ v ⊣ (s″ , ρ″)

explicate-pred-correct : ∀ {e₁ : IL-Exp} {c₁ c₂ c₃ : CStmt} {b : 𝔹} {v : Value} {s s′ s″ : Inputs} {ρ ρ′ ρ″ : Env Value} {B′ B″ B‴ : Blocks}
  → (s , ρ) ⊢ e₁ ⇓ Bool b ⊣ (s′ , ρ′)
  → (b ≡ true  →  (s′ , ρ′) , B′ ⊢ᶜ c₂ ⇓ v ⊣ (s″ , ρ″))
  → (b ≡ false  →  (s′ , ρ′) , B′ ⊢ᶜ c₃ ⇓ v ⊣ (s″ , ρ″))
  → B′ ↝ B″
  → explicate-pred e₁ c₂ c₃ B″ ≡ (c₁ , B‴)
  → (s , ρ) , B‴ ⊢ᶜ c₁ ⇓ v ⊣ (s″ , ρ″)
explicate-pred-correct {Atom a} {c₁} {c₂} {c₃} {false} {v} {s} {s′} {s″} {ρ} {ρ′} {ρ″} {B′} {B″} {B‴} (⇓atom ia) true→c₂⇓v false→c₃⇓v B′↝B″ refl =
    let B₂ = B″ ++ [ c₂ ] in
    let B₃ = B₂ ++ [ c₃ ] in
    let B″↝B₂ : B″ ↝ B₂
        B″↝B₂ = [ c₂ ] , refl in
    let B₂↝B₃ : B₂ ↝ B₃
        B₂↝B₃ = [ c₃ ] , refl in
    let c₃⇓v′ = eval-blocks B′↝B″ (false→c₃⇓v refl) in
    let c₃⇓v″ = eval-blocks B″↝B₂ c₃⇓v′ in
    let c₃⇓v‴ = eval-blocks B₂↝B₃ c₃⇓v″ in
    let nth2 : nth B₃ (length B₂) ≡ just c₃
        nth2 = nth-++-length B₂ [] c₃ in
    ⇓if-false ia refl refl nth2 c₃⇓v‴
explicate-pred-correct {Atom a} {c₁} {c₂} {c₃} {true} {v} {s} {s′} {s″} {ρ} {ρ′} {ρ″} {B′} {B″} {B‴} (⇓atom ia) true→c₂⇓v false→c₃⇓v B′↝B″ refl =
    let B₂ = B″ ++ [ c₂ ] in
    let B₃ = B₂ ++ [ c₃ ] in
    let B″↝B₂ : B″ ↝ B₂
        B″↝B₂ = [ c₂ ] , refl in
    let B₂↝B₃ : B₂ ↝ B₃
        B₂↝B₃ = [ c₃ ] , refl in
    let c₂⇓v′ = eval-blocks B′↝B″ (true→c₂⇓v refl) in
    let c₂⇓v″ = eval-blocks B″↝B₂ c₂⇓v′ in
    let c₂⇓v‴ = eval-blocks B₂↝B₃ c₂⇓v″ in
    let nth2 : nth B₂ (length B″) ≡ just c₂
        nth2 = nth-++-length B″ [] c₂ in
    let nth3 : nth B₃ (length B″) ≡ just c₂
        nth3 = nth-blocks B₂↝B₃ nth2 in
    ⇓if-true ia refl refl nth3 c₂⇓v‴
explicate-pred-correct {Sub a₁ a₂} {c₁} {c₂} {c₃} {b} {v} {s} {s′} {s″} {ρ} {ρ′} {ρ″} {B′} {B″} {B‴} (⇓sub x x₁ subv) true→c₂⇓v false→c₃⇓v B′↝B″ refl
    with sub-not-bool subv
... | ()
explicate-pred-correct {Eq a₁ a₂} {c₁} {c₂} {c₃} {true} {v} {s} {s′} {s″} {ρ} {ρ′} {ρ″} {B′} {B″} {B‴} (⇓eq ia1 ia2 eq) true→c₂⇓v false→c₃⇓v B′↝B″ refl =
    let B₂ = B″ ++ [ c₂ ] in
    let B₃ = B₂ ++ [ c₃ ] in
    let B″↝B₂ : B″ ↝ B₂
        B″↝B₂ = [ c₂ ] , refl in
    let B₂↝B₃ : B₂ ↝ B₃
        B₂↝B₃ = [ c₃ ] , refl in
    let c₂⇓v′ = eval-blocks B′↝B″ (true→c₂⇓v refl) in
    let c₂⇓v″ = eval-blocks B″↝B₂ c₂⇓v′ in
    let c₂⇓v‴ = eval-blocks B₂↝B₃ c₂⇓v″ in
    let nth2 : nth B₂ (length B″) ≡ just c₂
        nth2 = nth-++-length B″ [] c₂ in
    let nth3 : nth B₃ (length B″) ≡ just c₂
        nth3 = nth-blocks B₂↝B₃ nth2 in
   ⇓if-true ia1 ia2 eq nth3 c₂⇓v‴
explicate-pred-correct {Eq a₁ a₂} {c₁} {c₂} {c₃} {false} {v} {s} {s′} {s″} {ρ} {ρ′} {ρ″} {B′} {B″} {B‴} (⇓eq ia1 ia2 eq) true→c₂⇓v false→c₃⇓v B′↝B″ refl =
    let B₂ = B″ ++ [ c₂ ] in
    let B₃ = B₂ ++ [ c₃ ] in
    let B″↝B₂ : B″ ↝ B₂
        B″↝B₂ = [ c₂ ] , refl in
    let B₂↝B₃ : B₂ ↝ B₃
        B₂↝B₃ = [ c₃ ] , refl in
    let B′↝B₃ : B′ ↝ B₃
        B′↝B₃ = ↝-trans B′↝B″ (↝-trans B″↝B₂ B₂↝B₃) in
    let B′⊢c₃⇓v = (false→c₃⇓v refl) in
    let B₃⊢c₃⇓v = eval-blocks B′↝B₃ B′⊢c₃⇓v in
   ⇓if-false ia1 ia2 eq (nth-create-block{B₂}) B₃⊢c₃⇓v

explicate-pred-correct {Assign x e₁ e₂} {c} {c-thn} {c-els} {b} {v} {s} {s′} {s″} {ρ} {ρ′} {ρ″} {B′} {B″} {B‴} (⇓assign{s′ = s₁}{ρ₁}{n₁ = n₁}{n₂} e₁⇓ e₂⇓) true→c-thn⇓v false→c-els⇓v B′↝B″ refl =
    let (c₂ , B₂) = explicate-pred e₂ c-thn c-els B″ in
    let c₂⇓v : (s₁ , update ρ₁ x n₁) , B₂ ⊢ᶜ c₂ ⇓ v ⊣ (s″ , ρ″)
        c₂⇓v = explicate-pred-correct{c₁ = c₂}{B‴ = B₂} e₂⇓ true→c-thn⇓v false→c-els⇓v B′↝B″ refl in
    explicate-assign-correct e₁⇓ c₂⇓v refl

explicate-pred-correct {If e₁ e₂ e₃} {c} {c-thn} {c-els} {b} {v} {s} {s′} {s″} {ρ} {ρ′} {ρ″} {B′} {B″} {B‴} (⇓if-true e₁⇓true e₂⇓b) true→c-thn⇓v false→c-els⇓v B′↝B″ refl =
    let B₁ = B″ ++ [ c-thn ] in
    let lbl-thn = length B″ in
    let B₂ = B₁ ++ [ c-els ] in
    let lbl-els = length B₁ in

    let ep2 = explicate-pred e₂ (Goto lbl-thn) (Goto lbl-els) B₂ in
    let (c₂ , B₃) = ep2 in
    let ep3 = explicate-pred e₃ (Goto lbl-thn) (Goto lbl-els) B₃ in
    let (c₃ , B₄) = ep3 in

    let B′↝B₁ : B′ ↝ B₁
        B′↝B₁ = ↝-trans B′↝B″ ([ c-thn ] , refl) in
    let B₁↝B₂ : B₁ ↝ B₂
        B₁↝B₂ = [ c-els ] , refl in
    let B′↝B₂ : B′ ↝ B₂
        B′↝B₂ = ↝-trans B′↝B₁ B₁↝B₂ in
    let B₃↝B₄ : B₃ ↝ B₄
        B₃↝B₄ = explicate-pred-blocks e₃ (Goto lbl-thn) (Goto lbl-els) c₃ B₃ B₄ refl in

    let nth-thn : nth B₁ lbl-thn ≡ just c-thn
        nth-thn = nth-create-block{B″} in

    let nth-els : nth B₂ lbl-els ≡ just c-els
        nth-els = nth-create-block{B₁} in

    let IH2 = explicate-pred-correct {e₂}{B′ = B₂} e₂⇓b (λ b-true → let c-thn⇓ = (true→c-thn⇓v b-true) in ⇓goto (nth-blocks B₁↝B₂ nth-thn) (eval-blocks B′↝B₂ c-thn⇓))
                                               (λ b-false → let c-els⇓ = (false→c-els⇓v b-false) in ⇓goto nth-els (eval-blocks B′↝B₂ c-els⇓))
                                               ↝-refl refl in
    explicate-pred-correct {e₁} e₁⇓true (λ _ → IH2) (λ ()) B₃↝B₄ refl

explicate-pred-correct {If e₁ e₂ e₃} {c} {c-thn} {c-els} {b} {v} {s} {s′} {s″} {ρ} {ρ′} {ρ″} {B′} {B″} {B‴} (⇓if-false e₁⇓false e₃⇓b) true→c-thn⇓v false→c-els⇓v B′↝B″ refl =

    let B₁ = B″ ++ [ c-thn ] in
    let lbl-thn = length B″ in
    let B₂ = B₁ ++ [ c-els ] in
    let lbl-els = length B₁ in

    let ep2 = explicate-pred e₂ (Goto lbl-thn) (Goto lbl-els) B₂ in
    let (c₂ , B₃) = ep2 in
    let ep3 = explicate-pred e₃ (Goto lbl-thn) (Goto lbl-els) B₃ in
    let (c₃ , B₄) = ep3 in

    let B′↝B₁ : B′ ↝ B₁
        B′↝B₁ = ↝-trans B′↝B″ ([ c-thn ] , refl) in
    let B₁↝B₂ : B₁ ↝ B₂
        B₁↝B₂ = [ c-els ] , refl in
    let B′↝B₂ : B′ ↝ B₂
        B′↝B₂ = ↝-trans B′↝B₁ B₁↝B₂ in

    let B₂↝B₃ = (explicate-pred-blocks e₂ (Goto lbl-thn) (Goto lbl-els) c₂ B₂ B₃ refl) in
    
    let B′↝B₃ : B′ ↝ B₃
        B′↝B₃ = ↝-trans B′↝B₂ B₂↝B₃ in

    let B₁↝B₃ : B₁ ↝ B₃
        B₁↝B₃ = ↝-trans B₁↝B₂ B₂↝B₃ in

    let nth-thn : nth B₁ lbl-thn ≡ just c-thn
        nth-thn = nth-create-block{B″} in

    let nth-els : nth B₂ lbl-els ≡ just c-els
        nth-els = nth-create-block{B₁} in

    let IH3 = explicate-pred-correct {e₃}{B′ = B₃} e₃⇓b
               (λ b-true → let c-thn⇓ = (true→c-thn⇓v b-true) in ⇓goto (nth-blocks B₁↝B₃ nth-thn) (eval-blocks B′↝B₃ c-thn⇓))
               (λ b-false → let c-els⇓ = (false→c-els⇓v b-false) in ⇓goto (nth-blocks B₂↝B₃ nth-els) (eval-blocks B′↝B₃ c-els⇓))
               ↝-refl refl in

    explicate-pred-correct {e₁} e₁⇓false (λ ()) (λ _ → IH3) ↝-refl refl


explicate-assign-correct {x} {Atom a}{t}{ρ}{ρ′}{ρ″}{s}{s′}{s″}{B}{B′}{c}{n}{v} (⇓atom ia) t⇓v refl =
  ⇓assign Goal t⇓v
  where
  Goal : try (interp-atm a ρ) s ≡ just (n , s)
  Goal rewrite ia = refl
explicate-assign-correct {x}{ Read}{ t}{ ρ}{ ρ′}{ ρ″}{ s}{ s′}{ s″}{ B}{ B′}{ c}{ n}{ v} ⇓read t⇓v refl = ⇓assign refl t⇓v
explicate-assign-correct {x}{ (Sub a₁ a₂)}{ t}{ ρ}{ ρ′}{ ρ″}{ s}{ s′}{ s″}{ B}{ B′}{ c}{ n}{ v} (⇓sub{n₁ = n₁}{n₂} ia₁ ia₂ subv) t⇓v refl =
    ⇓assign Goal t⇓v
    where
    Goal : (try (interp-atm a₁ ρ) then
            (λ v₁ → try (interp-atm a₂ ρ) then (λ v₂ → try (sub v₁ v₂)))) s
            ≡ just (n , s)
    Goal rewrite ia₁ | ia₂ | subv = refl
explicate-assign-correct {x}{(Eq a₁ a₂)}{t}{ρ}{ρ′}{ρ″}{s}{ s′}{ s″}{ B}{ B′}{ c}{ n}{ v} (⇓eq{n₁ = n₁}{n₂} ia₁ ia₂ eqv) t⇓v refl =
    ⇓assign Goal t⇓v
    where
    Goal : (try (interp-atm a₁ ρ) then
            (λ v₁ → try (interp-atm a₂ ρ) then (λ v₂ → try (equal v₁ v₂)))) s
            ≡ just (n , s)
    Goal rewrite ia₁ | ia₂ | eqv = refl
    
explicate-assign-correct{ x}{ (Assign y e₁ e₂)}{t}{ρ}{ ρ′}{ ρ″}{ s}{ s′}{ s″}{ B}{ B″}{ c₁}{ n}{ v}
   (⇓assign {ρ′ = ρ′₁}{n₁ = n₁} e₁⇓n₁ e₂⇓v) t⇓v ea1
   with explicate-assign x e₂ t B in ea2
... | c₂ , B′ =
   let ee₂⇓v = explicate-assign-correct e₂⇓v t⇓v ea2 in
   explicate-assign-correct e₁⇓n₁ ee₂⇓v ea1

explicate-assign-correct {x}{ (If e₁ e₂ e₃)}{ t}{ ρ}{ ρ′}{ ρ″}{ s}{ s′}{ s″}{ B}{ B‴}{ c}{ n}{ v} (⇓if-true{sρ′ = (s₁ , ρ₁)} e₁⇓v₁ e₂⇓v₂) t⇓v ep1
    with explicate-assign x e₂ (Goto (length B)) (B ++ [ t ]) in ea2
... | c₂ , B′
    with explicate-assign x e₃ (Goto (length B)) B′ in ea3
... | c₃ , B″
    =
    let t⇓v′ = eval-blocks ([ t ] , refl) t⇓v in
    let IH2 = explicate-assign-correct e₂⇓v₂ (⇓goto (nth-++-length B [] t) t⇓v′) ea2 in
    let B′↝B″ = explicate-assign-blocks x e₃ (Goto (length B)) c₃ B′ B″ ea3 in
    explicate-pred-correct e₁⇓v₁ (λ _ → IH2) (λ ()) B′↝B″ ep1

explicate-assign-correct {x}{ (If e₁ e₂ e₃)}{ t}{ ρ}{ ρ′}{ ρ″}{ s}{ s′}{ s″}{ B}{ B‴}{ c}{ n}{ v} (⇓if-false{sρ′ = (s₁ , ρ₁)} e₁⇓v₁ e₃⇓v₃) t⇓v ep1
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
    let t⇓v′ = eval-blocks B↝B′ t⇓v in
    let nth1 : nth B₁ (length B) ≡ just t
        nth1 = nth-++-length B [] t in
    let nth2 : nth B′ (length B) ≡ just t
        nth2 = nth-blocks B₁↝B′ nth1 in
    let IH3 = explicate-assign-correct e₃⇓v₃ (⇓goto nth2 t⇓v′) ea3 in
    explicate-pred-correct e₁⇓v₁ (λ ()) (λ _ → IH3) ↝-refl ep1

explicate-tail-correct : ∀ {e : IL-Exp}{ρ ρ' : Env Value}{s s' : Inputs}{B B′ : List CStmt}{c : CStmt}{v : Value}
  → (s , ρ) ⊢ e ⇓ v ⊣ (s' , ρ')
  → explicate-tail e B ≡ (c , B′)
  → (s , ρ) , B′ ⊢ᶜ c ⇓ v ⊣ (s' , ρ')
explicate-tail-correct {(Atom a)}{ ρ}{ ρ'}{ s}{ s'}{ B}{ B′}{ c}{ v} (⇓atom ia) refl = ⇓return Goal
  where Goal : try (interp-atm a ρ) s ≡ just (v , s)
        Goal rewrite ia = refl
explicate-tail-correct{ Read}{ ρ}{ ρ'}{ s}{ s'}{ B}{ B′}{ c}{ v} ⇓read refl = ⇓return refl
explicate-tail-correct {(Sub a₁ a₂)}{ ρ}{ ρ'}{ s}{ s'}{ B}{ B′}{ c}{ v} (⇓sub{n₁ = n₁}{n₂} ia1 ia2 subv) refl = ⇓return Goal
  where Goal : (try (interp-atm a₁ ρ) then
               (λ v₁ → try (interp-atm a₂ ρ) then (λ v₂ → try (sub v₁ v₂)))) s
                ≡ just (v , s)
        Goal rewrite ia1 | ia2 | subv = refl
explicate-tail-correct {(Eq a₁ a₂)}{ ρ}{ ρ'}{ s}{ s'}{ B}{ B′}{ c}{ v} (⇓eq{n₁ = n₁}{n₂} ia1 ia2 subv) refl = ⇓return Goal
  where Goal : (try (interp-atm a₁ ρ) then
               (λ v₁ → try (interp-atm a₂ ρ) then (λ v₂ → try (equal v₁ v₂)))) s
                ≡ just (v , s)
        Goal rewrite ia1 | ia2 | subv = refl
explicate-tail-correct {(Assign x e₁ e₂)}{ ρ}{ ρ″}{ s}{ s″}{ B}{ B′}{ c}{ v} (⇓assign {s′ = s′}{ρ′}{n₁ = n₁} e₁⇓n₁ e₂⇓v) et
    with explicate-tail e₂ B in et2
... | c₂ , B₂ =
  let IH2 = explicate-tail-correct e₂⇓v et2 in
  explicate-assign-correct e₁⇓n₁ IH2 et
explicate-tail-correct {(If e₁ e₂ e₃)}{ ρ}{ ρ″}{ s}{ s″}{ B}{ B′}{ c}{ v} (⇓if-true{sρ′ = (s′ , ρ′)} e₁⇓true e₂⇓v) refl =
    let (c₂ , B₁) = explicate-tail e₂ B in
    let (c₃ , B₂) = explicate-tail e₃ B₁ in
    let c₂⇓ = explicate-tail-correct {e₂} e₂⇓v refl in
    let B₁↝B₂ : B₁ ↝ B₂
        B₁↝B₂ = explicate-tail-blocks e₃ B₁ B₂ c₃ refl in
    explicate-pred-correct {e₁} e₁⇓true (λ _ → c₂⇓) (λ ()) B₁↝B₂ refl
explicate-tail-correct {(If e₁ e₂ e₃)}{ ρ}{ ρ″}{ s}{ s″}{ B}{ B′}{ c}{ v} (⇓if-false{sρ′ = (s′ , ρ′)} e₁⇓false e₃⇓v) refl =
    let (c₂ , B₁) = explicate-tail e₂ B in
    let (c₃ , B₂) = explicate-tail e₃ B₁ in
    let c₃⇓ = explicate-tail-correct {e₃} e₃⇓v refl in
    explicate-pred-correct {e₁} e₁⇓false (λ ()) (λ _ → c₃⇓) ↝-refl refl

explicate-correct : ∀ (p : IL-Prog) (s : Inputs) (v : Value)
  → interp-ilprog p s v
  → interp-prog (explicate p) s v
explicate-correct (Program n e) s v ((s' , ρ') , e⇓v)
    with explicate-tail e [] in et
... | c , B =
    let c⇓v = explicate-tail-correct e⇓v et in
    let c⇓v′ = eval-blocks (c ∷ [] , refl) c⇓v in
    ((s' , ρ')) , ⇓goto (nth-++-length B [] c) c⇓v′
    

