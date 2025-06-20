module LIf2ExplicateCorrect where

open import Agda.Builtin.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product
open import Data.Integer using (ℤ; _-_; 0ℤ)
open import Data.List
open import Data.List.Properties
open import Data.Maybe
open import Data.Bool hiding (Bool)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Reader
open import Utilities
open import LIf2

--------------- Proof of correctness for Explicate Control -------------------

_↝_ : CFG → CFG → Set
G₁ ↝ G₂ = ∃[ G ] G₁ ++ G ≡ G₂

↝-refl : ∀ {G : CFG}
  → G ↝ G
↝-refl {G} = [] , (++-identityʳ G)

↝-trans : ∀ {G₁ G₂ G₃ : CFG}
  → G₁ ↝ G₂  → G₂ ↝ G₃
  → G₁ ↝ G₃
↝-trans {G₁}{G₂}{G₃} (G , eq12) (G' , eq23)
  rewrite sym eq12 | sym eq23  | ++-assoc G₁ G G'
  = G ++ G' , refl

↝-add-node : (t : CStmt) (G G' : CFG) (lbl : ℕ)
  → add-node t G ≡ (lbl , G')
  → G ↝ G'
↝-add-node t G G' lbl refl = [ t ] , refl

nth-add-node : ∀ {G : CFG}{c : CStmt}
  → nth (proj₂ (add-node c G)) (proj₁ (add-node c G)) ≡ just c
nth-add-node {G}{c}
  rewrite nth-++-length G [] c = refl

nth-CFG : ∀ {G₁ G₂ : CFG} {l : ℕ} {t : CStmt}
  → G₁ ↝ G₂
  → nth G₁ l ≡ just t
  → nth G₂ l ≡ just t
nth-CFG {G₁}{l = l}{t} (G , refl) n1 = nth-++-just G₁ G l t n1

explicate-assign-CFG : ∀ {x : Id}{m : Imp-Exp} {t t' : CStmt} {G₁ G₂ : CFG} → explicate-assign x m t G₁ ≡ (t' , G₂) → G₁ ↝ G₂
explicate-pred-CFG : ∀ {m : Imp-Exp}{t₁ t₂ t : CStmt}{G₁ G₂ : CFG} → explicate-pred m t₁ t₂ G₁ ≡ (t , G₂) → G₁ ↝ G₂
explicate-tail-CFG : ∀ {m : Imp-Exp} {G₁ G₂ : CFG}{t : CStmt} → explicate-tail m G₁ ≡ (t , G₂) → G₁ ↝ G₂

explicate-pred-CFG {Atom (Num x)} {c-thn} {c-els} {c} {B₁} {B₂} refl = ↝-refl
explicate-pred-CFG {Atom (Bool false)} {c-thn} {c-els} {c} {B₁} {B₂} refl = ↝-refl
explicate-pred-CFG {Atom (Bool true)} {c-thn} {c-els} {c} {B₁} {B₂} refl = ↝-refl
explicate-pred-CFG {Atom (Var x)} {c-thn} {c-els} {c} {B₁} {B₂} refl =
    let (l-thn , B′) = add-node c-thn B₁ in
    let (l-els , _) = add-node c-els B′ in 
    let B₁↝B′ = ↝-add-node c-thn B₁ B′ l-thn refl in
    let B′↝B₂ = ↝-add-node c-els B′ B₂ l-els refl in
    ↝-trans B₁↝B′ B′↝B₂
explicate-pred-CFG {Read} {c-thn} {c-els} {c} {B₁} {B₂} refl = ↝-refl
explicate-pred-CFG {Sub a₁ a₂} {c-thn} {c-els} {c} {B₁} {B₂} refl = ↝-refl
explicate-pred-CFG {Eq a₁ a₂} {c-thn} {c-els} {c} {B₁} {B₂} refl =
    let (l-thn , B′) = add-node c-thn B₁ in
    let (l-els , _) = add-node c-els B′ in 
    let B₁↝B′ = ↝-add-node c-thn B₁ B′ l-thn refl in
    let B′↝B₂ = ↝-add-node c-els B′ B₂ l-els refl in
    ↝-trans B₁↝B′ B′↝B₂
explicate-pred-CFG {Assign x e₁ e₂} {c-thn} {c-els} {c} {B₁} {B₂} refl = 
    let (c₂ , B′) = explicate-pred e₂ c-thn c-els B₁ in
    let (c₁ , _) = explicate-assign x e₁ c₂ B′ in
    let B₁↝B′ = explicate-pred-CFG {e₂}{c-thn}{c-els}{c₂}{B₁}{B′} refl in
    let B′↝B₂ = explicate-assign-CFG {x}{e₁}{c₂}{c₁}{B′}{B₂} refl in
    ↝-trans B₁↝B′ B′↝B₂
explicate-pred-CFG {If e₁ e₂ e₃} {thn} {els} {c} {B₁} {B₂} refl =
    let (lbl-thn , B′) = add-node thn B₁ in 
    let (lbl-els , B″) = add-node els B′ in 
    let (c₂ , B‴) = explicate-pred e₂ (Goto lbl-thn) (Goto lbl-els) B″ in 
    let (c₃ , B⁗) = explicate-pred e₃ (Goto lbl-thn) (Goto lbl-els) B‴ in 
    let B₁↝B′ = ↝-add-node thn B₁ B′ lbl-thn refl in
    let B′↝B″ = ↝-add-node els B′ B″ lbl-els refl in
    let B″↝B‴ = explicate-pred-CFG {e₂}{Goto lbl-thn}{Goto lbl-els}{c₂}{B″}{B‴} refl in
    let B‴↝B⁗ = explicate-pred-CFG {e₃}{Goto lbl-thn}{Goto lbl-els}{c₃}{B‴}{B⁗} refl in
    let B⁗↝B₂ = explicate-pred-CFG {e₁}{c₂}{c₃}{c}{B⁗}{B₂} refl in
    ↝-trans B₁↝B′ (↝-trans B′↝B″ (↝-trans B″↝B‴ (↝-trans B‴↝B⁗ B⁗↝B₂)))

explicate-tail-CFG {Atom a} {B₁} {B₂} {t} refl = ↝-refl
explicate-tail-CFG {Read} {B₁} {B₂} {t} refl = ↝-refl
explicate-tail-CFG {Sub a₁ a₂} {B₁} {B₂} {t} refl = ↝-refl
explicate-tail-CFG {Eq a₁ a₂} {B₁} {B₂} {t} refl = ↝-refl
explicate-tail-CFG {Assign x e₁ e₂} {B₁} {B₂} {t} et
    with explicate-tail e₂ B₁ in et2 | et
... | c₂ , B′ | refl =
    let B₁↝B′ = explicate-tail-CFG {e₂} et2 in
    let B′↝B₂ = explicate-assign-CFG {x}{e₁} refl in
    ↝-trans B₁↝B′ B′↝B₂
explicate-tail-CFG {If e₁ e₂ e₃} {B₁} {B₂} {t} et
    with explicate-tail e₂ B₁ in et2 | et
... | c₂ , B′ | et′
    with explicate-tail e₃ B′ in et3 | et′
... | c₃ , B″ | et″
    with explicate-pred e₁ c₂ c₃ B″ in ep1 | et″ 
... | t , B₂ | refl =
    let B₁↝B′ = explicate-tail-CFG {e₂}{B₁}{B′} et2 in
    let B′↝B″ = explicate-tail-CFG {e₃}{B′}{B″} et3 in
    let B″↝B₂ = explicate-pred-CFG {e₁}{c₂}{c₃}{t}{B″}{B₂} ep1 in
    ↝-trans B₁↝B′ (↝-trans B′↝B″ B″↝B₂)

explicate-assign-CFG {x} {Atom a} {t} {t'} {B₁} {B₂} refl = ↝-refl
explicate-assign-CFG {x} {Read} {t} {t'} {B₁} {B₂} refl = ↝-refl
explicate-assign-CFG {x} {Sub a₁ a₂} {t} {t'} {B₁} {B₂} refl = ↝-refl
explicate-assign-CFG {x} {Eq a₁ a₂} {t} {t'} {B₁} {B₂} refl = ↝-refl
explicate-assign-CFG {x} {Assign y e₁ e₂} {t} {t'} {B₁} {B₂} refl =
    let (t₂ , B′) = explicate-assign x e₂ t B₁ in 
    let B₁↝B′ = explicate-assign-CFG {x}{e₂}{t}{t₂}{B₁}{B′} refl in
    let B′↝B₂ = explicate-assign-CFG {y}{e₁}{t₂}{t'}{B′}{B₂} refl in
    ↝-trans B₁↝B′ B′↝B₂ 
explicate-assign-CFG {x} {If e₁ e₂ e₃} {t} {t'} {B₁} {B₂} refl =
    let (cont , B) = add-node t B₁ in
    let (t₂ , B') = explicate-assign x e₂ (Goto cont) B in 
    let (t₃ , B'') = explicate-assign x e₃ (Goto cont) B' in 
    let B₁↝B = ↝-add-node t B₁ B cont refl in
    let B↝B' = explicate-assign-CFG {x}{e₂}{Goto cont}{t₂}{B}{B'} refl in
    let B'↝B'' = explicate-assign-CFG {x}{e₃}{Goto cont}{t₃}{B'}{B''} refl in
    let B''↝B₂ = explicate-pred-CFG {e₁}{t₂}{t₃}{t'}{B''}{B₂} refl in
    ↝-trans B₁↝B (↝-trans B↝B' (↝-trans B'↝B'' B''↝B₂))

eval-CFG : ∀ {t : CStmt}{ ρ ρ′ : Env Value}{B₁ B₂ : CFG}{s s′ : Inputs}{v : Value} → B₁ ↝ B₂ → (s , ρ) , B₁ ⊢ᶜ t ⇓ v ⊣ (s′ , ρ′) → (s , ρ) , B₂ ⊢ᶜ t ⇓ v ⊣ (s′ , ρ′)
eval-CFG {Return e} {ρ} {ρ′} {B₁} {B₂} {s} {s′} {v} B₁↝B₂ (⇓return eq) = ⇓return eq
eval-CFG {Assign x e t} {ρ} {ρ′} {B₁} {B₂} {s} {s′} {v} B₁↝B₂ (⇓assign ie t⇓v) = ⇓assign ie (eval-CFG B₁↝B₂ t⇓v)
eval-CFG {IfEq a₁ a₂ thn els} {ρ} {ρ′} {B₁} {B₂} {s} {s′} {v} B₁↝B₂ (⇓if-true ia₁ ia₂ eq nth t⇓v) =
  ⇓if-true ia₁ ia₂ eq (nth-CFG B₁↝B₂ nth) (eval-CFG B₁↝B₂ t⇓v)
eval-CFG {IfEq a₁ a₂ thn els} {ρ} {ρ′} {B₁} {B₂} {s} {s′} {v} B₁↝B₂ (⇓if-false ia₁ ia₂ eq nth t⇓v) =
  ⇓if-false ia₁ ia₂ eq (nth-CFG B₁↝B₂ nth) (eval-CFG B₁↝B₂ t⇓v)
eval-CFG {Goto l} {ρ} {ρ′} {B₁} {B₂} {s} {s′} {v} B₁↝B₂ (⇓goto nth t⇓v) =
  ⇓goto (nth-CFG B₁↝B₂ nth) (eval-CFG B₁↝B₂ t⇓v)

sub-not-bool : ∀ {n₁ n₂ : Value}{b : 𝔹}
  → sub n₁ n₂ ≡ just (Bool b)
  → ⊥
sub-not-bool {Int x}{Int x₁} ()
sub-not-bool {Int x}{Bool x₁} ()

explicate-assign-correct : ∀{x : Id}{e : Imp-Exp}{t : CStmt}{ρ ρ′ ρ″ : Env Value}{s s′ s″ : Inputs}{B B′ : List CStmt}{c : CStmt}
    {n v : Value}
  → (s , ρ) ⊢ e ⇓ n ⊣ (s′ , ρ′)
  → (s′ , update ρ′ x n) , B ⊢ᶜ t ⇓ v ⊣ (s″ , ρ″)
  → explicate-assign x e t B ≡ (c , B′)
  → (s , ρ) , B′ ⊢ᶜ c ⇓ v ⊣ (s″ , ρ″)

explicate-pred-correct : ∀ {e₁ : Imp-Exp} {c₁ c₂ c₃ : CStmt} {b : 𝔹} {v : Value} {s s′ s″ : Inputs} {ρ ρ′ ρ″ : Env Value} {B B′ : CFG}
  → (s , ρ) ⊢ e₁ ⇓ Bool b ⊣ (s′ , ρ′)
  → ((s′ , ρ′) , B ⊢ᶜ (if b then c₂ else c₃) ⇓ v ⊣ (s″ , ρ″))
  → explicate-pred e₁ c₂ c₃ B ≡ (c₁ , B′)
  → (s , ρ) , B′ ⊢ᶜ c₁ ⇓ v ⊣ (s″ , ρ″)
explicate-pred-correct {Atom (Bool false)} {c₁} {c₂} {c₃} {false} {v} {s} {s′} {s″} {ρ} {ρ′} {ρ″} {B″} {B‴} (⇓atom ia) c₂orc₃⇓v refl =
    c₂orc₃⇓v
explicate-pred-correct {Atom (Var x)} {c₁} {c₂} {c₃} {false} {v} {s} {s′} {s″} {ρ} {ρ′} {ρ″} {B″} {B‴} (⇓atom ia) c₂orc₃⇓v refl =
    let B₂ = B″ ++ [ c₂ ] in
    let B₃ = B₂ ++ [ c₃ ] in
    let B″↝B₂ : B″ ↝ B₂
        B″↝B₂ = [ c₂ ] , refl in
    let B₂↝B₃ : B₂ ↝ B₃
        B₂↝B₃ = [ c₃ ] , refl in
    let c₃⇓v′ = c₂orc₃⇓v in
    let c₃⇓v″ = eval-CFG B″↝B₂ c₃⇓v′ in
    let c₃⇓v‴ = eval-CFG B₂↝B₃ c₃⇓v″ in
    let nth2 : nth B₃ (length B₂) ≡ just c₃
        nth2 = nth-++-length B₂ [] c₃ in
    ⇓if-false ia refl refl nth2 c₃⇓v‴
explicate-pred-correct {Atom (Bool true)} {c₁} {c₂} {c₃} {true} {v} {s} {s′} {s″} {ρ} {ρ′} {ρ″} {B″} {B‴} (⇓atom ia) c₂orc₃⇓v refl =
    c₂orc₃⇓v
explicate-pred-correct {Atom (Var x)} {c₁} {c₂} {c₃} {true} {v} {s} {s′} {s″} {ρ} {ρ′} {ρ″} {B″} {B‴} (⇓atom ia) c₂orc₃⇓v refl =
    let B₂ = B″ ++ [ c₂ ] in
    let B₃ = B₂ ++ [ c₃ ] in
    let B″↝B₂ : B″ ↝ B₂
        B″↝B₂ = [ c₂ ] , refl in
    let B₂↝B₃ : B₂ ↝ B₃
        B₂↝B₃ = [ c₃ ] , refl in
    let c₂⇓v′ = c₂orc₃⇓v in
    let c₂⇓v″ = eval-CFG B″↝B₂ c₂⇓v′ in
    let c₂⇓v‴ = eval-CFG B₂↝B₃ c₂⇓v″ in
    let nth2 : nth B₂ (length B″) ≡ just c₂
        nth2 = nth-++-length B″ [] c₂ in
    let nth3 : nth B₃ (length B″) ≡ just c₂
        nth3 = nth-CFG B₂↝B₃ nth2 in
    ⇓if-true ia refl refl nth3 c₂⇓v‴
explicate-pred-correct {Sub a₁ a₂} {c₁} {c₂} {c₃} {b} {v} {s} {s′} {s″} {ρ} {ρ′} {ρ″} {B″} {B‴} (⇓sub x x₁ subv) c₂orc₃⇓v refl
    with sub-not-bool subv
... | ()
explicate-pred-correct {Eq a₁ a₂} {c₁} {c₂} {c₃} {true} {v} {s} {s′} {s″} {ρ} {ρ′} {ρ″} {B″} {B‴} (⇓eq ia1 ia2 eq) c₂orc₃⇓v refl =
    let B₂ = B″ ++ [ c₂ ] in
    let B₃ = B₂ ++ [ c₃ ] in
    let B″↝B₂ : B″ ↝ B₂
        B″↝B₂ = [ c₂ ] , refl in
    let B₂↝B₃ : B₂ ↝ B₃
        B₂↝B₃ = [ c₃ ] , refl in
    let c₂⇓v′ = c₂orc₃⇓v in
    let c₂⇓v″ = eval-CFG B″↝B₂ c₂⇓v′ in
    let c₂⇓v‴ = eval-CFG B₂↝B₃ c₂⇓v″ in
    let nth2 : nth B₂ (length B″) ≡ just c₂
        nth2 = nth-++-length B″ [] c₂ in
    let nth3 : nth B₃ (length B″) ≡ just c₂
        nth3 = nth-CFG B₂↝B₃ nth2 in
   ⇓if-true ia1 ia2 eq nth3 c₂⇓v‴
explicate-pred-correct {Eq a₁ a₂} {c₁} {c₂} {c₃} {false} {v} {s} {s′} {s″} {ρ} {ρ′} {ρ″} {B″} {B‴} (⇓eq ia1 ia2 eq) c₂orc₃⇓v refl =
    let B₂ = B″ ++ [ c₂ ] in
    let B₃ = B₂ ++ [ c₃ ] in
    let B″↝B₂ : B″ ↝ B₂
        B″↝B₂ = [ c₂ ] , refl in
    let B₂↝B₃ : B₂ ↝ B₃
        B₂↝B₃ = [ c₃ ] , refl in
    let B″↝B₃ : B″ ↝ B₃
        B″↝B₃ = ↝-trans B″↝B₂ B₂↝B₃ in
    let B′⊢c₃⇓v = c₂orc₃⇓v in
    let B₃⊢c₃⇓v = eval-CFG B″↝B₃ B′⊢c₃⇓v in
   ⇓if-false ia1 ia2 eq (nth-add-node{B₂}) B₃⊢c₃⇓v

explicate-pred-correct {Assign x e₁ e₂} {c} {c-thn} {c-els} {b} {v} {s} {s′} {s″} {ρ} {ρ′} {ρ″} {B″} {B‴} (⇓assign{s′ = s₁}{ρ₁}{n₁ = n₁}{n₂} e₁⇓ e₂⇓) c-thnorc-els⇓v refl =
    let (c₂ , B₂) = explicate-pred e₂ c-thn c-els B″ in
    let c₂⇓v : (s₁ , update ρ₁ x n₁) , B₂ ⊢ᶜ c₂ ⇓ v ⊣ (s″ , ρ″)
        c₂⇓v = explicate-pred-correct{c₁ = c₂}{B′ = B₂} e₂⇓ c-thnorc-els⇓v refl in
    explicate-assign-correct e₁⇓ c₂⇓v refl

explicate-pred-correct {If e₁ e₂ e₃} {c} {c-thn} {c-els} {b} {v} {s} {s′} {s″} {ρ} {ρ′} {ρ″} {B″} {B‴} (⇓if-true e₁⇓true e₂⇓b) c-thnorc-els⇓v refl =
    let IH2 = explicate-pred-correct {e₂} e₂⇓b (Goal b c-thnorc-els⇓v) refl in
    explicate-pred-correct {e₁}{c₁}{c₂}{c₃}{true} e₁⇓true (eval-CFG B₃↝B₄ IH2) refl
    where
    B₁ = B″ ++ [ c-thn ]
    lbl-thn = length B″
    B₂ = B₁ ++ [ c-els ]
    lbl-els = length B₁

    ep2 = explicate-pred e₂ (Goto lbl-thn) (Goto lbl-els) B₂
    c₂ = proj₁ ep2
    B₃ = proj₂ ep2
    ep3 = explicate-pred e₃ (Goto lbl-thn) (Goto lbl-els) B₃
    c₃ = proj₁ ep3
    B₄ = proj₂ ep3
    ep1 = explicate-pred e₁ c₂ c₃ B₄
    c₁ = proj₁ ep1

    B₁↝B₂ : B₁ ↝ B₂
    B₁↝B₂ = [ c-els ] , refl 
    B″↝B₂ : B″ ↝ B₂
    B″↝B₂ = ↝-trans ([ c-thn ] , refl) B₁↝B₂
    B₃↝B₄ : B₃ ↝ B₄
    B₃↝B₄ = explicate-pred-CFG {e₃}{Goto lbl-thn}{Goto lbl-els} refl

    Goal : ∀ b
        → (s′ , ρ′) , B″ ⊢ᶜ if b then c-thn else c-els ⇓ v ⊣ (s″ , ρ″)
        → (s′ , ρ′) , B₂ ⊢ᶜ if b then Goto lbl-thn else Goto lbl-els ⇓ v ⊣ (s″ , ρ″)
    Goal false c-thnorc-els⇓v =
        let nth-els : nth B₂ lbl-els ≡ just c-els
            nth-els = nth-add-node{B₁} in
        ⇓goto nth-els (eval-CFG B″↝B₂ c-thnorc-els⇓v)
    Goal true c-thnorc-els⇓v =
        let nth-thn : nth B₁ lbl-thn ≡ just c-thn
            nth-thn = nth-add-node{B″} in
        ⇓goto (nth-CFG B₁↝B₂ nth-thn) (eval-CFG B″↝B₂ c-thnorc-els⇓v)

explicate-pred-correct {If e₁ e₂ e₃} {c} {c-thn} {c-els} {b} {v} {s} {s′} {s″} {ρ} {ρ′} {ρ″} {B″} {B‴} (⇓if-false e₁⇓false e₃⇓b) c-thnorc-els⇓v refl =
    let IH3 = explicate-pred-correct {e₃} e₃⇓b (Goal b c-thnorc-els⇓v) refl in
    explicate-pred-correct {e₁}{c₁}{c₂}{c₃}{false} e₁⇓false IH3 refl
    where
    B₁ = B″ ++ [ c-thn ]
    lbl-thn = length B″
    B₂ = B₁ ++ [ c-els ]
    lbl-els = length B₁

    ep2 = explicate-pred e₂ (Goto lbl-thn) (Goto lbl-els) B₂
    c₂ = proj₁ ep2
    B₃ = proj₂ ep2
    ep3 = explicate-pred e₃ (Goto lbl-thn) (Goto lbl-els) B₃
    c₃ = proj₁ ep3
    B₄ = proj₂ ep3
    ep1 = explicate-pred e₁ c₂ c₃ B₄
    c₁ = proj₁ ep1

    B″↝B₁ : B″ ↝ B₁
    B″↝B₁ = [ c-thn ] , refl 
    B₁↝B₂ : B₁ ↝ B₂
    B₁↝B₂ = [ c-els ] , refl
    B₂↝B₃ = (explicate-pred-CFG {e₂}{Goto lbl-thn}{Goto lbl-els} refl)
    B″↝B₃ : B″ ↝ B₃
    B″↝B₃ = ↝-trans (↝-trans B″↝B₁ B₁↝B₂) B₂↝B₃
    B₁↝B₃ : B₁ ↝ B₃
    B₁↝B₃ = ↝-trans B₁↝B₂ B₂↝B₃
    
    Goal : ∀ b
       → (s′ , ρ′) , B″ ⊢ᶜ if b then c-thn else c-els ⇓ v ⊣ (s″ , ρ″)
       → (s′ , ρ′) , B₃ ⊢ᶜ if b then Goto (add-node c-thn B″ .proj₁) else
                            Goto (add-node c-els (add-node c-thn B″ .proj₂) .proj₁) ⇓ v ⊣ (s″ , ρ″)
    Goal false c-thnorc-els⇓v =
        let nth-els : nth B₂ lbl-els ≡ just c-els
            nth-els = nth-add-node{B₁} in
         ⇓goto (nth-CFG B₂↝B₃ nth-els) (eval-CFG B″↝B₃ c-thnorc-els⇓v)
    Goal true c-thnorc-els⇓v =
        let nth-thn : nth B₁ lbl-thn ≡ just c-thn
            nth-thn = nth-add-node{B″} in
         ⇓goto (nth-CFG B₁↝B₃ nth-thn) (eval-CFG B″↝B₃ c-thnorc-els⇓v)

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
    let t⇓v′ = eval-CFG ([ t ] , refl) t⇓v in
    let IH2 = explicate-assign-correct e₂⇓v₂ (⇓goto (nth-++-length B [] t) t⇓v′) ea2 in
    let B′↝B″ = explicate-assign-CFG {x}{e₃}{Goto (length B)}{c₃} ea3 in
    explicate-pred-correct e₁⇓v₁ (eval-CFG B′↝B″ IH2) ep1

explicate-assign-correct {x}{ (If e₁ e₂ e₃)}{ t}{ ρ}{ ρ′}{ ρ″}{ s}{ s′}{ s″}{ B}{ B‴}{ c}{ n}{ v} (⇓if-false{sρ′ = (s₁ , ρ₁)} e₁⇓v₁ e₃⇓v₃) t⇓v ep1
    with explicate-assign x e₂ (Goto (length B)) (B ++ [ t ]) in ea2
... | c₂ , B′
    with explicate-assign x e₃ (Goto (length B)) B′ in ea3
... | c₃ , B″
    =
    let B₁ = (B ++ t ∷ []) in
    let B↝B₁ : B ↝ B₁
        B↝B₁ = ([ t ] , refl) in
    let B₁↝B′ = explicate-assign-CFG {x}{e₂}{Goto (length B)} ea2 in
    let B↝B′ = ↝-trans B↝B₁ B₁↝B′ in
    let t⇓v′ = eval-CFG B↝B′ t⇓v in
    let nth1 : nth B₁ (length B) ≡ just t
        nth1 = nth-++-length B [] t in
    let nth2 : nth B′ (length B) ≡ just t
        nth2 = nth-CFG B₁↝B′ nth1 in
    let IH3 = explicate-assign-correct e₃⇓v₃ (⇓goto nth2 t⇓v′) ea3 in
    explicate-pred-correct e₁⇓v₁ IH3 ep1

explicate-tail-correct : ∀ {e : Imp-Exp}{ρ ρ' : Env Value}{s s' : Inputs}{B B′ : List CStmt}{c : CStmt}{v : Value}
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
        B₁↝B₂ = explicate-tail-CFG {e₃} refl in
    explicate-pred-correct {e₁} e₁⇓true (eval-CFG B₁↝B₂ c₂⇓) refl
explicate-tail-correct {(If e₁ e₂ e₃)}{ ρ}{ ρ″}{ s}{ s″}{ B}{ B′}{ c}{ v} (⇓if-false{sρ′ = (s′ , ρ′)} e₁⇓false e₃⇓v) refl =
    let (c₂ , B₁) = explicate-tail e₂ B in
    let (c₃ , B₂) = explicate-tail e₃ B₁ in
    let c₃⇓ = explicate-tail-correct {e₃} e₃⇓v refl in
    explicate-pred-correct {e₁} e₁⇓false c₃⇓ refl

explicate-correct : ∀{p}{s}{v}
  → interp-imp p s v
  → interp-prog (explicate p) s v
explicate-correct {Program n e}{s}{v} ((s' , ρ') , e⇓v)
    with explicate-tail e [] in et
... | c , B =
    let c⇓v = explicate-tail-correct e⇓v et in
    let c⇓v′ = eval-CFG (c ∷ [] , refl) c⇓v in
    ((s' , ρ')) , ⇓goto (nth-++-length B [] c) c⇓v′
    

