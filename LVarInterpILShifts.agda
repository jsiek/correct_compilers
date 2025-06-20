module LVarInterpILShifts where

open import Agda.Builtin.Unit
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using ()
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; _≤ᵇ_; _∸_; _+_; s≤s)
open import Data.Nat.Properties
open import Data.Product
open import Data.Sum
open import Data.Integer using (ℤ; -_; _-_; 0ℤ)
open import Data.List
open import Data.List.Properties -- using (++-assoc; length-replicate; ++-identityʳ; length-++)
open import Data.Maybe
open import Relation.Binary.PropositionalEquality
   using (_≡_; refl; trans; sym; cong; cong-app; subst)
open import Agda.Builtin.Bool
open import Relation.Nullary.Negation.Core using (¬_; contradiction)
open import Function.Base using (case_of_; case_returning_of_)

open import Reader
open import Utilities
open import LVar
open import LVarRCOCorrect

--------------- Proof of correctness for Lift Locals -------------------

⇓-store-length : ∀ {e}{s}{ρ}{v}{s′}{ρ′}
  → (s , ρ) ⊢ e ⇓ v ⊣ (s′ , ρ′)
  → length ρ ≡ length ρ′
⇓-store-length {e} {s} {ρ} {v} {s′} {ρ′} (⇓atom ia) = refl
⇓-store-length {e} {s} {ρ} {v} {s′} {ρ′} ⇓read = refl
⇓-store-length {e} {s} {ρ} {v} {s′} {ρ′} (⇓sub ia1 ia2) = refl
⇓-store-length {Assign x e₁ e₂} {s} {ρ} {v} {s′} {ρ′} (⇓assign{ρ′ = ρ′₁}{n₁ = n₁} e₁⇓n₁ e₂⇓v) =
  let IH1 = ⇓-store-length {e₁} e₁⇓n₁ in
  let IH2 = ⇓-store-length {e₂} e₂⇓v in
  let ul = update-length ρ′₁ x n₁ in
  trans IH1 (trans (sym ul) IH2)

interp-shifts-atm : ∀ (a : Atm) (ρ₁ ρ₂ ρ₃ : Env ℤ)
  → interp-atm (shifts-atm a (length ρ₁) (length ρ₂)) (ρ₁ ++ ρ₂ ++ ρ₃)
  ≡ interp-atm a (ρ₁ ++ ρ₃)
interp-shifts-atm (Num x) ρ₁ ρ₂ ρ₃ = refl
interp-shifts-atm (Var x) ρ₁ ρ₂ ρ₃ = nth-++-shifts-var ρ₁ ρ₂ ρ₃ x

⇓atom-elim : ∀{s s′ ρ ρ′ a v}
   → (s , ρ) ⊢ Atom a ⇓ v ⊣ (s′ , ρ′)
   → interp-atm a ρ ≡ just v × s ≡ s′ × ρ ≡ ρ′
⇓atom-elim (⇓atom eq) = eq , (refl , refl)

⇓read-elim : ∀{i f i' f' ρ ρ′ v}
   → ((i , f) , ρ) ⊢ Read ⇓ v ⊣ ((i' , f') , ρ′)
   → i' ≡ suc i × f' ≡ f × v ≡ f i × ρ′ ≡ ρ
⇓read-elim ⇓read = refl , refl , refl , refl

⇓sub-elim : ∀{s s' ρ ρ' a₁ a₂ v}
   → (s , ρ) ⊢ Sub a₁ a₂ ⇓ v ⊣ (s' , ρ')
   → Σ[ n₁ ∈ ℤ ] Σ[ n₂ ∈ ℤ ] interp-atm a₁ ρ ≡ just n₁ × interp-atm a₂ ρ ≡ just n₂
       × v ≡ n₁ - n₂ × s ≡ s' × ρ ≡ ρ'
⇓sub-elim (⇓sub{n₁ = n₁}{n₂} eq1 eq2) = n₁ , n₂ , eq1 , eq2 , refl , refl , refl

⇓shifts : ∀ {e : IL-Exp}{v : ℤ} {s s′ : Inputs} {ρ₁ ρ′₁ ρ₂ ρ₃ ρ′₃ : Env ℤ} 
  → (s , ρ₁ ++ ρ₃) ⊢ e ⇓ v ⊣ (s′ , ρ′₁ ++ ρ′₃)
  → length ρ′₁ ≡ length ρ₁
  → (s , ρ₁ ++ ρ₂ ++ ρ₃) ⊢
      shifts-imp-exp e (length ρ₁) (length ρ₂) ⇓ v ⊣ (s′ , ρ′₁ ++ ρ₂ ++ ρ′₃)
⇓shifts {Atom a} {v} {s} {s′}{ρ₁}{ρ′₁}{ρ₂}{ρ₃}{ρ′₃} e⇓v lρ1
    with ⇓atom-elim e⇓v
... | ia , refl , eq2 
    with length≡++{ℤ}{ρ₁}{ρ′₁}{ρ₃}{ρ′₃} (sym lρ1) eq2
... | refl , refl
    =
    ⇓atom Subgoal
    where
    Subgoal : interp-atm (shifts-atm a (length ρ₁) (length ρ₂)) (ρ₁ ++ ρ₂ ++ ρ₃) ≡ just v
    Subgoal rewrite interp-shifts-atm a ρ₁ ρ₂ ρ₃ = ia

⇓shifts {Read} {v} {i , f} {i' , f'}{ρ₁}{ρ′₁}{ρ₂}{ρ₃}{ρ′₃} e⇓v lρ1
    with ⇓read-elim e⇓v
... | refl , refl , refl , eq4
    with length≡++{ℤ}{ρ₁}{ρ′₁}{ρ₃}{ρ′₃} (sym lρ1) (sym eq4)
... | refl , refl
    = ⇓read

⇓shifts {Sub a₁ a₂} {v} {s} {s′} {ρ₁}{ρ′₁}{ρ₂}{ρ₃}{ρ′₃} e⇓v lρ1
    with ⇓sub-elim e⇓v
... | n₁ , n₂ , ia₁ , ia₂ , refl , refl , r=
    with length≡++{ℤ}{ρ₁}{ρ′₁}{ρ₃}{ρ′₃} (sym lρ1) r=
... | refl , refl
    = ⇓sub is1 is2
    where
    is1 : interp-atm (shifts-atm a₁ (length ρ₁) (length ρ₂)) (ρ₁ ++ ρ₂ ++ ρ₃) ≡ just n₁
    is1 rewrite interp-shifts-atm a₁ ρ₁ ρ₂ ρ₃ = ia₁

    is2 : interp-atm (shifts-atm a₂ (length ρ₁) (length ρ₂)) (ρ₁ ++ ρ₂ ++ ρ₃) ≡ just n₂
    is2 rewrite interp-shifts-atm a₂ ρ₁ ρ₂ ρ₃ = ia₂

⇓shifts {Assign x e₁ e₂} {v₂} {s} {s′} {ρ₁}{ρ′₁}{ρ₂}{ρ₃}{ρ′₃}
        (⇓assign {ρ′ = ρ′}{n₁ = n₁} e₁⇓n₁ e₂⇓v₂) lρ1
    with ⇓-store-length e₁⇓n₁
... | r13=r′
    rewrite length-++ ρ₁ {ρ₃}
    with ++-length ρ′ (length ρ₁) (length ρ₃) (sym r13=r′)
... | ρ″₁ , ρ″₃ , refl , lρ″₁ , lρ″₃
    with ⇓shifts {e₁}{n₁}{s}{_}{ρ₁}{ρ″₁}{ρ₂}{ρ₃}{ρ″₃} e₁⇓n₁ lρ″₁
... | se1⇓n1
    with length ρ₁ ≤ᵇ x in r1x
... | true
    with m≤n⇒-+ (length ρ₁) x (≤ᵇ⇒≤ (length ρ₁) x (eq-true-top r1x))
... | i , refl
    rewrite sym lρ1 | sym lρ″₁ | update-++-+ ρ″₁ ρ″₃ i n₁
    with ⇓shifts {e₂}{v₂}{_}{s′}{ρ″₁}{ρ′₁}{ρ₂}{update ρ″₃ i n₁}{ρ′₃} e₂⇓v₂ (sym lρ″₁)
... | se2⇓v₂ =     
    ⇓assign se1⇓n1 Goal
    where
    EQ : update (ρ″₁ ++ ρ₂ ++ ρ″₃) (length ρ″₁ + length ρ₂ + i) n₁
         ≡ ρ″₁ ++ ρ₂ ++ (update ρ″₃ i n₁)
    EQ  rewrite sym (++-assoc ρ″₁ ρ₂ ρ″₃)
        | sym (length-++ ρ″₁ {ρ₂})
        | update-++-+ (ρ″₁ ++ ρ₂) ρ″₃ i n₁
        | ++-assoc ρ″₁ ρ₂ (update ρ″₃ i n₁)
        = refl
       
    Goal : (_ , update (ρ″₁ ++ ρ₂ ++ ρ″₃) (length ρ₂ + (length ρ″₁ + i)) n₁)
      ⊢ shifts-imp-exp e₂ (length ρ″₁) (length ρ₂)
      ⇓ v₂ ⊣ (s′ , ρ′₁ ++ ρ₂ ++ ρ′₃)
    Goal
        rewrite sym (+-assoc (length ρ₂) (length ρ″₁) i)
        | +-comm (length ρ₂) (length ρ″₁)
        | EQ
        = se2⇓v₂
    
⇓shifts {Assign x e₁ e₂} {v₂} {s} {s′} {ρ₁}{ρ′₁}{ρ₂}{ρ₃}{ρ′₃}
        (⇓assign {ρ′ = ρ′}{n₁ = n₁} e₁⇓n₁ e₂⇓v₂) lρ1
    | r13=r′ | ρ″₁ , ρ″₃ , refl , lρ″₁ , lρ″₃ | se1⇓n1
    | false
    rewrite update-++-< ρ″₁ ρ″₃ x n₁ (≰⇒> λ ρ″₁≤x → (eq-false-not-top r1x)
                                                                 (≤⇒≤ᵇ (subst (λ X → X ≤ x)
                                                                        lρ″₁ ρ″₁≤x)))
    with ⇓shifts {e₂}{v₂}{_}{s′}{update ρ″₁ x n₁}{ρ′₁}{ρ₂}{ρ″₃}{ρ′₃} e₂⇓v₂ (sym (trans (update-length ρ″₁ x n₁) (trans lρ″₁ (sym lρ1)) ))
... | se2⇓v₂
    rewrite sym (update-++-< ρ″₁ (ρ₂ ++ ρ″₃) x n₁ ((≰⇒> λ ρ″₁≤x → (eq-false-not-top r1x)
                                                                 (≤⇒≤ᵇ (subst (λ X → X ≤ x)
                                                                        lρ″₁ ρ″₁≤x)))))
    | update-length ρ″₁ x n₁ | lρ″₁
    =
      ⇓assign se1⇓n1 se2⇓v₂

    
