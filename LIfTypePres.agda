module LIfTypePres where

open import Agda.Builtin.Unit
open import Data.Empty using (⊥; ⊥-elim)
import Data.Bool
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; _≤ᵇ_; _∸_; _+_; s≤s)
open import Data.Nat.Properties
open import Data.Product
open import Data.Sum
open import Data.Integer using (ℤ; -_; _-_; 0ℤ)
open import Data.List
open import Data.List.Properties using (++-assoc; length-replicate; ++-identityʳ)
open import Data.Maybe
open import Relation.Binary.PropositionalEquality
   using (_≡_; refl; trans; sym; cong; cong-app)
open import Agda.Builtin.Bool renaming (Bool to 𝔹)
open import Relation.Nullary.Negation.Core using (¬_; contradiction)
open import Function.Base using (case_of_; case_returning_of_)

open import Reader
open import Utilities
open import LIf

TypeEnv : Set
TypeEnv = List Type

wt-uniop : UniOp → Type → Maybe Type
wt-uniop Neg IntT = just IntT
wt-uniop Neg BoolT = nothing
wt-uniop Not IntT = nothing
wt-uniop NOt BoolT = just BoolT

wt-binop : BinOp → Type → Type → Maybe Type
wt-binop Sub IntT IntT = just IntT
wt-binop Sub IntT BoolT = nothing
wt-binop Sub BoolT t2 = nothing
wt-binop Eq IntT IntT = just BoolT
wt-binop Eq IntT BoolT = nothing
wt-binop Eq BoolT IntT = nothing
wt-binop Eq BoolT BoolT = just BoolT
wt-binop LessEq IntT IntT = just BoolT
wt-binop LessEq IntT BoolT = nothing
wt-binop LessEq BoolT t2 = nothing
wt-binop And IntT t2 = nothing
wt-binop And BoolT IntT = nothing
wt-binop And BoolT BoolT = just BoolT

--- Type System for LIf

infix 4 _⊢_⦂_
data _⊢_⦂_ : TypeEnv → Exp → Type → Set where
  wt-num : ∀ {Γ n} → Γ ⊢ Num n ⦂ IntT
  wt-bool : ∀ {Γ b} → Γ ⊢ Bool b ⦂ BoolT
  wt-read : ∀ {Γ} → Γ ⊢ Read ⦂ IntT
  wt-uni : ∀ {Γ op e T₁ T}
    → Γ ⊢ e ⦂ T₁
    → wt-uniop op T₁ ≡ just T
    → Γ ⊢ Uni op e ⦂ T
  wt-bin : ∀ {Γ op e₁ e₂ T₁ T₂ T}
    → Γ ⊢ e₁ ⦂ T₁
    → Γ ⊢ e₂ ⦂ T₂
    → wt-binop op T₁ T₂ ≡ just T
    → Γ ⊢ Bin op e₁ e₂ ⦂ T
  wt-var : ∀ {Γ x T}
    → nth Γ x ≡ just T
    → Γ ⊢ Var x ⦂ T
  wt-let : ∀ {Γ e₁ e₂ T₁ T}
    → Γ ⊢ e₁ ⦂ T₁
    → T₁ ∷ Γ ⊢ e₂ ⦂ T
    → Γ ⊢ Let e₁ e₂ ⦂ T
  wt-if : ∀ {Γ e₁ e₂ e₃ T}
    → Γ ⊢ e₁ ⦂ BoolT
    → Γ ⊢ e₂ ⦂ T
    → Γ ⊢ e₃ ⦂ T
    → Γ ⊢ If e₁ e₂ e₃ ⦂ T

--- Type System for LMonIf

infix 4 _⊢ᵃ_⦂_
data _⊢ᵃ_⦂_ : TypeEnv → Atm → Type → Set where
  wt-num : ∀ {Γ n} → Γ ⊢ᵃ Num n ⦂ IntT
  wt-bool : ∀ {Γ b} → Γ ⊢ᵃ Bool b ⦂ BoolT
  wt-var : ∀ {Γ x T}
    → nth Γ x ≡ just T
    → Γ ⊢ᵃ Var x ⦂ T
  
infix 4 _⊢ᵐ_⦂_
data _⊢ᵐ_⦂_ : TypeEnv → Mon → Type → Set where
  wt-atom : ∀ {Γ a T}
    → Γ ⊢ᵃ a ⦂ T
    → Γ ⊢ᵐ Atom a ⦂ T
  wt-read : ∀ {Γ} → Γ ⊢ᵐ Read ⦂ IntT
  wt-uni : ∀ {Γ op a T₁ T}
    → Γ ⊢ᵃ a ⦂ T₁
    → wt-uniop op T₁ ≡ just T
    → Γ ⊢ᵐ Uni op a ⦂ T
  wt-bin : ∀ {Γ op a₁ a₂ T₁ T₂ T}
    → Γ ⊢ᵃ a₁ ⦂ T₁
    → Γ ⊢ᵃ a₂ ⦂ T₂
    → wt-binop op T₁ T₂ ≡ just T
    → Γ ⊢ᵐ Bin op a₁ a₂ ⦂ T
  wt-let : ∀ {Γ e₁ e₂ T₁ T}
    → Γ ⊢ᵐ e₁ ⦂ T₁
    → T₁ ∷ Γ ⊢ᵐ e₂ ⦂ T
    → Γ ⊢ᵐ Let e₁ e₂ ⦂ T
  wt-if : ∀ {Γ e₁ e₂ e₃ T}
    → Γ ⊢ᵐ e₁ ⦂ BoolT
    → Γ ⊢ᵐ e₂ ⦂ T
    → Γ ⊢ᵐ e₃ ⦂ T
    → Γ ⊢ᵐ If e₁ e₂ e₃ ⦂ T
    
--- Type System for CIf

infix 4 _⊢ᵉ_⦂_
data _⊢ᵉ_⦂_ : TypeEnv → CExp → Type → Set where
  wt-atom : ∀ {Γ a T}
    → Γ ⊢ᵃ a ⦂ T
    → Γ ⊢ᵉ Atom a ⦂ T
  wt-read : ∀ {Γ} → Γ ⊢ᵉ Read ⦂ IntT
  wt-uni : ∀ {Γ op a T₁ T}
    → Γ ⊢ᵃ a ⦂ T₁
    → wt-uniop op T₁ ≡ just T
    → Γ ⊢ᵉ Uni op a ⦂ T
  wt-bin : ∀ {Γ op a₁ a₂ T₁ T₂ T}
    → Γ ⊢ᵃ a₁ ⦂ T₁
    → Γ ⊢ᵃ a₂ ⦂ T₂
    → wt-binop op T₁ T₂ ≡ just T
    → Γ ⊢ᵉ Bin op a₁ a₂ ⦂ T

infix 4 _⊢ᵗ_
data _⊢ᵗ_ : TypeEnv → CTail → Set where
  wt-return : ∀ {Γ e }
    → Γ ⊢ᵉ e ⦂ IntT
    → Γ ⊢ᵗ Return e
  wt-assign : ∀ {Γ x e t T₁}
    → nth Γ x ≡ just T₁ 
    → Γ ⊢ᵉ e ⦂ T₁
    → (T₁ ∷ Γ) ⊢ᵗ t
    → Γ ⊢ᵗ Assign x e t
  wt-if : ∀ {Γ op a₁ a₂ thn els T₁ T₂}
    → Γ ⊢ᵃ a₁ ⦂ T₁
    → Γ ⊢ᵃ a₂ ⦂ T₂
    → wt-binop op T₁ T₂ ≡ just BoolT
    → Γ ⊢ᵗ If op a₁ a₂ thn els

wt-blocks : TypeEnv → Blocks → Set
wt-blocks Γ [] = ⊤
wt-blocks Γ (b ∷ bs) = Γ ⊢ᵗ b × wt-blocks Γ bs

-- wt-prog : CProgram → Set
-- wt-prog (Γ , bs) = wt-blocks Γ bs


--------------- Shift Preserves Types -------------------

well-typed-shift-atm : ∀ (a : Atm) (Γ₁ Γ₂ : TypeEnv) (T₁ T : Type)
  → Γ₁ ++ Γ₂ ⊢ᵃ a ⦂ T
  → Γ₁ ++ T₁ ∷ Γ₂ ⊢ᵃ shift-atm a (length Γ₁) ⦂ T
well-typed-shift-atm (Num n) Γ₁ Γ₂ T₁ T wt-num = wt-num
well-typed-shift-atm (Bool b) Γ₁ Γ₂ T₁ T wt-bool = wt-bool
well-typed-shift-atm (Var x) Γ₁ Γ₂ T₁ T (wt-var nth) 
  rewrite sym (nth-++-shift-var Γ₁ Γ₂ T₁ x)
  = wt-var nth

well-typed-shift-mon : ∀ (m : Mon) (Γ₁ Γ₂ : TypeEnv) (T₁ T : Type)
  → Γ₁ ++ Γ₂ ⊢ᵐ m ⦂ T
  → Γ₁ ++ T₁ ∷ Γ₂ ⊢ᵐ shift-mon m (length Γ₁) ⦂ T
well-typed-shift-mon (Atom a) Γ₁ Γ₂ T₁ T (wt-atom wt-a) =
  wt-atom (well-typed-shift-atm a Γ₁ Γ₂ T₁ T wt-a)
well-typed-shift-mon Read Γ₁ Γ₂ T₁ T wt-read = wt-read
well-typed-shift-mon (Uni op a) Γ₁ Γ₂ T₁ T (wt-uni wt-a wt-op) =
  wt-uni (well-typed-shift-atm a Γ₁ Γ₂ T₁ _ wt-a) wt-op
well-typed-shift-mon (Bin op a₁ a₂) Γ₁ Γ₂ T₁ T (wt-bin wt-a₁ wt-a₂ wt-op) =
  wt-bin (well-typed-shift-atm a₁ Γ₁ Γ₂ T₁ _ wt-a₁)
         (well-typed-shift-atm a₂ Γ₁ Γ₂ T₁ _ wt-a₂)
         wt-op
well-typed-shift-mon (Let m₁ m₂) Γ₁ Γ₂ T' T (wt-let{T₁ = T₁} wt-m₁ wt-m₂) =
  let wt-m₁ : Γ₁ ++ T' ∷ Γ₂ ⊢ᵐ shift-mon m₁ (length Γ₁) ⦂ T₁
      wt-m₁ = well-typed-shift-mon m₁ Γ₁ Γ₂ T' T₁ wt-m₁ in
  let wt-m₂ : T₁ ∷ Γ₁ ++ T' ∷ Γ₂ ⊢ᵐ shift-mon m₂ (suc (length Γ₁)) ⦂ T
      wt-m₂ = well-typed-shift-mon m₂ (T₁ ∷ Γ₁) Γ₂ T' T wt-m₂ in
  wt-let{T₁ = T₁} wt-m₁ wt-m₂
well-typed-shift-mon (If m₁ m₂ m₃) Γ₁ Γ₂ T₁ T (wt-if wt-m₁ wt-m₂ wt-m₃) =
  wt-if (well-typed-shift-mon m₁ Γ₁ Γ₂ T₁ BoolT wt-m₁)
        (well-typed-shift-mon m₂ Γ₁ Γ₂ T₁ T wt-m₂)
        (well-typed-shift-mon m₃ Γ₁ Γ₂ T₁ T wt-m₃)

--------------- RCO Preserves Types -------------------

rco-well-typed : ∀ {Γ e T}
  → Γ ⊢ e ⦂ T
  → Γ ⊢ᵐ rco e ⦂ T
rco-well-typed wt-num = wt-atom wt-num
rco-well-typed wt-bool = wt-atom wt-bool
rco-well-typed wt-read = wt-read
rco-well-typed (wt-uni wt-e wt-op) =
  wt-let (rco-well-typed wt-e) (wt-uni (wt-var refl) wt-op)
rco-well-typed (wt-bin{Γ}{e₂ = e₂}{T₁}{T₂} wt-e₁ wt-e₂ wt-op) =
  wt-let (rco-well-typed wt-e₁)
  (wt-let (well-typed-shift-mon (rco e₂) [] Γ T₁ T₂ (rco-well-typed wt-e₂))
  (wt-bin (wt-var refl) (wt-var refl) wt-op))
rco-well-typed (wt-var nth) = wt-atom (wt-var nth)
rco-well-typed (wt-let wt-e₁ wt-e₂) =
  wt-let (rco-well-typed wt-e₁) (rco-well-typed wt-e₂)
rco-well-typed (wt-if wt-e₁ wt-e₂ wt-e₃) =
  wt-if (rco-well-typed wt-e₁) (rco-well-typed wt-e₂)
                               (rco-well-typed wt-e₃)
