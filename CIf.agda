module CIf where

open import Agda.Builtin.Unit
open import Data.Nat using (ℕ; zero; suc; _<_; _+_)
open import Data.Nat.Properties
open import Data.Product
open import Data.Integer using (ℤ; -_; _-_; 0ℤ; 1ℤ; -1ℤ; _≤ᵇ_)
open import Data.List
open import Data.Maybe
open import Relation.Binary.PropositionalEquality
   using (_≡_; refl; trans; sym; cong; cong-app)
open import Agda.Builtin.Bool renaming (Bool to 𝔹)
open import Data.Bool using (_∧_; _∨_; not)
open import Utilities
open import LIf
open import LMonIf
open import IL1
open import Reader

----------------- Definition of CIf ----------------------------

data CExp : Set where
  Atom : Atm → CExp
  Read : CExp
  Uni : UniOp → Atm → CExp
  Bin : BinOp → Atm → Atm → CExp

data CTail : Set where
  Return : CExp → CTail
  Assign : Id → CExp → CTail → CTail
  If : BinOp → Atm → Atm → Id → Id → CTail
  Goto : Id → CTail

Blocks : Set
Blocks = List CTail

data Type : Set where
  IntT : Type
  BoolT : Type

data C-Prog : Set where
  Program : ℕ → Id → Blocks → C-Prog

--- Interpreter for CIf

interp-CExp : CExp → Env Value → Reader Value
interp-CExp (Atom atm) ρ = try (interp-atm atm ρ)
interp-CExp Read ρ = read-int Int
interp-CExp (Uni op a) ρ =
  try (interp-atm a ρ) then
  λ v → try (uniop op v)
interp-CExp (Bin op a₁ a₂) ρ =
  try (interp-atm a₁ ρ) then
  λ v₁ → try (interp-atm a₂ ρ) then
  λ v₂ → try (binop op v₁ v₂)

--- Small-step Semantics for CIf

data CResult : Set where
  value : Value → CResult
  step : CTail → Env Value → Inputs → CResult

State = Inputs × Env Value

--- Big-step Semantics for CIf

infix 4 _,_⊢_⇓_⊣_
data _,_⊢_⇓_⊣_ : State → Blocks → CTail → Value → State → Set where
   return-⇓ : ∀{s s'}{ρ}{B}{e}{v}
       → interp-CExp e ρ s ≡ just (v , s')
       → (s , ρ) , B ⊢ Return e ⇓ v ⊣ (s' , ρ)
   assign-⇓ : ∀{ρ}{B}{x}{e}{t}{s s' : Inputs}{v}{r : State}
       → interp-CExp e ρ s ≡ just (v , s')
       → (s' , (update ρ x v)) , B ⊢ t ⇓ v ⊣ r
       → (s , ρ) , B ⊢ Assign x e t ⇓ v ⊣ r
   if-⇓-true : ∀{ρ}{B}{op}{a₁ a₂ : Atm}{thn}{els}{s s' : Inputs}{r : State}{v : Value}
       → interp-CExp (Bin op a₁ a₂) ρ s ≡ just (Bool true , s')
       → (s' , ρ) , B ⊢ Goto thn ⇓ v ⊣ r
       → (s , ρ) , B ⊢ If op a₁ a₂ thn els ⇓ v ⊣ r
   if-⇓-false : ∀{ρ}{B}{op}{a₁ a₂ : Atm}{thn}{els}{s s' : Inputs}{r : State}{v : Value}
       → interp-CExp (Bin op a₁ a₂) ρ s ≡ just (Bool false , s')
       → (s' , ρ) , B ⊢ Goto els ⇓ v ⊣ r
       → (s , ρ) , B ⊢ If op a₁ a₂ thn els ⇓ v ⊣ r
   goto-⇓ : ∀{ρ}{B}{s : Inputs}{lbl}{t : CTail}{r : State}{v : Value}
       → nth B lbl ≡ just t
       → (s , ρ) , B ⊢ t ⇓ v ⊣ r
       → (s , ρ) , B ⊢ Goto lbl ⇓ v ⊣ r

eval-CIf : C-Prog → Inputs → Value → Set
eval-CIf (Program n lbl B) s v =
    Σ[ r ∈ State ] (s , replicate n (Int 0ℤ)) , B ⊢ Goto lbl ⇓ v ⊣ r

