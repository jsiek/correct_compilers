module LVarCorrect where

open import Agda.Builtin.Unit
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using ()
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; _≤ᵇ_; _∸_; _+_; s≤s)
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
open import LVar
open import LVarRCOCorrect
open import LVarLiftCorrect
open import LVarExplicateCorrect
open import LVarSelectCorrect

compile-correct : (e : Exp) (s : Inputs) (v : ℤ)
  → interp-LVar e s ≡ just v
  → interp-x86-var (compile e) s v
compile-correct e s v ie =
   let i-rco = trans (rco-correct e s) ie in
   let i-lift = lift-locals-correct (rco e) s v i-rco in
   let i-exp = explicate-correct (lift-locals (rco e)) s v i-lift in
   select-inst-correct (explicate (lift-locals (rco e))) s v i-exp


