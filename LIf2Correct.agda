module LIf2Correct where

open import Data.Integer using (ℤ)
open import Data.Maybe
open import Relation.Binary.PropositionalEquality using (_≡_; trans)

open import Utilities
open import LIf2
open import LIf2RCOCorrect
open import LIf2LiftCorrect
open import LIf2ExplicateCorrect
open import LIf2SelectCorrect

compile-correct : (e : Exp) (s : Inputs) (v : Value)
  → interp-LIf e s ≡ just v
  → interp-x86-var (compile e) s v
compile-correct e s v ie =
   let i-rco = trans (rco-correct e s) ie in
   let i-lift = lift-locals-correct (rco e) s v i-rco in
   let i-exp = explicate-correct (lift-locals (rco e)) s v i-lift in
   select-inst-correct (explicate (lift-locals (rco e))) s v i-exp


