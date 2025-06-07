module LIfRCO where

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

----------------- Remove Complex Operands ----------------------------

rco : Exp → Mon
rco (Num n) = Atom (Num n)
rco (Bool b) = Atom (Bool b)
rco Read = Read
rco (Uni op e) =
   Let (rco e) (Uni op (Var zero))
rco (Bin op e₁ e₂) =
   Let (rco e₁)
   (Let (shift-mon (rco e₂) zero) (Bin op (Var (suc (zero))) (Var zero)))
rco (Var i) = Atom (Var i)
rco (Let e₁ e₂) = Let (rco e₁) (rco e₂)
rco (If e₁ e₂ e₃) = If (rco e₁) (rco e₂) (rco e₃)
