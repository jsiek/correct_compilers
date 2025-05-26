module LVar where

open import Data.Nat using (ℕ; zero; suc; _≤ᵇ_)
open import Data.Nat.Properties
open import Data.Product
open import Data.Integer using (ℤ; -_; _-_)
open import Data.List
open import Data.Maybe
open import Relation.Binary.PropositionalEquality
   using (_≡_; refl; trans; sym; cong; cong-app)
open import Agda.Builtin.Bool
open import Reader

----------------- Variables ----------------------------

Id : Set
Id = ℕ

----------------- Definition of LVar ----------------------------

data Exp : Set where
  Num : ℤ → Exp
  Read : Exp
  Sub : Exp → Exp → Exp
  Var : (i : Id) → Exp
  Let : Exp → Exp → Exp

Env : Set
Env = List ℤ

nth : ∀{A : Set} (xs : List A) → ℕ → Maybe A
nth [] i = nothing
nth (x ∷ xs) zero    = just x
nth (x ∷ xs) (suc i) = nth xs i

interp : Exp → Env → Reader ℤ
interp (Num n) ρ = return n
interp Read ρ = read
interp (Sub e₁ e₂) ρ =
  (interp e₁ ρ) then
  λ v₁ → (interp e₂ ρ) then
  λ v₂ → return (Data.Integer._-_ v₁ v₂)
interp (Var i) ρ = try (nth ρ i)
interp (Let e₁ e₂) ρ =
  (interp e₁ ρ) then
  λ v₁ → interp e₂ (v₁ ∷ ρ)

----------------- Definition of LMonVar ----------------------------

data Atm : Set where
  Num : ℤ → Atm 
  Var : Id → Atm

data Mon : Set where
  Atom : Atm → Mon
  Read : Mon
  Sub : Atm → Atm → Mon
  Let : Mon → Mon → Mon

interp-atm : Atm → Env → Reader ℤ
interp-atm (Num n) ρ = return n
interp-atm (Var i) ρ = try (nth ρ i)

interp-mon : Mon → Env → Reader ℤ
interp-mon (Atom atm) ρ = interp-atm atm ρ
interp-mon Read ρ = read
interp-mon (Sub a₁ a₂) ρ =
  (interp-atm a₁ ρ) then
  λ v₁ → (interp-atm a₂ ρ) then
  λ v₂ → return (Data.Integer._-_ v₁ v₂)
interp-mon (Let e₁ e₂) ρ =
  (interp-mon e₁ ρ) then
  λ v₁ → interp-mon e₂ (v₁ ∷ ρ)

shift-atm : Atm → ℕ → Atm
shift-atm (Num x) c = Num x
shift-atm (Var x) c
    with c ≤ᵇ x
... | true = Var (suc x)
... | false = Var x

shift-mon : Mon → ℕ → Mon
shift-mon (Atom atm) c = Atom (shift-atm atm c)
shift-mon Read c = Read
shift-mon (Sub a₁ a₂) c = Sub (shift-atm a₁ c) (shift-atm a₂ c)
shift-mon (Let m₁ m₂) c = Let (shift-mon m₁ c) (shift-mon m₂ (suc c))

----------------- Remove Complex Operands ----------------------------

rco : Exp → Mon
rco (Num x) = Atom (Num x)
rco Read = Read
rco (Sub e₁ e₂) =
   Let (rco e₁)
   (Let (shift-mon (rco e₂) zero) (Sub (Var (suc (zero))) (Var zero)))
rco (Var i) = Atom (Var i)
rco (Let e₁ e₂) = Let (rco e₁) (rco e₂)

----------------- Definition of CVar ----------------------------

data CExp : Set where
  Atom : Atm → CExp
  Read : CExp
  Sub : Atm → Atm → CExp

data CTail : Set where
  Return : CExp → CTail
  Let : CExp → CTail → CTail

interp-exp : CExp → Env → Reader ℤ
interp-exp (Atom atm) ρ = interp-atm atm ρ
interp-exp Read ρ = read
interp-exp (Sub a₁ a₂) ρ =
  (interp-atm a₁ ρ) then
  λ v₁ → (interp-atm a₂ ρ) then
  λ v₂ → return (Data.Integer._-_ v₁ v₂)

interp-tail : CTail → Env → Reader ℤ
interp-tail (Return e) ρ = interp-exp e ρ
interp-tail (Let e t) ρ =
  (interp-exp e ρ) then
  λ v₁ → interp-tail t (v₁ ∷ ρ)

shift-exp : CExp → ℕ → CExp
shift-exp (Atom atm) c = Atom (shift-atm atm c)
shift-exp Read c = Read
shift-exp (Sub a₁ a₂) c = Sub (shift-atm a₁ c) (shift-atm a₂ c)

shift-tail : CTail → ℕ → CTail
shift-tail (Return e) c = Return (shift-exp e c)
shift-tail (Let e t) c = Let (shift-exp e c) (shift-tail t (suc c))

----------------- Explicate Control ----------------------------

explicate-let : Mon → CTail → CTail
explicate : Mon → CTail

explicate-let (Atom x) rest = Let (Atom x) rest  
explicate-let Read rest = Let Read rest
explicate-let (Sub a₁ a₂) rest = Let (Sub a₁ a₂) rest
explicate-let (Let m₁ m₂) rest =
  -- (Let (Let m₁ m₂) rest) ==> (Let m₁ (Let m₂ rest))
  let rest' = explicate-let m₂ (shift-tail rest 1) in
  explicate-let m₁ rest'

explicate (Atom x) = Return (Atom x)
explicate Read = Return Read
explicate (Sub a₁ a₂) = Return (Sub a₁ a₂)
explicate (Let m₁ m₂) = explicate-let m₁ (explicate m₂)

