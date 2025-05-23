module LVar where

open import Data.Nat using (ℕ; zero; suc; _≤ᵇ_)
open import Data.Nat.Properties
open import Data.Product
open import Data.Integer using (ℤ; -_; _-_)
open import Data.List
open import Data.Maybe
open import Relation.Binary.PropositionalEquality
   using (_≡_; refl; trans; sym; cong; cong-app)
open import Data.Vec
open import Data.Fin
open import Agda.Builtin.Bool

----------------- Variables ----------------------------

Id : ℕ → Set
Id n = Fin n

up : ∀ {k} → Id k → Id (suc k)
up zero = zero
up (suc i) = suc (up i)

----------------- Reader (ish) Monad ----------------------------

Reader : Set → Set
Reader A = ℕ → (ℕ → A) → A × ℕ × (ℕ → A)

read : ∀{A} → Reader A
read i f = f i , suc i , f

return : ∀{A : Set} → A → Reader A
return a i f = a , i , f

_then_ : ∀{A} → Reader A → (A → Reader A) → Reader A
(M then g) i f
    with M i f
... | v , i' , f' = g v i' f'

----------------- Definition of LVar ----------------------------

data Exp : ℕ → Set where
  Num : ∀ {n} → ℤ → Exp n
  Read : ∀{n} → Exp n
  Sub : ∀{n} → Exp n → Exp n → Exp n
  Var : ∀{n} → (i : Id n) → Exp n
  Let : ∀{n} → Exp n → Exp (suc n) → Exp n

Env : ℕ → Set
Env k = Vec ℤ k

interp : ∀{k} → Exp k → Env k → Reader ℤ
interp (Num n) ρ = return n
interp Read ρ = read
interp (Sub e₁ e₂) ρ =
  (interp e₁ ρ) then
  λ v₁ → (interp e₂ ρ) then
  λ v₂ → return (Data.Integer._-_ v₁ v₂)
interp (Var i) ρ = return (Data.Vec.lookup ρ i)
interp (Let e₁ e₂) ρ =
  (interp e₁ ρ) then
  λ v₁ → interp e₂ (v₁ ∷ ρ)

----------------- Definition of LMonVar ----------------------------

data Atm : ℕ → Set where
  Num : ∀ {n} → ℤ → Atm n
  Var : ∀{n} → Id n → Atm n

data Mon : ℕ → Set where
  Atom : ∀{n} → Atm n → Mon n
  Read : ∀{n} → Mon n
  Sub : ∀{n} → Atm n → Atm n → Mon n
  Let : ∀{n} → Mon n → Mon (suc n) → Mon n

interp-atm : ∀{k} → Atm k → Env k → Reader ℤ
interp-atm (Num n) ρ = return n
interp-atm (Var i) ρ = return (Data.Vec.lookup ρ i)

interp-mon : ∀{k} → Mon k → Env k → Reader ℤ
interp-mon (Atom atm) ρ = interp-atm atm ρ
interp-mon Read ρ = read
interp-mon (Sub a₁ a₂) ρ =
  (interp-atm a₁ ρ) then
  λ v₁ → (interp-atm a₂ ρ) then
  λ v₂ → return (Data.Integer._-_ v₁ v₂)
interp-mon (Let e₁ e₂) ρ =
  (interp-mon e₁ ρ) then
  λ v₁ → interp-mon e₂ (v₁ ∷ ρ)

shift-atm : ∀ {k} → Atm k → Id (suc k) → Atm (suc k)
shift-atm (Num x) c = Num x
shift-atm (Var x) c
    with toℕ c ≤ᵇ toℕ x
... | true = Var (suc x)
... | false = Var (up x)

shift-mon : ∀ {k} → Mon k → Id (suc k) → Mon (suc k)
shift-mon (Atom atm) c = Atom (shift-atm atm c)
shift-mon Read c = Read
shift-mon (Sub a₁ a₂) c = Sub (shift-atm a₁ c) (shift-atm a₂ c)
shift-mon (Let m₁ m₂) c = Let (shift-mon m₁ c) (shift-mon m₂ (suc c))

----------------- Remove Complex Operands ----------------------------

rco : ∀{k : ℕ} → Exp k → Mon k
rco (Num x) = Atom (Num x)
rco Read = Read
rco (Sub e₁ e₂) =
   let m₁ = rco e₁ in
   let m₂ = rco e₂ in
   Let m₁ (Let (shift-mon m₂ zero) (Sub (Var (suc (zero))) (Var zero)))
rco (Var i) = Atom (Var i)
rco (Let e₁ e₂) = Let (rco e₁) (rco e₂)

----------------- Definition of CVar ----------------------------

data CExp : ℕ → Set where
  Atom : ∀{n} → Atm n → CExp n
  Read : ∀{n} → CExp n
  Sub : ∀{n} → Atm n → Atm n → CExp n

data CTail : ℕ → Set where
  Return : ∀{n} → CExp n → CTail n
  Let : ∀{n} → CExp n → CTail (suc n) → CTail n

interp-exp : ∀{k} → CExp k → Env k → Reader ℤ
interp-exp (Atom atm) ρ = interp-atm atm ρ
interp-exp Read ρ = read
interp-exp (Sub a₁ a₂) ρ =
  (interp-atm a₁ ρ) then
  λ v₁ → (interp-atm a₂ ρ) then
  λ v₂ → return (Data.Integer._-_ v₁ v₂)

interp-tail : ∀{k} → CTail k → Env k → Reader ℤ
interp-tail (Return e) ρ = interp-exp e ρ
interp-tail (Let e t) ρ =
  (interp-exp e ρ) then
  λ v₁ → interp-tail t (v₁ ∷ ρ)

shift-exp : ∀ {k} → CExp k → Id (suc k) → CExp (suc k)
shift-exp (Atom atm) c = Atom (shift-atm atm c)
shift-exp Read c = Read
shift-exp (Sub a₁ a₂) c = Sub (shift-atm a₁ c) (shift-atm a₂ c)

shift-tail : ∀ {k} → CTail k → Id (suc k) → CTail (suc k)
shift-tail (Return e) c = Return (shift-exp e c)
shift-tail (Let e t) c = Let (shift-exp e c) (shift-tail t (suc c))

----------------- Explicate Control ----------------------------

explicate-assign : ∀{k} → Mon k → CTail (suc k) → CTail k
explicate-tail : ∀{k} → Mon k → CTail k

explicate-assign (Atom x) rest = Let (Atom x) rest  
explicate-assign Read rest = Let Read rest
explicate-assign (Sub a₁ a₂) rest = Let (Sub a₁ a₂) rest
explicate-assign (Let m₁ m₂) rest =
  let rest' = explicate-assign m₂ (shift-tail rest zero) in
  explicate-assign m₁ rest'

explicate-tail (Atom x) = Return (Atom x)
explicate-tail Read = Return Read
explicate-tail (Sub a₁ a₂) = Return (Sub a₁ a₂)
explicate-tail (Let m₁ m₂) = explicate-assign m₁ (explicate-tail m₂)

