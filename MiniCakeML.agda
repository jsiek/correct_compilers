open import Data.Nat
open import Data.List
open import Data.Maybe

module MiniCakeML where

Var : Set
Var = ℕ

{-------------------- Untyped Lambda Calculus ---------------------------------}

data Term : Set where
  unit : Term
  `_ : Var → Term
  ƛ_ : Term → Term
  _·_ : Term → Term → Term
  
data Val : Set where
  vunit : Val
  clos : Term → List Val → Val

Env : Set
Env = List Val

data Result : Set → Set where
  val : ∀ {V : Set} → V → Result V
  error : ∀ {V : Set} → Result V
  timeout : ∀ {V : Set} → Result V

get : ∀{V : Set} → ℕ → List V → Maybe V
get n [] = nothing
get zero (v ∷ ρ) = just v
get (suc n) (v ∷ ρ) = get n ρ

_then_ : ∀{V W : Set} → Result V → (V → Result W) → Result W
r then f
    with r
... | val v = f v
... | error = error
... | timeout = timeout

cases : ∀{V : Set} → V → (V → Result V) → Result V
cases V f = f V

interp : ℕ → Term → Env → Result Val
interp 0 M ρ = timeout
interp (suc n) unit ρ = val vunit
interp (suc n) (` x) ρ
    with get x ρ
... | nothing = error
... | just v = val v
interp (suc n) (ƛ M) ρ = val (clos M ρ)
interp (suc n) (L · M) ρ =
    (interp n L ρ) then (λ V →
    (interp n M ρ) then (λ W →
    cases V (λ {vunit → error;
                (clos N ρ′) → interp n N (W ∷ ρ′) })))

   
{-------------------- Intermediate Language ---------------------------------}

data IL : Set where
  unit : IL
  `_ : Var → IL
  δ : ℕ → IL → IL
  _•_ : IL → List IL → IL
  _·_ : IL → IL → IL

data ILVal : Set where
  ilunit : ILVal
  delta : ℕ → IL → ILVal
  ilclos : IL → List ILVal → ILVal

ILEnv : Set
ILEnv = List ILVal


interpIL : ℕ → IL → ILEnv → Result ILVal
interpILs : ℕ → List IL → ILEnv → Result (List ILVal)

interpILs n [] ρ = val []
interpILs n (M ∷ Ms) ρ =
  (interpIL n M ρ) then (λ V →
  (interpILs n Ms ρ) then (λ Ws →
    val (V ∷ Ws)))

interpIL zero M ρ = timeout 
interpIL (suc n) unit ρ = val ilunit
interpIL (suc n) (` x) ρ
    with get x ρ
... | nothing = error
... | just v = val v
interpIL (suc n) (δ k N) ρ = val (delta k N)
interpIL (suc n) (L • Ms) ρ =
  (interpIL n L ρ) then (λ V →
  (interpILs n Ms ρ) then (λ Ws →
  cases V (λ{ ilunit → error ;
              (delta k N) → val (ilclos N Ws) ;
              (ilclos N vs) → error })))
interpIL (suc n) (L · M) ρ =
  (interpIL n L ρ) then (λ V →
  (interpIL n M ρ) then (λ W →
  cases V (λ{ ilunit → error ;
              (delta k N) → error ;
              (ilclos N vs) → interpIL n N (W ∷ vs) })))
