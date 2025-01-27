open import Data.Nat
open import Data.Nat.Properties
open import Data.List
open import Data.List.Properties
open import Data.Maybe
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; trans; cong; cong₂; cong-app; subst)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (tt; ⊤)
open import Data.Product

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

get-append-front : ∀ {T : Set} (xs ys : List T) i
  → i < length xs
  → get i (xs ++ ys) ≡ get i xs
get-append-front (x ∷ xs) ys zero lt = refl
get-append-front (x ∷ xs) ys (suc i) (s≤s lt) = get-append-front xs ys i lt

get-append-back : ∀ {T : Set} (xs ys : List T) i
  → get (length xs + i) (xs ++ ys) ≡ get i ys
get-append-back [] ys i = refl
get-append-back (x ∷ xs) ys i = get-append-back xs ys i

gets : ∀{V : Set} → List ℕ → List V → List V
gets [] ρ = []
gets (x ∷ xs) ρ
    with get x ρ
... | nothing = gets xs ρ
... | just V = V ∷ gets xs ρ

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

data _⊢_⇓_ : Env → Term → Val → Set where
  unit⇓ : ∀ ρ → ρ ⊢ unit ⇓ vunit
  var⇓ : ∀ ρ x v
    → get x ρ ≡ just v
    → ρ ⊢ ` x ⇓ v
  lam⇓ : ∀ ρ N
    → ρ ⊢ ƛ N ⇓ clos N ρ
  app⇓ : ∀ ρ L M N ρ′ W V
    → ρ ⊢ L ⇓ clos N ρ′
    → ρ ⊢ M ⇓ W
    → (W ∷ ρ′) ⊢ N ⇓ V
    → ρ ⊢ L · M ⇓ V
   
{-------------------- Intermediate Language ---------------------------------}

data IL : Set where
  unit : IL
  `_ : Var → IL
  δ : IL → IL
  _•_ : IL → List IL → IL
  _·_ : IL → IL → IL

data ILVal : Set where
  vunit : ILVal
  delta : IL → ILVal
  clos : IL → List ILVal → ILVal

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
interpIL (suc n) unit ρ = val vunit
interpIL (suc n) (` x) ρ
    with get x ρ
... | nothing = error
... | just v = val v
interpIL (suc n) (δ N) ρ = val (delta N)
interpIL (suc n) (L • Ms) ρ =
  (interpIL n L ρ) then (λ V →
  (interpILs n Ms ρ) then (λ Ws →
  cases V (λ{ vunit → error ;
              (delta N) → val (clos N Ws) ;
              (clos N vs) → error })))
interpIL (suc n) (L · M) ρ =
  (interpIL n L ρ) then (λ V →
  (interpIL n M ρ) then (λ W →
  cases V (λ{ vunit → error ;
              (delta N) → error ;
              (clos N vs) → interpIL n N (W ∷ vs) })))

data _⊢_⇩_ : ILEnv → IL → ILVal → Set 
data _⊢_⟱_ : ILEnv → List IL → List ILVal → Set 

data _⊢_⇩_ where
  unit⇩ : ∀ ρ → ρ ⊢ unit ⇩ vunit
  var⇩ : ∀ ρ x v
    → get x ρ ≡ just v
    → ρ ⊢ ` x ⇩ v
  delta⇩ : ∀ ρ N
    → ρ ⊢ δ N ⇩ delta N
  clos⇩ : ∀ ρ L N Ms Ws
    → ρ ⊢ L ⇩ delta N
    → ρ ⊢ Ms ⟱ Ws
    → ρ ⊢ L • Ms ⇩ clos N Ws
  app⇩ : ∀ ρ L M N ρ′ W V
    → ρ ⊢ L ⇩ clos N ρ′
    → ρ ⊢ M ⇩ W
    → (W ∷ ρ′) ⊢ N ⇩ V
    → ρ ⊢ L · M ⇩ V

data _⊢_⟱_ where
  empty⟱ : ∀ ρ → ρ ⊢ [] ⟱ []
  cons⟱ : ∀ {ρ M Ms V Vs}
    → ρ ⊢ M ⇩ V
    → ρ ⊢ Ms ⟱ Vs
    → ρ ⊢ (M ∷ Ms) ⟱ (V ∷ Vs)

{-------------------- Closure Conversion (Easy Version) -----------------------}

varsRange : ℕ → ℕ → List IL
varsRange start zero = []
varsRange start (suc num) = ` start ∷ varsRange (suc start) num

varsTo : ℕ → List IL
varsTo zero = []
varsTo (suc n) = ` n ∷ varsTo n

CC : Term → ℕ → IL
CC unit n = unit
CC (` x) n = ` x
CC (ƛ M) n = (δ (CC M (suc n))) • (varsRange 0 n)
CC (L · M) n = (CC L n) · (CC M n)


{-------------------- Testing Closure Conversion ------------------------------}

Eg1 : Term
Eg1 = (ƛ ` 0) · unit

_ : interp 10 Eg1 [] ≡ val vunit
_ = refl

_ : interpIL 10 (CC Eg1 0) [] ≡ val vunit
_ = refl

Eg2 : Term
Eg2 = ((ƛ (ƛ ` 1)) · unit) · (ƛ ` 0)

_ : interp 10 Eg2 [] ≡ val vunit
_ = refl

_ : interpIL 10 (CC Eg2 0) [] ≡ val vunit
_ = refl

{-------------------- Proof of Correctness ------------------------------}

{- Simulation Relation -}
data _⊢_≋_ : ℕ → Term → IL → Set
data _≈_ : Val → ILVal → Set
data _≅_ : List Val → List ILVal → Set

data _⊢_≋_ where
  unit≋ : ∀ {n} → n ⊢ unit ≋ unit
  var≋ : ∀ {n x} → n ⊢ (` x) ≋ (` x)
  lam≋ : ∀ {n N N′}
    → suc n ⊢ N ≋ N′
    → n ⊢ (ƛ N) ≋ ((δ N′) • (varsRange 0 n))
  app≋ : ∀ {n L L′ M M′}
    → n ⊢ L ≋ L′
    → n ⊢ M ≋ M′
    → n ⊢ (L · M) ≋ (L′ · M′)

data _≈_ where
  vunit≈ : vunit ≈ vunit
  clos≈ : ∀ N ρ N′ ρ′
     → suc (length ρ) ⊢ N ≋ N′
     → ρ ≅ ρ′
     → (clos N ρ) ≈ (clos N′ ρ′) 

data _≅_ where
  empty≅ : [] ≅ []
  cons≅ : ∀ {V Vs W Ws}
    → V ≈ W
    → Vs ≅ Ws
    → (V ∷ Vs) ≅ (W ∷ Ws)


lookupSomething : ∀ {ρ ρ′ x V}
  → ρ ≅ ρ′
  → get x ρ ≡ just V
  → ∃[ W ] get x ρ′ ≡ just W × V ≈ W
lookupSomething {V ∷ ρ} {W ∷ ρ′} {zero} {V} (cons≅ V≈W ρ≅ρ′) refl =
  W , (refl , V≈W)
lookupSomething {V ∷ ρ} {W ∷ ρ′} {suc x} {V′} (cons≅ V≈W ρ≅ρ′) ρxV =
  lookupSomething ρ≅ρ′ ρxV

lookupNothing : ∀ ρ ρ′ x 
  → ρ ≅ ρ′
  → get x ρ ≡ nothing
  → get x ρ′ ≡ nothing
lookupNothing [] [] zero ρ≅ρ′ ρxV = refl
lookupNothing [] [] (suc x) ρ≅ρ′ ρxV = refl
lookupNothing (V ∷ ρ) (W ∷ ρ′) (suc x) (cons≅ V≈W ρ≅ρ′) ρxV =
    lookupNothing ρ ρ′ x ρ≅ρ′ ρxV

compileRelated : ∀ M n → n ⊢ M ≋ CC M n
compileRelated unit n = unit≋
compileRelated (` x) n = var≋
compileRelated (ƛ M) n = lam≋ (compileRelated M (suc n))
compileRelated (L · M) n = app≋ (compileRelated L n) (compileRelated M n)

length-≅ : ∀ {ρ ρ′} → ρ ≅ ρ′ → length ρ ≡ length ρ′
length-≅ {.[]} {.[]} empty≅ = refl
length-≅ {.(_ ∷ _)} {.(_ ∷ _)} (cons≅ x ρ=ρ′) = cong suc (length-≅ ρ=ρ′)

evalVarsAux : ∀ (xs ys : ILEnv) num
  → num ≤ length ys
  → (xs ++ ys) ⊢ varsRange (length xs) num ⟱ take num ys
evalVarsAux xs ys zero lt = empty⟱ (xs ++ ys)
evalVarsAux xs (y ∷ ys) (suc num) (s≤s lt) rewrite sym (++-assoc xs (y ∷ []) ys)
   with  evalVarsAux (xs ++ (y ∷ [])) ys num lt
... | IH rewrite length-++ xs {y ∷ []} | +-comm (length xs) 1 =
  cons⟱ (var⇩ ((xs ++ y ∷ []) ++ ys) (length xs) y get-y) IH
  where
  LT : length xs < length (xs ++ y ∷ [])
  LT rewrite length-++ xs {y ∷ []} | +-comm (length xs) 1 = s≤s ≤-refl

  get-y : get (length xs) ((xs ++ y ∷ []) ++ ys) ≡ just y
  get-y rewrite get-append-front (xs ++ y ∷ []) ys (length xs) LT | sym (+-identityʳ (length xs)) =
    get-append-back xs (y ∷ []) 0

take-length : ∀ {T : Set} (xs : List T)
  → take (length xs) xs ≡ xs
take-length [] = refl
take-length (x ∷ xs) = cong (λ X → x ∷ X) (take-length xs)

evalVars : ∀ (ρ : ILEnv) 
  → ρ ⊢ varsRange 0 (length ρ) ⟱ ρ
evalVars ρ
    with evalVarsAux [] ρ (length ρ) ≤-refl
... | EV rewrite (take-length ρ) = EV

evalRelated : ∀ M M′ ρ ρ′ V
  → length ρ ⊢ M ≋ M′
  → ρ ≅ ρ′
  → ρ ⊢ M ⇓ V
  → ∃[ W ] ρ′ ⊢ M′ ⇩ W × V ≈ W
evalRelated .unit .unit ρ ρ′ .vunit unit≋ ρ=ρ′ (unit⇓ .ρ) = vunit , (unit⇩ ρ′ , vunit≈)
evalRelated .(` x) .(` x) ρ ρ′ V var≋ ρ=ρ′ (var⇓ .ρ x .V eq)
    with lookupSomething ρ=ρ′ eq
... | W , eq2 , V=W = W , ((var⇩ ρ′ x W eq2) , V=W)  
evalRelated .(ƛ N) .(δ _ • varsRange 0 n) ρ ρ′ .(clos N ρ) (lam≋{n}{N}{N′} N=N′) ρ=ρ′ (lam⇓ .ρ N) =
  clos N′ ρ′ ,
  clos⇩ ρ′ (δ N′) N′ (varsRange zero (length ρ)) ρ′ (delta⇩ ρ′ N′) Goal1 ,
  clos≈ N ρ N′ ρ′ N=N′ ρ=ρ′
  where
  Goal1 : ρ′ ⊢ varsRange 0 (length ρ) ⟱ ρ′
  Goal1 rewrite length-≅ ρ=ρ′ = evalVars ρ′
evalRelated .(L · M) (L′ · M′) ρ ρ′ V (app≋ L=L′ M=M′) ρ=ρ′ (app⇓ .ρ L M N ρ″ W .V L⇓C M⇓W N⇓V)
    with evalRelated _ _ _ _ _ L=L′ ρ=ρ′ L⇓C
... | .(clos N′ ρ‴) , L′⇓C′ , clos≈ .N .ρ″ N′ ρ‴ N=N′ ρ″=ρ‴
    with evalRelated _ _ _ _ _ M=M′ ρ=ρ′ M⇓W
... | W′ , M′⇓W′ , W=W′
    with evalRelated _ _ _ _ _ N=N′ (cons≅ W=W′ ρ″=ρ‴) N⇓V
... | V′ , N′⇓V′ , V=V′ =
    V′ , (app⇩ ρ′ L′ M′ N′ ρ‴ W′ V′ L′⇓C′ M′⇓W′ N′⇓V′ , V=V′)


{-
{- Having both up and down is problematic -Jeremy -}

down≅ : ∀ {n ρ ρ′}
  → suc n ⊢ ρ ≅ ρ′
  → n ⊢ ρ ≅ ρ′
down≅ = {!!}

up≈ : ∀ {n M M′}
  → n ⊢ M ≈ M′
  → suc n ⊢ M ≈ M′
up≈ = {!!}

correct : ∀ M n ρ ρ′
  → n ⊢ ρ ≅ ρ′
  → n ⊢ interp n M ρ ≈ᵣ interpIL n (CC M (length ρ)) ρ′
correct unit zero ρ ρ′ ρ≅ρ′ = tt
correct unit (suc n) ρ ρ′ ρ≅ρ′ = tt
correct (` x) zero ρ ρ′ ρ≅ρ′ = tt
correct (` x) (suc n) ρ ρ′ ρ≅ρ′
    with get x ρ in eq
... | nothing
    with get x ρ′ in eq′
... | nothing = tt
... | just W′
    with lookupNothing ρ ρ′ x n (down≅ ρ≅ρ′) eq
... | eq2 rewrite eq′
    with eq2
... | ()
correct (` x) (suc n) ρ ρ′ ρ≅ρ′ | just V
    with lookupSomething ρ ρ′ x n V (down≅ ρ≅ρ′) eq
... | W , eq2 , V≈W
    with get x ρ′
... | nothing
    with eq2
... | ()
correct (` x) (suc n) ρ ρ′ ρ≅ρ′ | just V | W , eq2 , V≈W | just W′
    with eq2
... | refl = up≈ V≈W
correct (ƛ M) n ρ ρ′ ρ≅ρ′ = {!!}
correct (M · M₁) n ρ ρ′ ρ≅ρ′ = {!!}
-}
{--
data _≈_ : Val → ILVal → Set
data _≅_ : List Val → List ILVal → Set
data _≈ᵣ_ : Result Val → Result ILVal → Set

data _≈_ where
  relUnit : vunit ≈ vunit
  relClos : ∀ N N′ ρ ρ′
    → (∀ n V W → V ≈ W → interp n N (V ∷ ρ) ≈ᵣ interpIL n N′ (W ∷ ρ′))
    → ρ ≅ ρ′
    → (clos N ρ) ≈ (ilclos N′ ρ′)

data _≅_ where
  relEmpty : [] ≅ []
  relCons : ∀{V Vs W Ws}
    → V ≈ W
    → Vs ≅ Ws
    → (V ∷ Vs) ≅ (W ∷ Ws)

data _≈ᵣ_ where
--}
