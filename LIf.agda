module LIf where

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
open import Reader
open import Utilities

----------------- Definition of LIf ----------------------------

data UniOp : Set where
  Neg : UniOp
  Not : UniOp

data BinOp : Set where
  Sub : BinOp
  Eq : BinOp
  LessEq : BinOp
  And : BinOp

data Exp : Set where
  Num : ℤ → Exp
  Bool : 𝔹 → Exp
  Read : Exp
  Uni : UniOp → Exp → Exp
  Bin : BinOp → Exp → Exp → Exp
  Var : (i : Id) → Exp
  Let : Exp → Exp → Exp
  If : Exp → Exp → Exp → Exp

data Value : Set where
  Int : ℤ → Value
  Bool : 𝔹 → Value

toInt : Value → Maybe ℤ
toInt (Int n) = just n
toInt (Bool b) = nothing

toBool : Value → Maybe 𝔹
toBool (Int n) = nothing
toBool (Bool b) = just b

uniop : UniOp → Value → Reader Value
uniop Neg v =
  try (toInt v) then
  (λ n → return (Int (- n)))
uniop Not v =
  try (toBool v) then
  (λ n → return (Bool (not n)))

binop : BinOp → Value → Value → Reader Value
binop Sub v₁ v₂ =
  try (toInt v₁) then
  λ n₁ → try (toInt v₂) then
  λ n₂ → return (Int (n₁ - n₂))
binop Eq v₁ v₂ =
  try (toInt v₁) then
  λ n₁ → try (toInt v₂) then
  λ n₂ → return (Bool ((n₁ ≤ᵇ n₂) ∧ (n₂ ≤ᵇ n₁)))
binop LessEq v₁ v₂ =
  try (toInt v₁) then
  λ n₁ → try (toInt v₂) then
  λ n₂ → return (Bool (n₁ ≤ᵇ n₂))
binop And v₁ v₂ =
  try (toBool v₁) then
  λ b₁ → try (toBool v₂) then
  λ b₂ → return (Bool (b₁ ∧ b₂))

interp-exp : Exp → Env Value → Reader Value
interp-exp (Num n) ρ = return (Int n)
interp-exp (Bool b) ρ = return (Bool b)
interp-exp Read ρ = read-int Int
interp-exp (Uni op e) ρ =
  (interp-exp e ρ) then
  λ v → uniop op v
interp-exp (Bin op e₁ e₂) ρ =
  (interp-exp e₁ ρ) then
  λ v₁ → (interp-exp e₂ ρ) then
  λ v₂ → binop op v₁ v₂
interp-exp (Var i) ρ = try (nth ρ i)
interp-exp (Let e₁ e₂) ρ =
  (interp-exp e₁ ρ) then
  λ v₁ → interp-exp e₂ (v₁ ∷ ρ)
interp-exp (If e₁ e₂ e₃) ρ =
  (interp-exp e₁ ρ) then
  λ v₁ → try (toBool v₁) then
  λ { true → interp-exp e₂ ρ
    ; false → interp-exp e₃ ρ }

interp-LIf : Exp → Inputs → Maybe Value
interp-LIf e s = run (interp-exp e []) s

----------------- Definition of LMonIf ----------------------------

data Atm : Set where
  Num : ℤ → Atm 
  Bool : 𝔹 → Atm
  Var : Id → Atm

data Mon : Set where
  Atom : Atm → Mon
  Read : Mon
  Uni : UniOp → Atm → Mon
  Bin : BinOp → Atm → Atm → Mon
  Let : Mon → Mon → Mon
  If : Mon → Mon → Mon → Mon

interp-atm : Atm → Env Value → Maybe Value
interp-atm (Num n) ρ = just (Int n)
interp-atm (Bool b) ρ = just (Bool b)
interp-atm (Var i) ρ = nth ρ i

interp-mon : Mon → Env Value → Reader Value
interp-mon (Atom atm) ρ = try (interp-atm atm ρ)
interp-mon Read ρ = read-int Int
interp-mon (Uni op a) ρ =
  try (interp-atm a ρ) then
  λ v → uniop op v
interp-mon (Bin op a₁ a₂) ρ =
  try (interp-atm a₁ ρ) then
  λ v₁ → try (interp-atm a₂ ρ) then
  λ v₂ → binop op v₁ v₂
interp-mon (Let e₁ e₂) ρ =
  (interp-mon e₁ ρ) then
  λ v₁ → interp-mon e₂ (v₁ ∷ ρ)
interp-mon (If e₁ e₂ e₃) ρ =
  (interp-mon e₁ ρ) then
  λ v₁ → try (toBool v₁) then
  λ { true → interp-mon e₂ ρ
    ; false → interp-mon e₃ ρ }

interp-LMonIf : Mon → Inputs → Maybe Value
interp-LMonIf m s = run (interp-mon m []) s

shift-atm : Atm → ℕ → Atm
shift-atm (Num n) c = Num n
shift-atm (Bool b) c = Bool b
shift-atm (Var x) c = Var (shift-var x c)

shift-mon : Mon → ℕ → Mon
shift-mon (Atom atm) c = Atom (shift-atm atm c)
shift-mon Read c = Read
shift-mon (Uni op a) c = Uni op (shift-atm a c)
shift-mon (Bin op a₁ a₂) c = Bin op (shift-atm a₁ c) (shift-atm a₂ c)
shift-mon (Let m₁ m₂) c =
  Let (shift-mon m₁ c) (shift-mon m₂ (suc c))
shift-mon (If m₁ m₂ m₃) c =
  If (shift-mon m₁ c) (shift-mon m₂ c) (shift-mon m₃ c)

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


----------------- Definition of IL1If ----------------------------

data IL1-Exp : Set where
  Atom : Atm → IL1-Exp
  Read : IL1-Exp
  Uni : UniOp → Atm → IL1-Exp
  Bin : BinOp → Atm → Atm → IL1-Exp
  Assign : Id → IL1-Exp → IL1-Exp → IL1-Exp
  If : IL1-Exp → IL1-Exp → IL1-Exp → IL1-Exp

data IL1-Prog : Set where
  Program : ℕ → IL1-Exp → IL1-Prog

interp-il1-exp : IL1-Exp → Env Value → Reader Value
interp-il1-exp (Atom atm) ρ = try (interp-atm atm ρ)
interp-il1-exp Read ρ = read-int Int
interp-il1-exp (Uni op a) ρ =
  try (interp-atm a ρ) then
  λ v → uniop op v
interp-il1-exp (Bin op a₁ a₂) ρ =
  try (interp-atm a₁ ρ) then
  λ v₁ → try (interp-atm a₂ ρ) then
  λ v₂ → binop op v₁ v₂
interp-il1-exp (Assign x e₁ e₂) ρ =
  (interp-il1-exp e₁ ρ) then
  λ v₁ → interp-il1-exp e₂ (update ρ x v₁)
interp-il1-exp (If e₁ e₂ e₃) ρ =
  (interp-il1-exp e₁ ρ) then
  λ v₁ → try (toBool v₁) then
  λ { true → interp-il1-exp e₂ ρ
    ; false → interp-il1-exp e₃ ρ }

interp-IL1 : IL1-Prog → Inputs → Maybe Value
interp-IL1 (Program n e) s =
    run (interp-il1-exp e (replicate n (Int 0ℤ))) s

----------------- Convert to IL1: Lift Locals -------------------

shifts-atm : Atm → ℕ → ℕ → Atm
shifts-atm (Num x) c n = Num x
shifts-atm (Bool b) c n = Bool b
shifts-atm (Var x) c n = Var (shifts-var x c n)

shifts-il1-exp : IL1-Exp → ℕ → ℕ → IL1-Exp
shifts-il1-exp (Atom a) c n =
    Atom (shifts-atm a c n) 
shifts-il1-exp Read c n =
    Read
shifts-il1-exp (Uni op a) c n =
    Uni op (shifts-atm a c n)
shifts-il1-exp (Bin op a₁ a₂) c n =
    Bin op (shifts-atm a₁ c n) (shifts-atm a₂ c n)
shifts-il1-exp (Assign x e₁ e₂) c n =
    Assign (shifts-var x c n) (shifts-il1-exp e₁ c n) (shifts-il1-exp e₂ c n)
shifts-il1-exp (If e₁ e₂ e₃) c n =
    If (shifts-il1-exp e₁ c n) (shifts-il1-exp e₂ c n) (shifts-il1-exp e₃ c n)

-- Hoists all the Let's to the top, leaving in their place assignments.
--   let x = e₁ in e₂
--   ==>
--   let x = 0 in { x := e′₁; e′₂ }
--
--
--   Returns the number of let's around the expression:
--   let y₁=0,...,yᵢ=0 in m₁
--   is represented as
--   i , m₁
lift-locals-mon : Mon → ℕ × IL1-Exp
lift-locals-mon (Atom a) = 0 , (Atom a)
lift-locals-mon Read = 0 , Read
lift-locals-mon (Uni op a) = 0 , (Uni op a)
lift-locals-mon (Bin op a₁ a₂) = 0 , (Bin op a₁ a₂)

lift-locals-mon (Let m₁ m₂)
    with lift-locals-mon m₁
... | i , e₁
    with lift-locals-mon m₂
... | j , e₂
--   let x = (let y₁=0,...,yᵢ=0 in m₁)
--   in (let z₁=0,...,zⱼ=0 in m₂)
--   ==>
--   let x=0, y₁=0,...,yᵢ=0, z₁=0,...,zⱼ=0  in
--   i+j := (e₁ ↑ j+1 cutoff 0);
--   (e₂ ↑ i cutoff j)
    = (suc (i + j)) , Assign (i + j) (shifts-il1-exp e₁ 0 (suc j)) (shifts-il1-exp e₂ j i)
    
lift-locals-mon (If m₁ m₂ m₃) 
    with lift-locals-mon m₁ 
... | i , e₁
    with lift-locals-mon m₂ 
... | j , e₂
    with lift-locals-mon m₃ 
... | k , e₃
--  if (let x₁=0,...,xᵢ=0 in m₁) then
--      (let y₁=0,...,yⱼ=0 in m₂)
--  else 
--      (let z₁=0,...,z_k=0 in m₃)
--  ==>
--  let x₁=0,...,xᵢ=0, y₁=0,...,yⱼ=0, z₁=0,...,z_k=0 in
--  if (m₁ ↑ j + k cutoff 0) then ((m₂ ↑ k cutoff 0) ↑ i cutoff (k + j)) else (m₃ ↑ i + j cutoff k)
    =
    let e′₁ = shifts-il1-exp e₁ 0 (j + k) in
    let e′₂ = shifts-il1-exp (shifts-il1-exp e₂ 0 k) (k + j) i in
    let e′₃ = shifts-il1-exp e₃ k (i + j) in
    (i + j + k) , (If e′₁ e′₂ e′₃)

lift-locals : Mon → IL1-Prog
lift-locals m
    with lift-locals-mon m
... | n , e = Program n e    

---- Test lift-locals

S0 : Inputs
S0 = (1 , λ x → Data.Integer.+ x)

test : Mon → Set
test P = interp-IL1 (lift-locals P) S0 ≡ run (interp-mon P []) S0

P0 : Mon
P0 = Let Read (Atom (Var 0))
T0 : test P0
T0 = refl

P1 : Mon
P1 = Let Read (Let Read (Bin Sub (Var 0) (Var 1)))
T1 : test P1
T1 = refl

P2 : Mon
P2 = Let Read
      (Let (Let (Bin Sub (Var 0) (Num 1ℤ)) (Bin Sub (Var 0) (Num -1ℤ)))
       (Let (Uni Neg (Var 0))
        (Bin Sub (Var 2) (Var 0))))
T2 : test P2
T2 = refl

P3 : Mon
P3 = Let Read
      (If (Bin LessEq (Var 0) (Num 1ℤ))
        (Let Read (Atom (Var 0)))
        (Let Read (Atom (Num 0ℤ))))
T3 : test P3
T3 = refl

P4 : Mon
P4 = Let Read
       (If (Let Read (Bin LessEq (Var 0) (Num 1ℤ)))
           (Let Read (Bin Sub (Var 0) (Var 1)))
           (Let Read (Bin Sub (Var 1) (Var 0))))
T4 : test P4
T4 = refl

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
  λ v → uniop op v
interp-CExp (Bin op a₁ a₂) ρ =
  try (interp-atm a₁ ρ) then
  λ v₁ → try (interp-atm a₂ ρ) then
  λ v₂ → binop op v₁ v₂

--- Big-step Semantics for CIf

infix 4 _,_,_⊢_⇓_
data _,_,_⊢_⇓_ : Env Value → Inputs → Blocks → CTail → (Value × Inputs) → Set where
   return-⇓ : ∀{ρ}{s}{B}{e}{r}
       → interp-CExp e ρ s ≡ just r
       → ρ , s , B ⊢ Return e ⇓ r
   assign-⇓ : ∀{ρ}{B}{x}{e}{t}{s0 s1 : Inputs}{v}{r : (Value × Inputs)}
       → interp-CExp e ρ s0 ≡ just (v , s1)
       → update ρ x v , s1 , B ⊢ t ⇓ r
       → ρ , s0 , B ⊢ Assign x e t ⇓ r
   if-⇓-true : ∀{ρ}{B}{op}{a₁ a₂ : Atm}{thn}{els}{s0 s1 : Inputs}{t-thn : CTail }{r : (Value × Inputs)}
       → interp-CExp (Bin op a₁ a₂) ρ s0 ≡ just (Bool true , s1)
       → nth B thn ≡ just t-thn
       → ρ , s1 , B ⊢ t-thn ⇓ r
       → ρ , s0 , B ⊢ If op a₁ a₂ thn els ⇓ r
   if-⇓-false : ∀{ρ}{B}{op}{a₁ a₂ : Atm}{thn}{els}{s0 s1 : Inputs}{t-els : CTail }{r : (Value × Inputs)}
       → interp-CExp (Bin op a₁ a₂) ρ s0 ≡ just (Bool true , s1)
       → nth B els ≡ just t-els
       → ρ , s1 , B ⊢ t-els ⇓ r
       → ρ , s0 , B ⊢ If op a₁ a₂ thn els ⇓ r
   goto-⇓ : ∀{ρ}{B}{s0 : Inputs}{lbl}{t : CTail}{r : (Value × Inputs)}
       → nth B lbl ≡ just t
       → ρ , s0 , B ⊢ t ⇓ r
       → ρ , s0 , B ⊢ Goto lbl ⇓ r

eval-CIf : C-Prog → Inputs → Value → Set
eval-CIf (Program n lbl B) s v =
    Σ[ s' ∈ Inputs ] (replicate n (Int 0ℤ)) , s , B ⊢ Goto lbl ⇓ (v , s')

----------------- Explicate Control ----------------------------

-- Split into two parts:
-- A) Move the Let's to the top
-- B) Convert AST to a DAG

-- Block Monad
-- Next label to use for a new block
-- The list of blocks that have been created

Blocker : Set → Set
Blocker A = Blocks → A × Blocks

returnB : ∀{A : Set} → A → Blocker A
returnB a s = a , s

_thenB_ : ∀{A B : Set} → Blocker A → (A → Blocker B) → Blocker B
(M thenB g) s
    with M s
... | (v , s') = g v s'

create-block : CTail → Blocker Id
create-block (Goto lbl) B = lbl , B
create-block t B = length B , (B ++ [ t ])

explicate-assign : Id → IL1-Exp → CTail → Blocker CTail
explicate-pred : IL1-Exp → CTail → CTail → Blocker CTail
explicate-tail : IL1-Exp → Blocker CTail

explicate-assign y (Atom a) rest = returnB (Assign y (Atom a) rest)
explicate-assign y Read rest = returnB (Assign y Read rest)
explicate-assign y (Uni op a) rest = returnB (Assign y (Uni op a) rest)
explicate-assign y (Bin op a₁ a₂) rest = returnB (Assign y (Bin op a₁ a₂) rest)
explicate-assign y (Assign x e₁ e₂) rest =
  explicate-assign y e₂ rest thenB
  λ t₂ → explicate-assign x e₁ t₂
explicate-assign y (If e₁ e₂ e₃) rest =
   create-block rest thenB
   λ l → explicate-assign y e₂ (Goto l) thenB
   λ t₂ → explicate-assign y e₃ (Goto l) thenB
   λ t₃ → explicate-pred e₁ t₂ t₃

explicate-pred (Atom a) thn els =
  create-block thn thenB
  λ l₁ → create-block els thenB
  λ l₂ → returnB (If Eq a (Bool true) l₁ l₂)
explicate-pred Read thn els = returnB (Return (Atom (Num 0ℤ)))
explicate-pred (Uni Neg a) thn els = returnB (Return (Atom (Num 0ℤ)))
explicate-pred (Uni Not a) thn els = explicate-pred (Atom a) els thn
explicate-pred (Bin op a₁ a₂) thn els =
  create-block thn thenB
  λ lbl-thn → create-block els thenB
  λ lbl-els → returnB (If op a₁ a₂ lbl-thn lbl-els)
explicate-pred (Assign x e₁ e₂) thn els =
  explicate-pred e₂ thn els thenB
  λ rest' → explicate-assign x e₁ rest'
explicate-pred (If e₁ e₂ e₃) thn els =
    create-block thn thenB
   λ lbl-thn → create-block els thenB
   λ lbl-els → explicate-pred e₂ (Goto lbl-thn) (Goto lbl-els) thenB
   λ t₂ → (explicate-pred e₃ (Goto lbl-thn) (Goto lbl-els)) thenB
   λ t₃ → explicate-pred e₁ t₂ t₃

explicate-tail (Atom a) = returnB (Return (Atom a))
explicate-tail Read = returnB (Return Read)
explicate-tail (Uni op a) = returnB (Return (Uni op a))
explicate-tail (Bin op a₁ a₂) = returnB (Return (Bin op a₁ a₂))
explicate-tail (Assign x e₁ e₂) =
  explicate-tail e₂ thenB
  λ t₂ → explicate-assign x e₁ t₂
explicate-tail (If e₁ e₂ e₃) =
  (explicate-tail e₂) thenB
  λ t₂ → (explicate-tail e₃) thenB
  λ t₃ → explicate-pred e₁ t₂ t₃

explicate : IL1-Prog → C-Prog
explicate (Program n e)
    with ((explicate-tail e) thenB
          (λ t → create-block t)) []
... | lbl , B = Program n lbl B
     
