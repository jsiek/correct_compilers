module LMonLiftLocals where

open import Agda.Builtin.Unit
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (if_then_else_)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; _≤ᵇ_; _∸_; _+_; s≤s; _⊔_)
open import Data.Nat.Properties
open import Data.Product
open import Data.Sum
open import Data.Integer using (ℤ; -_; _-_; 0ℤ; 1ℤ; -1ℤ)
open import Data.List
open import Data.List.Properties using (++-assoc; length-replicate; ++-identityʳ; length-++)
open import Data.Maybe
open import Relation.Binary.PropositionalEquality
   using (_≡_; refl; trans; sym; cong; cong-app)
open import Agda.Builtin.Bool renaming (Bool to 𝔹)
open import Relation.Nullary.Negation.Core using (¬_; contradiction)
open import Function.Base using (case_of_; case_returning_of_)

open import Utilities
open import LIf
open import LMonIf
open import IL1
open import Reader

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

