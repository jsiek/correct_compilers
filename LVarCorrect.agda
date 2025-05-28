module LVarCorrect where

open import Agda.Builtin.Unit
open import Data.Bool using ()
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; _≤ᵇ_; _∸_; _+_; s≤s)
open import Data.Nat.Properties
open import Data.Product
open import Data.Sum
open import Data.Integer using (ℤ; -_; _-_; 0ℤ)
open import Data.List
open import Data.List.Properties using (++-assoc; length-replicate; ++-identityʳ)
open import Data.Maybe
open import Relation.Binary.PropositionalEquality
   using (_≡_; refl; trans; sym; cong; cong-app)
open import Agda.Builtin.Bool
open import Relation.Nullary.Negation.Core using (¬_; contradiction)
open import Function.Base using (case_of_; case_returning_of_)

open import LVar
open import Reader

update-correct : ∀ {A} (xs ys : List A) (v v' : A)
  → update (xs ++ v ∷ ys) (length xs) v' ≡ xs ++ v' ∷ ys
update-correct [] ys v v' = refl
update-correct (x ∷ xs) ys v v' rewrite update-correct xs ys v v' = refl

++-length : ∀ {A : Set} (xs : List A) (m n : ℕ)
  → length xs ≡ (m + n)
  → Σ[ ys ∈ List A ] Σ[ zs ∈ List A ] (xs ≡ ys ++ zs × length ys ≡ m × length zs ≡ n)
++-length xs zero n len_mn = [] , xs , refl , refl , len_mn
++-length (x ∷ xs) (suc m) n len_mn
    with ++-length xs m n (suc-injective len_mn)
... | ys , zs , refl , refl , refl
    = x ∷ ys , zs , refl , refl , refl

++-length-+-1 : ∀ {A : Set} (xs : List A) (m : ℕ)
  → length xs ≡ (m + 1)
  → Σ[ ys ∈ List A ] Σ[ z ∈ A ] (xs ≡ ys ++ [ z ] × length ys ≡ m)
++-length-+-1 xs m eq
    with ++-length xs m 1 eq
... | ys , z ∷ [] , refl , refl , eq2
    = ys , z , refl , refl

m≤n⇒-+ : ∀ (m n : ℕ)
  → m ≤ n
  → Σ[ l ∈ ℕ ] m + l ≡ n
m≤n⇒-+ zero n mn = n , refl
m≤n⇒-+ (suc m) (suc n) (s≤s mn)
    with m≤n⇒-+ m n mn
... | l , refl = l , refl

nth-++-< : ∀{A : Set} → (xs ys : List A) (x : ℕ)
       → x < length xs
       → nth (xs ++ ys) x ≡ nth xs x
nth-++-< {A} (x₁ ∷ xs) ys zero lt = refl
nth-++-< {A} (x₁ ∷ xs) ys (suc x) (_≤_.s≤s lt) = nth-++-< xs ys x lt

-- TODO: replace uses of nth-++-≤ with nth-++-+
nth-++-≤ : ∀{A : Set} → (xs ys : List A) (x : ℕ)
       → length xs ≤ x
       → nth (xs ++ ys) x ≡ nth ys (x ∸ length xs)
nth-++-≤ {A} [] ys x lt = refl
nth-++-≤ {A} (x₁ ∷ xs) ys (suc x) (_≤_.s≤s lt) = nth-++-≤ xs ys x lt

nth-++-+ : ∀{A : Set} → (xs ys : List A) (n : ℕ)
       → nth (xs ++ ys) (length xs + n) ≡ nth ys n
nth-++-+ {A} [] ys n = refl
nth-++-+ {A} (x ∷ xs) ys n = nth-++-+ xs ys n

eq-true-top : ∀{P} → P ≡ true → Data.Bool.T P
eq-true-top {P} eq rewrite eq = tt

eq-false-not-top : ∀{P} → P ≡ false → ¬ Data.Bool.T P
eq-false-not-top {P} eq rewrite eq = λ {()}

postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------------------
    → f ≡ g

--------------- Proof of correctness for RCO ------------------------

interp-shift-atm : ∀ (a : Atm) (v : ℤ) (ρ₁ : Env) (ρ₂ : Env)
  → interp-atm (shift-atm a (length ρ₁)) (ρ₁ ++ v ∷ ρ₂) 
    ≡ interp-atm a (ρ₁ ++ ρ₂) 
interp-shift-atm a v ρ₁ ρ₂ = extensionality (Goal a)
  where
  Goal : (a : Atm )(s : StateR ℤ) →
        interp-atm (shift-atm a (length ρ₁)) (ρ₁ ++ v ∷ ρ₂) s
      ≡ interp-atm a (ρ₁ ++ ρ₂) s
  Goal (Num x) s = refl
  Goal (Var x) s
      with (length ρ₁) ≤ᵇ x in lt
  ... | true
      rewrite nth-++-≤ ρ₁ ρ₂ x (≤ᵇ⇒≤ (length ρ₁) x (eq-true-top lt))
      | nth-++-≤ ρ₁ (v ∷ ρ₂) (suc x) (≤-trans ((≤ᵇ⇒≤ (length ρ₁) x (eq-true-top lt))) (n≤1+n x))
      | +-∸-assoc 1 {x}{length ρ₁} (≤ᵇ⇒≤ (length ρ₁) x (eq-true-top lt)) =
        refl
  ... | false
      rewrite nth-++-< ρ₁ ρ₂ x (≰⇒> λ x₁ → (eq-false-not-top lt) (≤⇒≤ᵇ x₁))
      | nth-++-< ρ₁ (v ∷ ρ₂) x ((≰⇒> λ x₁ → (eq-false-not-top lt) (≤⇒≤ᵇ x₁))) =
     refl  

interp-shift-mon : ∀ (m : Mon) (v : ℤ) (ρ₁ : Env) (ρ₂ : Env)
  → interp-mon (shift-mon m (length ρ₁)) (ρ₁ ++ (v ∷ ρ₂))
    ≡ interp-mon m (ρ₁ ++ ρ₂)
interp-shift-mon (Atom a) v ρ₁ ρ₂ = interp-shift-atm a v ρ₁ ρ₂
interp-shift-mon Read v ρ₁ ρ₂ = refl
interp-shift-mon (Sub a₁ a₂) v ρ₁ ρ₂ 
    rewrite interp-shift-atm a₁ v ρ₁ ρ₂
    | interp-shift-atm a₂ v ρ₁ ρ₂
    = refl
interp-shift-mon (Let m₁ m₂) v ρ₁ ρ₂ 
  rewrite interp-shift-mon m₁ v ρ₁ ρ₂
  = extensionality Goal
  where
  Goal : (s : StateR ℤ) →
          (interp-mon m₁ (ρ₁ ++ ρ₂) then
            (λ v₁ → interp-mon (shift-mon m₂ (suc (length ρ₁))) (v₁ ∷ ρ₁ ++ v ∷ ρ₂))) s
          ≡ (interp-mon m₁ (ρ₁ ++ ρ₂) then
             (λ v₁ → interp-mon m₂ (v₁ ∷ ρ₁ ++ ρ₂))) s
  Goal s
      with interp-mon m₁ (ρ₁ ++ ρ₂) s
  ... | nothing = refl
  ... | just (v₁ , s')
      rewrite interp-shift-mon m₂ v (v₁ ∷ ρ₁) ρ₂
      = refl

rco-correct-exp : ∀ (e : Exp) (ρ : Env)
  → interp-mon (rco e) ρ ≡ interp-exp e ρ
rco-correct-exp (Num x) ρ = refl
rco-correct-exp Read ρ = refl
rco-correct-exp (Sub e₁ e₂) ρ = extensionality Goal
  where
  Goal : (s : StateR ℤ) →
      (interp-mon (rco e₁) ρ then
       (λ v₁ → interp-mon (shift-mon (rco e₂) 0) (v₁ ∷ ρ) then
       (λ v₂ → return (v₁ - v₂)))) s
      ≡ (interp-exp e₁ ρ then
        (λ v₁ → interp-exp e₂ ρ then
        (λ v₂ → return (v₁ - v₂)))) s
  Goal s
      rewrite rco-correct-exp e₁ ρ
      with interp-exp e₁ ρ s
  ... | nothing = refl
  ... | just (v₁ , s')
      rewrite interp-shift-mon (rco e₂) v₁ [] ρ
      | rco-correct-exp e₂ ρ
      = refl
rco-correct-exp (Var i₁) ρ = refl
rco-correct-exp (Let e₁ e₂) ρ = extensionality Goal
  where
  Goal : (s : StateR ℤ) →
        (interp-mon (rco e₁) ρ then (λ v₁ → interp-mon (rco e₂) (v₁ ∷ ρ))) s
      ≡ (interp-exp e₁ ρ then (λ v₁ → interp-exp e₂ (v₁ ∷ ρ))) s
  Goal s
      rewrite rco-correct-exp e₁ ρ
      with interp-exp e₁ ρ s
  ... | nothing = refl
  ... | just (v₁ , s')
      rewrite rco-correct-exp e₂ (v₁ ∷ ρ)
      = refl

rco-correct : ∀ (e : Exp) (s : StateR ℤ)
  → interp-LMonVar (rco e) s ≡ interp-LVar e s 
rco-correct e s rewrite rco-correct-exp e [] = refl

--------------- Proof of correctness for Explicate Control ------------------------

interp-shift-exp : ∀ (e : CExp) (v : ℤ) (ρ₁ : Env) (ρ₂ : Env)
  → interp-CExp (shift-exp e (length ρ₁)) (ρ₁ ++ (v ∷ ρ₂))
    ≡ interp-CExp e (ρ₁ ++ ρ₂)
interp-shift-exp (Atom atm) v ρ₁ ρ₂ = interp-shift-atm atm v ρ₁ ρ₂
interp-shift-exp Read v ρ₁ ρ₂ = refl
interp-shift-exp (Sub a₁ a₂) v ρ₁ ρ₂ = extensionality Goal
  where
  Goal : (s : StateR ℤ) →
      interp-CExp (shift-exp (Sub a₁ a₂) (length ρ₁)) (ρ₁ ++ (v ∷ ρ₂)) s
    ≡ interp-CExp (Sub a₁ a₂) (ρ₁ ++ ρ₂) s
  Goal s
    rewrite interp-shift-atm a₁ v ρ₁ ρ₂ | interp-shift-atm a₂ v ρ₁ ρ₂
      with interp-atm a₁ (ρ₁ ++ ρ₂) s
  ... | nothing = refl
  ... | just (v₁ , s1)
      with interp-atm a₂ (ρ₁ ++ ρ₂) s1
  ... | nothing = refl
  ... | just (v₂ , s2) = refl

interp-shift-tail : ∀ (c : CTail) (v : ℤ) (ρ₁ : Env) (ρ₂ : Env)
  → interp-tail (shift-tail c (length ρ₁)) (ρ₁ ++ (v ∷ ρ₂))
    ≡ interp-tail c (ρ₁ ++ ρ₂)
interp-shift-tail (Return e) v ρ₁ ρ₂ = interp-shift-exp e v ρ₁ ρ₂
interp-shift-tail (Let e c) v ρ₁ ρ₂ = extensionality Goal
  where
  Goal : (s : StateR ℤ) →
       interp-tail (shift-tail (Let e c) (length ρ₁)) (ρ₁ ++ (v ∷ ρ₂)) s
     ≡ interp-tail (Let e c) (ρ₁ ++ ρ₂) s
  Goal s
      rewrite interp-shift-exp e v ρ₁ ρ₂
      with interp-CExp e (ρ₁ ++ ρ₂) s
  ... | nothing = refl
  ... | just (v₁ , s')
      rewrite interp-shift-tail c v (v₁ ∷ ρ₁) ρ₂
      = refl
      
explicate-let-correct : ∀ (m : Mon) (c : CTail) (ρ : Env)
   → interp-tail (explicate-let m c) ρ
     ≡ (interp-mon m ρ then (λ v₁ → interp-tail c (v₁ ∷ ρ)))
explicate-let-correct (Let m₁ m₂) c ρ = extensionality Goal
  where
  Goal : (s : StateR ℤ)
   → interp-tail (explicate-let (Let m₁ m₂) c) ρ s
     ≡ (interp-mon (Let m₁ m₂) ρ then (λ v₁ → interp-tail c (v₁ ∷ ρ))) s
  Goal s
      rewrite explicate-let-correct m₁ (explicate-let m₂ (shift-tail c 1)) ρ
      with interp-mon m₁ ρ s
  ... | nothing = refl
  ... | just (v₁ , s1)
      rewrite explicate-let-correct m₂ (shift-tail c 1) (v₁ ∷ ρ)
      with interp-mon m₂ (v₁ ∷ ρ) s1
  ... | nothing = refl
  ... | just (v₂ , s2)
      rewrite interp-shift-tail c v₁ [ v₂ ] ρ 
      = refl
explicate-let-correct (Atom a) c ρ = refl
explicate-let-correct Read c ρ = refl
explicate-let-correct (Sub a₁ a₂) m₂ ρ = refl

explicate-correct-mon : ∀ (m : Mon) (ρ : Env)
   → interp-tail (explicate m) ρ ≡ interp-mon m ρ
explicate-correct-mon (Atom x) ρ = refl
explicate-correct-mon Read ρ = refl
explicate-correct-mon (Sub a₁ a₂) ρ = refl
explicate-correct-mon (Let m₁ m₂) ρ = extensionality Goal
    where
  Goal : (s : StateR ℤ)
    → interp-tail (explicate (Let m₁ m₂)) ρ s ≡ interp-mon (Let m₁ m₂) ρ s
  Goal s
      rewrite explicate-let-correct m₁ (explicate m₂) ρ
      with interp-mon m₁ ρ s
  ... | nothing = refl
  ... | just (v₁ , s1)
      rewrite explicate-correct-mon m₂ (v₁ ∷ ρ)
      = refl

explicate-correct : ∀ (m : Mon) (s : StateR ℤ)
  → interp-CVar (explicate m) s ≡ interp-LMonVar m s
explicate-correct m s rewrite explicate-correct-mon m [] = refl

--------------- Proof of correctness for Lower Lets ------------------------

interp-shifts-atm : ∀ (a : Atm) (ρ₁ ρ₂ ρ₃ : Env)
  → interp-atm (shifts-atm a (length ρ₁) (length ρ₂)) (ρ₁ ++ ρ₂ ++ ρ₃)
  ≡ interp-atm a (ρ₁ ++ ρ₃)
interp-shifts-atm a ρ₁ ρ₂ ρ₃ = extensionality (Goal a)
  where
  Goal : (a : Atm )(s : StateR ℤ)
       → interp-atm (shifts-atm a (length ρ₁) (length ρ₂)) (ρ₁ ++ ρ₂ ++ ρ₃) s
        ≡ interp-atm a (ρ₁ ++ ρ₃) s
  Goal (Num i) s = refl
  Goal (Var x) s
      with length ρ₁ ≤ᵇ x in lt
  ... | true
      with m≤n⇒-+ (length ρ₁) x (≤ᵇ⇒≤ (length ρ₁) x (eq-true-top lt))
  ... | k , eq
      rewrite sym eq
      | sym (+-assoc (length ρ₂) (length ρ₁) k)
      | +-comm (length ρ₂) (length ρ₁)
      | (+-assoc (length ρ₁) (length ρ₂) k)
      | nth-++-+ ρ₁ (ρ₂ ++ ρ₃) (length ρ₂ + k)
      | nth-++-+ ρ₂ ρ₃ k
      | nth-++-+ ρ₁ ρ₃ k
      = refl
  Goal (Var x) s | false
      rewrite nth-++-< ρ₁ (ρ₂ ++ ρ₃) x (≰⇒> λ x₁ → (eq-false-not-top lt) (≤⇒≤ᵇ x₁))
      | nth-++-< ρ₁ ρ₃ x (≰⇒> λ x₁ → (eq-false-not-top lt) (≤⇒≤ᵇ x₁))
      = refl

interp-shifts-exp : ∀ (e : CExp) (ρ₁ ρ₂ ρ₃ : Env)
  → interp-CExp (shifts-exp e (length ρ₁) (length ρ₂)) (ρ₁ ++ ρ₂ ++ ρ₃)
  ≡ interp-CExp e (ρ₁ ++ ρ₃)
interp-shifts-exp (Atom a) ρ₁ ρ₂ ρ₃ = interp-shifts-atm a ρ₁ ρ₂ ρ₃
interp-shifts-exp Read ρ₁ ρ₂ ρ₃ = refl
interp-shifts-exp (Sub a₁ a₂) ρ₁ ρ₂ ρ₃ = extensionality Goal
  where
  Goal : (s : StateR ℤ)
    → interp-CExp (shifts-exp (Sub a₁ a₂) (length ρ₁) (length ρ₂)) (ρ₁ ++ ρ₂ ++ ρ₃) s
      ≡ interp-CExp (Sub a₁ a₂) (ρ₁ ++ ρ₃) s
  Goal s
       rewrite interp-shifts-atm a₁ ρ₁ ρ₂ ρ₃
       | interp-shifts-atm a₂ ρ₁ ρ₂ ρ₃
       with interp-atm a₁ (ρ₁ ++ ρ₃) s
  ... | nothing = refl
  ... | just (v₁ , s2)
       with interp-atm a₂ (ρ₁ ++ ρ₃) s2
  ... | nothing = refl
  ... | just (v₂ , s3)
       = refl

lower-tail-correct-aux : ∀ (c : CTail) (ρ₁ ρ₂ : Env)
  → proj₂ (lower-tail c) ≡ length ρ₁
  → interp-tail c ρ₂ ≡ interp-stmt (proj₁ (lower-tail c)) (ρ₁ ++ ρ₂)
lower-tail-correct-aux (Return e) [] ρ₂ eq = refl
lower-tail-correct-aux (Let e c) ρ₁ ρ₂ eq = extensionality Goal
  where
  Goal : (s : StateR ℤ)
    → (interp-tail (Let e c) ρ₂) s
    ≡ interp-stmt (proj₁ (lower-tail (Let e c))) (ρ₁ ++ ρ₂) s
  Goal s 
      rewrite eq | interp-shifts-exp e [] ρ₁ ρ₂
      with interp-CExp e ρ₂ s
  ... | nothing = refl
  ... | just (v , s1)
      rewrite +-comm 1 (proj₂ (lower-tail c))
      with ++-length-+-1 ρ₁ (proj₂ (lower-tail c)) (sym eq)
  ... | r11 , v₂ , refl , eq2
      rewrite ++-assoc r11 (v₂ ∷ []) ρ₂
      | sym eq2
      | update-correct r11 ρ₂ v₂ v
      | lower-tail-correct-aux c r11 (v ∷ ρ₂) (sym eq2)
      = refl

lower-tail-correct : ∀ (c : CTail) (ρ : Env)
  → proj₂ (lower-tail c) ≡ length ρ
  → interp-tail c [] ≡ interp-stmt (proj₁ (lower-tail c)) ρ
lower-tail-correct c ρ prem
    with lower-tail-correct-aux c ρ [] prem
... | eq rewrite ++-identityʳ ρ = eq

lower-lets-correct : ∀ (c : CTail) (s : StateR ℤ)
  → interp-CVar c s ≡ interp-prog (lower-lets c) s
lower-lets-correct c s 
  rewrite lower-tail-correct c (replicate (lower-tail c .proj₂) 0ℤ)
              (sym (length-replicate (proj₂ (lower-tail c))))
  = refl

--------------- Proof of correctness for Select Instructions ------------------------

-- select-inst-correct : ∀ (p : CProg)
--   → interp-x86-var (select-inst p) ≡ interp-prog p
-- select-inst-correct p = ?
