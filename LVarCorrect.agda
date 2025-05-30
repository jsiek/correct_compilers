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
open import Data.List.Properties using (++-assoc; length-replicate; ++-identityʳ)
open import Data.Maybe
open import Relation.Binary.PropositionalEquality
   using (_≡_; refl; trans; sym; cong; cong-app)
open import Agda.Builtin.Bool
open import Relation.Nullary.Negation.Core using (¬_; contradiction)
open import Function.Base using (case_of_; case_returning_of_)

open import Reader
open import Utilities
open import LVar


--------------- Proof of correctness for RCO ------------------------

interp-shift-atm : ∀ (a : Atm) (v : ℤ) (ρ₁ ρ₂ : Env ℤ)
  → interp-atm (shift-atm a (length ρ₁)) (ρ₁ ++ v ∷ ρ₂) 
    ≡ interp-atm a (ρ₁ ++ ρ₂) 
interp-shift-atm (Num n) v ρ₁ ρ₂ = refl
interp-shift-atm (Var x) v ρ₁ ρ₂ = nth-++-shift-var ρ₁ ρ₂ v x

interp-shift-mon : ∀ (m : Mon) (v : ℤ) (ρ₁ ρ₂ : Env ℤ)
  → interp-mon (shift-mon m (length ρ₁)) (ρ₁ ++ (v ∷ ρ₂))
    ≡ interp-mon m (ρ₁ ++ ρ₂)
interp-shift-mon (Atom a) v ρ₁ ρ₂ rewrite interp-shift-atm a v ρ₁ ρ₂ = refl
interp-shift-mon Read v ρ₁ ρ₂ = refl
interp-shift-mon (Sub a₁ a₂) v ρ₁ ρ₂ 
    rewrite interp-shift-atm a₁ v ρ₁ ρ₂
    | interp-shift-atm a₂ v ρ₁ ρ₂
    = refl
interp-shift-mon (Let m₁ m₂) v ρ₁ ρ₂ 
  = extensionality Goal
  where
  Goal : (s : Inputs) →
     interp-mon (shift-mon (Let m₁ m₂) (length ρ₁)) (ρ₁ ++ (v ∷ ρ₂)) s
     ≡ interp-mon (Let m₁ m₂) (ρ₁ ++ ρ₂) s
  Goal s
      rewrite interp-shift-mon m₁ v ρ₁ ρ₂
      with interp-mon m₁ (ρ₁ ++ ρ₂) s
  ... | nothing = refl
  ... | just (v₁ , s')
      rewrite interp-shift-mon m₂ v (v₁ ∷ ρ₁) ρ₂
      = refl

rco-correct-exp : ∀ (e : Exp) (ρ : Env ℤ)
  → interp-mon (rco e) ρ ≡ interp-exp e ρ
rco-correct-exp (Num x) ρ = refl
rco-correct-exp Read ρ = refl
rco-correct-exp (Sub e₁ e₂) ρ = extensionality Goal
  where
  Goal : (s : Inputs) →
         interp-mon (rco (Sub e₁ e₂)) ρ s ≡ interp-exp (Sub e₁ e₂) ρ s
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
  Goal : (s : Inputs) →
         interp-mon (rco (Let e₁ e₂)) ρ s ≡ interp-exp (Let e₁ e₂) ρ s  
  Goal s
      rewrite rco-correct-exp e₁ ρ
      with interp-exp e₁ ρ s
  ... | nothing = refl
  ... | just (v₁ , s')
      rewrite rco-correct-exp e₂ (v₁ ∷ ρ)
      = refl

rco-correct : ∀ (e : Exp) (s : Inputs)
  → interp-LMonVar (rco e) s ≡ interp-LVar e s 
rco-correct e s rewrite rco-correct-exp e [] = refl

--------------- Proof of correctness for Explicate Control -------------------

interp-shift-exp : ∀ (e : CExp) (v : ℤ) (ρ₁ ρ₂ : Env ℤ)
  → interp-CExp (shift-exp e (length ρ₁)) (ρ₁ ++ (v ∷ ρ₂))
    ≡ interp-CExp e (ρ₁ ++ ρ₂)
interp-shift-exp (Atom atm) v ρ₁ ρ₂ rewrite interp-shift-atm atm v ρ₁ ρ₂ = refl
interp-shift-exp Read v ρ₁ ρ₂ = refl
interp-shift-exp (Sub a₁ a₂) v ρ₁ ρ₂ 
    rewrite interp-shift-atm a₁ v ρ₁ ρ₂ | interp-shift-atm a₂ v ρ₁ ρ₂
    with interp-atm a₁ (ρ₁ ++ ρ₂) 
... | nothing = refl
... | just v₁
    with interp-atm a₂ (ρ₁ ++ ρ₂)
... | nothing = refl
... | just v₂ = refl

interp-shift-tail : ∀ (c : CTail) (v : ℤ) (ρ₁ ρ₂ : Env ℤ)
  → interp-tail (shift-tail c (length ρ₁)) (ρ₁ ++ (v ∷ ρ₂))
    ≡ interp-tail c (ρ₁ ++ ρ₂)
interp-shift-tail (Return e) v ρ₁ ρ₂ = interp-shift-exp e v ρ₁ ρ₂
interp-shift-tail (Let e c) v ρ₁ ρ₂ = extensionality Goal
  where
  Goal : (s : Inputs) →
       interp-tail (shift-tail (Let e c) (length ρ₁)) (ρ₁ ++ (v ∷ ρ₂)) s
     ≡ interp-tail (Let e c) (ρ₁ ++ ρ₂) s
  Goal s
      rewrite interp-shift-exp e v ρ₁ ρ₂
      with interp-CExp e (ρ₁ ++ ρ₂) s
  ... | nothing = refl
  ... | just (v₁ , s')
      rewrite interp-shift-tail c v (v₁ ∷ ρ₁) ρ₂
      = refl
      
explicate-let-correct : ∀ (m : Mon) (c : CTail) (ρ : Env ℤ)
   → interp-tail (explicate-let m c) ρ
     ≡ (interp-mon m ρ then (λ v₁ → interp-tail c (v₁ ∷ ρ)))
explicate-let-correct (Let m₁ m₂) c ρ = extensionality Goal
  where
  Goal : (s : Inputs)
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

explicate-correct-mon : ∀ (m : Mon) (ρ : Env ℤ)
   → interp-tail (explicate m) ρ ≡ interp-mon m ρ
explicate-correct-mon (Atom x) ρ = refl
explicate-correct-mon Read ρ = refl
explicate-correct-mon (Sub a₁ a₂) ρ = refl
explicate-correct-mon (Let m₁ m₂) ρ = extensionality Goal
    where
  Goal : (s : Inputs)
    → interp-tail (explicate (Let m₁ m₂)) ρ s ≡ interp-mon (Let m₁ m₂) ρ s
  Goal s
      rewrite explicate-let-correct m₁ (explicate m₂) ρ
      with interp-mon m₁ ρ s
  ... | nothing = refl
  ... | just (v₁ , s1)
      rewrite explicate-correct-mon m₂ (v₁ ∷ ρ)
      = refl

explicate-correct : ∀ (m : Mon) (s : Inputs)
  → interp-CVar (explicate m) s ≡ interp-LMonVar m s
explicate-correct m s rewrite explicate-correct-mon m [] = refl

--------------- Proof of correctness for Lower Lets ------------------------

interp-shifts-atm : ∀ (a : Atm) (ρ₁ ρ₂ ρ₃ : Env ℤ)
  → interp-atm (shifts-atm a (length ρ₁) (length ρ₂)) (ρ₁ ++ ρ₂ ++ ρ₃)
  ≡ interp-atm a (ρ₁ ++ ρ₃)
interp-shifts-atm (Num x) ρ₁ ρ₂ ρ₃ = refl
interp-shifts-atm (Var x) ρ₁ ρ₂ ρ₃
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
interp-shifts-atm (Var x) ρ₁ ρ₂ ρ₃ | false
    rewrite nth-++-< ρ₁ (ρ₂ ++ ρ₃) x (≰⇒> λ x₁ → (eq-false-not-top lt) (≤⇒≤ᵇ x₁))
    | nth-++-< ρ₁ ρ₃ x (≰⇒> λ x₁ → (eq-false-not-top lt) (≤⇒≤ᵇ x₁))
    = refl

interp-shifts-exp : ∀ (e : CExp) (ρ₁ ρ₂ ρ₃ : Env ℤ)
  → interp-CExp (shifts-exp e (length ρ₁) (length ρ₂)) (ρ₁ ++ ρ₂ ++ ρ₃)
  ≡ interp-CExp e (ρ₁ ++ ρ₃)
interp-shifts-exp (Atom a) ρ₁ ρ₂ ρ₃ rewrite interp-shifts-atm a ρ₁ ρ₂ ρ₃ = refl
interp-shifts-exp Read ρ₁ ρ₂ ρ₃ = refl
interp-shifts-exp (Sub a₁ a₂) ρ₁ ρ₂ ρ₃ = extensionality Goal
  where
  Goal : (s : Inputs)
    → interp-CExp (shifts-exp (Sub a₁ a₂) (length ρ₁) (length ρ₂)) (ρ₁ ++ ρ₂ ++ ρ₃) s
      ≡ interp-CExp (Sub a₁ a₂) (ρ₁ ++ ρ₃) s
  Goal s
       rewrite interp-shifts-atm a₁ ρ₁ ρ₂ ρ₃
       | interp-shifts-atm a₂ ρ₁ ρ₂ ρ₃
       with interp-atm a₁ (ρ₁ ++ ρ₃)
  ... | nothing = refl
  ... | just v₁
       with interp-atm a₂ (ρ₁ ++ ρ₃)
  ... | nothing = refl
  ... | just v₂
       = refl

lower-tail-correct-aux : ∀ (c : CTail) (ρ₁ ρ₂ : Env ℤ)
  → proj₂ (lower-tail c) ≡ length ρ₁
  → interp-tail c ρ₂ ≡ interp-stmt (proj₁ (lower-tail c)) (ρ₁ ++ ρ₂)
lower-tail-correct-aux (Return e) [] ρ₂ eq = refl
lower-tail-correct-aux (Let e c) ρ₁ ρ₂ eq = extensionality Goal
  where
  Goal : (s : Inputs)
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

lower-tail-correct : ∀ (c : CTail) (ρ : Env ℤ)
  → proj₂ (lower-tail c) ≡ length ρ
  → interp-tail c [] ≡ interp-stmt (proj₁ (lower-tail c)) ρ
lower-tail-correct c ρ prem
    with lower-tail-correct-aux c ρ [] prem
... | eq rewrite ++-identityʳ ρ = eq

lower-lets-correct : ∀ (c : CTail) (s : Inputs)
  → interp-CVar c s ≡ interp-prog (lower-lets c) s
lower-lets-correct c s 
  rewrite lower-tail-correct c (replicate (lower-tail c .proj₂) 0ℤ)
              (sym (length-replicate (proj₂ (lower-tail c))))
  = refl

--------------- Proof of correctness for Select Instructions ------------------------


--- Well-formedness of CProg

data AtmOK : Atm → ℕ → Set where
  NumOK : ∀ {n : ℤ}{nv : ℕ} → AtmOK (Num n) nv 
  VarOK : ∀ {x nv : ℕ} → x < nv → AtmOK (Var x) nv 

data CExpOK : CExp → ℕ → Set where
  AtomOK : ∀{a : Atm}{nv : ℕ}
    → AtmOK a nv
    → CExpOK (Atom a) nv
  ReadOK : ∀{nv : ℕ} → CExpOK Read nv
  SubOK : ∀{a₁ a₂ : Atm}{nv : ℕ}
    → AtmOK a₁ nv
    → AtmOK a₂ nv
    → CExpOK (Sub a₁ a₂) nv

data CStmtOK : CStmt → ℕ → Set where
  ReturnOK : ∀{e : CExp}{nv : ℕ}
    → CExpOK e nv
    → CStmtOK (Return e) nv
  AssignOK : ∀{x : Id}{e : CExp}{s : CStmt}{nv : ℕ}
    → x < nv
    → CExpOK e nv
    → CStmtOK s nv 
    → CStmtOK (Assign x e s) nv

data CProgOK : CProg → Set where
  ProgramOK : ∀{s : CStmt}{nv : ℕ}
    → CStmtOK s nv
    → CProgOK (Program nv s)

--- Well-formedness of X86Var

data ArgOK : Arg → ℕ → ℕ → Set where
  NumOK : ∀ {n : ℤ}{nv nr : ℕ} → ArgOK (Num n) nv nr
  RegOK : ∀ {x nv nr : ℕ} → x < nr → ArgOK (Reg x) nv nr
  VarOK : ∀ {x nv nr : ℕ} → x < nv → ArgOK (Var x) nv nr

data DestOK : Dest → ℕ → ℕ → Set where
  RegOK : ∀ {x nv nr : ℕ} → x < nr → DestOK (Reg x) nv nr
  VarOK : ∀ {x nv nr : ℕ} → x < nv → DestOK (Var x) nv nr

data InstOK : Inst → ℕ → ℕ → Set where
  MovQOK : ∀ {src : Arg}{dst : Dest}{nv nr : ℕ}
    → ArgOK src nv nr
    → DestOK dst nv nr
    → InstOK (MovQ src dst) nv nr
  SubQOK : ∀ {src : Arg}{dst : Dest}{nv nr : ℕ}
    → ArgOK src nv nr
    → DestOK dst nv nr
    → InstOK (SubQ src dst) nv nr
  ReadIntOK : ∀{nv nr : ℕ}
    → DestOK (Reg rax) nv nr
    → InstOK ReadInt nv nr

InstsOK : List Inst → ℕ → ℕ → Set
InstsOK [] nv nr = ⊤
InstsOK (i ∷ is) nv nr = InstOK i nv nr × InstsOK is nv nr

X86VarOK : X86Var → ℕ → Set
X86VarOK (Program nv is) nr = InstsOK is nv nr

OutSyncExp : Maybe (ℤ × Inputs) → Maybe StateX86 → Dest → Set
OutSyncExp (just (v , inputs)) (just (inputs' , regs , ρ)) (Var x) =
  inputs ≡ inputs' × nth ρ x ≡ just v
OutSyncExp (just (v , inputs)) (just (inputs' , regs , ρ)) (Reg x) = 
  inputs ≡ inputs' × nth regs x ≡ just v
OutSyncExp (just x) nothing dest = ⊥
OutSyncExp nothing (just x) dest = ⊥
OutSyncExp nothing nothing dest = ⊤

OutSync : Maybe (ℤ × Inputs) → Maybe StateX86 → Set
OutSync (just (v , inputs)) (just (inputs' , regs , ρ)) = 
  inputs ≡ inputs' × nth regs rax ≡ just v
OutSync (just x) nothing = ⊥
OutSync nothing (just x) = ⊥
OutSync nothing nothing = ⊤

to-arg-correct : ∀ (a : Atm) (ρ : Env ℤ) (inputs : Inputs) (regs : List ℤ) 
  → (interp-atm a ρ) ≡ (interp-arg (to-arg a) (inputs , regs , ρ))
to-arg-correct (Num n) ρ inputs regs = refl
to-arg-correct (Var x) ρ inputs regs
    with nth ρ x
... | nothing = refl
... | just v = refl

seq : (StateX86 → Maybe StateX86) → (StateX86 → Maybe StateX86)
    → StateX86 → Maybe StateX86
seq M₁ M₂ s1
    with M₁ s1
... | nothing = nothing
... | just s2 = M₂ s2

interp-insts-++ : ∀(xs ys : List Inst) (s : StateX86)
  → interp-insts (xs ++ ys) s ≡ seq (interp-insts xs) (interp-insts ys) s
interp-insts-++ [] ys s = refl
interp-insts-++ (x ∷ xs) ys s0
    with interp-inst x s0
... | nothing = refl
... | just s1
    rewrite interp-insts-++ xs ys s1 = refl

update-length-lemma : ∀ (x y : ℕ) (v : ℤ) (ρ : List ℤ)
  → x < length ρ
  → x < length (update ρ y v)
update-length-lemma x y v ρ xlt 
  rewrite update-length ρ y v = xlt

update-length-lemma2 : ∀ (x y : ℕ) (v : ℤ) (ρ : List ℤ)
  → x < length (update ρ y v)
  → x < length ρ
update-length-lemma2 x y v ρ xlt 
  rewrite update-length ρ y v = xlt


write-var-update : ∀(e : CExp) (x : Id) (inputs inputs' : Inputs) (regs regs' ρ ρ' : List ℤ) (v : ℤ)
  → rax < length regs
  → x < length ρ
  → interp-insts (select-exp e (Var x)) (inputs , regs , ρ) ≡ just (inputs' , regs' , ρ')
  → nth ρ' x ≡ just v
  → ρ' ≡ update ρ x v
write-var-update (Atom (Num n)) x inputs inputs' regs regs' ρ ρ' v rax-lt x-lt refl eq
    rewrite nth-update ρ x n x-lt
    with eq
... | refl = refl
write-var-update (Atom (Var y)) x inputs inputs' regs regs' ρ ρ' v rax-lt x-lt eq1 eq2
    with nth ρ y
... | just v'
    with eq1
... | refl
    rewrite nth-update ρ x v' x-lt
    with eq2
... | refl = refl
write-var-update Read x (i , stream) inputs' regs regs' ρ ρ' v rax-lt x-lt eq1 eq2
    with nth (update regs rax (stream i)) rax in eq3
... | just v'
    rewrite nth-update regs rax (stream i) rax-lt
    with eq1 | eq3
... | refl | refl
    rewrite nth-update ρ x (stream i) x-lt
    with eq2
... | refl = refl
write-var-update (Sub a₁ a₂) x inputs inputs' regs regs' ρ ρ' v rax-lt x-lt eq1 eq2
    with interp-arg (to-arg a₁) (inputs , regs , ρ)
... | just v₁
    with interp-arg (to-arg a₂) (inputs , update regs 0 v₁ , ρ)
... | just v₂
    rewrite nth-update regs rax v₁ rax-lt
    with nth (update (update regs 0 v₁) 0 (v₁ - v₂)) 0 in eq
... | just v'
    with eq1
... | refl 
    rewrite nth-update ρ x v' x-lt
    with eq2
... | refl = refl


select-exp-correct : ∀ (e : CExp) (ρ : Env ℤ) (inputs : Inputs) (dest : Dest) (regs : List ℤ)
  → DestOK dest (length ρ) (length regs)
  → DestOK (Reg rax) (length ρ) (length regs)
  → OutSyncExp (interp-CExp e ρ inputs) (interp-insts (select-exp e dest) (inputs , regs , ρ)) dest
select-exp-correct (Atom a) ρ inputs dest regs destOk raxOk
    rewrite to-arg-correct a ρ inputs regs 
    with interp-arg (to-arg a) (inputs , regs , ρ)
... | nothing = tt
... | just v'
    with write dest v' (inputs , regs , ρ) | dest
... | (inputs' , regs' , ρ') | Var x
    with destOk
... | VarOK lt = refl , nth-update ρ x v' lt
select-exp-correct (Atom a) ρ inputs dest regs destOk raxOk
    | just v' | (inputs' , regs' , ρ') | Reg x
    with destOk
... | RegOK lt = refl , nth-update regs x v' lt
select-exp-correct Read ρ (i , stream) dest regs destOk (RegOK lt)
  rewrite nth-update regs rax (stream i) lt
  with dest | destOk
... | Reg x | RegOK xlt rewrite nth-update (update regs 0 (stream i)) x (stream i) (update-length-lemma x 0 (stream i) regs xlt) = refl , refl
... | Var x | VarOK xlt = refl , nth-update ρ x (stream i) xlt
select-exp-correct (Sub a₁ a₂) ρ inputs dest regs destOk (RegOK rax-lt)
    rewrite to-arg-correct a₁ ρ inputs regs
    with interp-arg (to-arg a₁) (inputs , regs , ρ)
... | nothing = tt
... | just v₁
    rewrite to-arg-correct a₂ ρ inputs (update regs 0 v₁)
    with interp-arg (to-arg a₂) (inputs , update regs 0 v₁ , ρ)
... | nothing = tt
... | just v₂
    rewrite nth-update (update regs 0 v₁) 0 (v₁ - v₂) (update-length-lemma 0 0 v₁ regs rax-lt)
    | nth-update regs 0 v₁ rax-lt 
    with dest | destOk
... | Var x | VarOK xlt
    rewrite nth-update (update regs 0 v₁) 0 (v₁ - v₂) (update-length-lemma 0 0 v₁ regs rax-lt)
    | nth-update ρ x (v₁ - v₂) xlt
    = refl , refl
... | Reg x | RegOK xlt
    with update-length-lemma x 0 v₁ regs xlt
... | xlt2
--   x < length (update regs 0 v₁)
    with update-length-lemma x 0 (v₁ - v₂) (update regs 0 v₁) xlt2
... | xlt3    
--   x < length (update (update regs 0 v₁) 0 (v₁ - v₂))
    rewrite nth-update (update regs 0 v₁) 0 (v₁ - v₂) (update-length-lemma 0 0 v₁ regs rax-lt)
    | nth-update (update (update regs 0 v₁) 0 (v₁ Data.Integer.+ - v₂)) x (v₁ - v₂) xlt3
    = refl , refl

Evolved : StateX86 → StateX86 → Set
Evolved ((i , stream) , regs , ρ) ((i' , stream') , regs' , ρ') =
  stream ≡ stream' × i ≤ i' × length regs ≡ length regs' × length ρ ≡ length ρ'

write-evolved : ∀ (d : Dest) (v : ℤ) (s : StateX86)
  → Evolved s (write d v s)
write-evolved (Var x) v (inputs , regs , ρ) rewrite update-length ρ x v = refl , ≤-refl , refl , refl
write-evolved (Reg x) v (inputs , regs , ρ) rewrite update-length regs x v = refl , ≤-refl , refl , refl

interp-inst-evolved : ∀ (i : Inst) (s s' : StateX86)
  → interp-inst i s ≡ just s'
  → Evolved s s'
interp-inst-evolved (MovQ a d) s s' interp-eq
    with interp-arg a s | interp-eq
... | just v | refl = write-evolved d v s
interp-inst-evolved (SubQ a d) s s' interp-eq
    with interp-arg a s
... | just v₁
    with interp-dest d s | interp-eq
... | just v₂ | refl = write-evolved d (v₂ - v₁) s
interp-inst-evolved ReadInt (inputs , regs , ρ) (inputs' , regs' , ρ') refl
  rewrite update-length regs rax ((inputs .proj₂ (inputs .proj₁))) =
  refl , n≤1+n _  , refl , refl

Evolved-trans : ∀(s1 s2 s3 : StateX86)
  → Evolved s1 s2
  → Evolved s2 s3
  → Evolved s1 s3
Evolved-trans s1 s2 s3 (a , b , c , d) (e , f , g , h) =
  trans a e , ≤-trans b f , trans c g , trans d h

interp-insts-evolved : ∀ (is : List Inst) (s s' : StateX86)
  → interp-insts is s ≡ just s'
  → Evolved s s'
interp-insts-evolved [] s s' refl = refl , ≤-refl , refl , refl
interp-insts-evolved (i ∷ is) s s' eq2
    with interp-inst i s in eq1
... | just s2 =
    let E1 = interp-inst-evolved i s s2 eq1 in
    let IH = interp-insts-evolved is s2 s' eq2 in
    Evolved-trans s s2 s' E1 IH

select-stmt-correct : ∀ (s : CStmt) (ρ : Env ℤ) (inputs : Inputs) (regs : List ℤ)
  → CStmtOK s (length ρ)
  → DestOK (Reg rax) (length ρ) (length regs)
  → OutSync (interp-stmt s ρ inputs) (interp-insts (select-stmt s) (inputs , regs , ρ))
select-stmt-correct (Return e) ρ inputs regs sOk raxOk
    with interp-CExp e ρ inputs
    | interp-insts (select-exp e (Reg rax)) (inputs , regs , ρ)
    | select-exp-correct e ρ inputs (Reg rax) regs raxOk raxOk
... | just v | just (inputs' , regs' , ρ') | refl , eq = refl , eq
... | nothing | nothing | zz = tt
select-stmt-correct (Assign x e rest) ρ inputs regs (AssignOK xlt eOk sOk) raxOk
    rewrite interp-insts-++ (select-exp e (Var x)) (select-stmt rest) (inputs , regs , ρ)
    with interp-CExp e ρ inputs
    | interp-insts (select-exp e (Var x)) (inputs , regs , ρ) in eq
    | select-exp-correct e ρ inputs (Var x) regs (VarOK xlt) raxOk
... | nothing | nothing | cc = tt
... | just (v , inputs') | just (inputs' , regs' , ρ') | refl , nth-ρx-v
    rewrite sym (update-length ρ x v )
    with interp-insts-evolved (select-exp e (Var x)) (inputs , regs , ρ)  (inputs' , regs' , ρ') eq
... | a , b , reg-len , var-len
    with raxOk
... | RegOK rax-lt
    rewrite write-var-update e x inputs inputs' regs regs' ρ ρ' v rax-lt (update-length-lemma2 x x v ρ xlt) eq nth-ρx-v 
    | reg-len
    =
    select-stmt-correct rest (update ρ x v) inputs' regs' sOk (RegOK rax-lt)

select-inst-correct : ∀ (p : CProg)
  → CProgOK p 
  → interp-x86-var (select-inst p) ≡ interp-prog p
select-inst-correct (Program n s) (ProgramOK sok) = extensionality Goal
  where
  sok2 : CStmtOK s (length (replicate n 0ℤ))
  sok2 rewrite length-replicate n {0ℤ} = sok

  Goal : (inputs : Inputs)
    → run-x86 (interp-insts (select-stmt s)) n inputs
    ≡ run (interp-stmt s (replicate n 0ℤ)) inputs
  Goal inputs
      with interp-insts (select-stmt s) (inputs , [ 0ℤ ] , replicate n 0ℤ)
      | interp-stmt s (replicate n (ℤ.pos 0)) inputs
      | select-stmt-correct s (replicate n 0ℤ) inputs [ 0ℤ ] sok2 (RegOK (s≤s _≤_.z≤n))
  ... | nothing | just (inputs' , regs' , ρ') | ()
  ... | nothing | nothing | sync = refl
  ... | just (inputs' , regs' , ρ') | just (v , inputs'') | refl , eq = eq
