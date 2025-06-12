module LVarSelectCorrect where

open import Agda.Builtin.Unit
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using ()
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; _≤ᵇ_; _∸_; _+_; s≤s)
open import Data.Nat.Properties
open import Data.Product
open import Data.Sum
open import Data.Integer using (ℤ; -_; _-_; 0ℤ)
open import Data.List
open import Data.List.Properties using (++-assoc; length-replicate; ++-identityʳ; length-++)
open import Data.Maybe
open import Relation.Binary.PropositionalEquality
   using (_≡_; refl; trans; sym; cong; cong-app)
open import Agda.Builtin.Bool
open import Relation.Nullary.Negation.Core using (¬_; contradiction)
open import Function.Base using (case_of_; case_returning_of_)

open import Reader
open import Utilities
open import LVar

--------------- Proof of correctness for Select Instructions ------------------------


-- --- Well-formedness of CProg

-- data AtmOK : Atm → ℕ → Set where
--   NumOK : ∀ {n : ℤ}{nv : ℕ} → AtmOK (Num n) nv 
--   VarOK : ∀ {x nv : ℕ} → x < nv → AtmOK (Var x) nv 

-- data CExpOK : CExp → ℕ → Set where
--   AtomOK : ∀{a : Atm}{nv : ℕ}
--     → AtmOK a nv
--     → CExpOK (Atom a) nv
--   ReadOK : ∀{nv : ℕ} → CExpOK Read nv
--   SubOK : ∀{a₁ a₂ : Atm}{nv : ℕ}
--     → AtmOK a₁ nv
--     → AtmOK a₂ nv
--     → CExpOK (Sub a₁ a₂) nv

-- data CStmtOK : CStmt → ℕ → Set where
--   ReturnOK : ∀{e : CExp}{nv : ℕ}
--     → CExpOK e nv
--     → CStmtOK (Return e) nv
--   AssignOK : ∀{x : Id}{e : CExp}{s : CStmt}{nv : ℕ}
--     → x < nv
--     → CExpOK e nv
--     → CStmtOK s nv 
--     → CStmtOK (Assign x e s) nv

-- data CProgOK : CProg → Set where
--   ProgramOK : ∀{s : CStmt}{nv : ℕ}
--     → CStmtOK s nv
--     → CProgOK (Program nv s)

-- --- Well-formedness of X86Var

-- data ArgOK : Arg → ℕ → ℕ → Set where
--   NumOK : ∀ {n : ℤ}{nv nr : ℕ} → ArgOK (Num n) nv nr
--   RegOK : ∀ {x nv nr : ℕ} → x < nr → ArgOK (Reg x) nv nr
--   VarOK : ∀ {x nv nr : ℕ} → x < nv → ArgOK (Var x) nv nr

-- data DestOK : Dest → ℕ → ℕ → Set where
--   RegOK : ∀ {x nv nr : ℕ} → x < nr → DestOK (Reg x) nv nr
--   VarOK : ∀ {x nv nr : ℕ} → x < nv → DestOK (Var x) nv nr

-- data InstOK : Inst → ℕ → ℕ → Set where
--   MovQOK : ∀ {src : Arg}{dst : Dest}{nv nr : ℕ}
--     → ArgOK src nv nr
--     → DestOK dst nv nr
--     → InstOK (MovQ src dst) nv nr
--   SubQOK : ∀ {src : Arg}{dst : Dest}{nv nr : ℕ}
--     → ArgOK src nv nr
--     → DestOK dst nv nr
--     → InstOK (SubQ src dst) nv nr
--   ReadIntOK : ∀{nv nr : ℕ}
--     → DestOK (Reg rax) nv nr
--     → InstOK ReadInt nv nr

-- InstsOK : List Inst → ℕ → ℕ → Set
-- InstsOK [] nv nr = ⊤
-- InstsOK (i ∷ is) nv nr = InstOK i nv nr × InstsOK is nv nr

-- X86VarOK : X86Var → ℕ → Set
-- X86VarOK (Program nv is) nr = InstsOK is nv nr

-- OutSyncExp : Maybe (ℤ × Inputs) → Maybe StateX86 → Dest → Set
-- OutSyncExp (just (v , inputs)) (just (inputs' , regs , ρ)) (Var x) =
--   inputs ≡ inputs' × nth ρ x ≡ just v
-- OutSyncExp (just (v , inputs)) (just (inputs' , regs , ρ)) (Reg x) = 
--   inputs ≡ inputs' × nth regs x ≡ just v
-- OutSyncExp (just x) nothing dest = ⊥
-- OutSyncExp nothing (just x) dest = ⊥
-- OutSyncExp nothing nothing dest = ⊤

-- OutSync : Maybe (ℤ × Inputs) → Maybe StateX86 → Set
-- OutSync (just (v , inputs)) (just (inputs' , regs , ρ)) = 
--   inputs ≡ inputs' × nth regs rax ≡ just v
-- OutSync (just x) nothing = ⊥
-- OutSync nothing (just x) = ⊥
-- OutSync nothing nothing = ⊤

to-arg-correct : ∀ (a : Atm) (ρ : Env ℤ) (inputs : Inputs) (regs : List ℤ) 
  → (interp-atm a ρ) ≡ (interp-arg (to-arg a) (inputs , regs , ρ))
to-arg-correct (Num n) ρ inputs regs = refl
to-arg-correct (Var x) ρ inputs regs
    with nth ρ x
... | nothing = refl
... | just v = refl

-- seq : (StateX86 → Maybe StateX86) → (StateX86 → Maybe StateX86)
--     → StateX86 → Maybe StateX86
-- seq M₁ M₂ s1
--     with M₁ s1
-- ... | nothing = nothing
-- ... | just s2 = M₂ s2

-- interp-insts-++ : ∀(xs ys : List Inst) (s : StateX86)
--   → interp-insts (xs ++ ys) s ≡ seq (interp-insts xs) (interp-insts ys) s
-- interp-insts-++ [] ys s = refl
-- interp-insts-++ (x ∷ xs) ys s0
--     with interp-inst x s0
-- ... | nothing = refl
-- ... | just s1
--     rewrite interp-insts-++ xs ys s1 = refl

-- update-length-lemma : ∀ (x y : ℕ) (v : ℤ) (ρ : List ℤ)
--   → x < length ρ
--   → x < length (update ρ y v)
-- update-length-lemma x y v ρ xlt 
--   rewrite update-length ρ y v = xlt

-- update-length-lemma2 : ∀ (x y : ℕ) (v : ℤ) (ρ : List ℤ)
--   → x < length (update ρ y v)
--   → x < length ρ
-- update-length-lemma2 x y v ρ xlt 
--   rewrite update-length ρ y v = xlt


-- write-var-update : ∀(e : CExp) (x : Id) (inputs inputs' : Inputs) (regs regs' ρ ρ' : List ℤ) (v : ℤ)
--   → rax < length regs
--   → x < length ρ
--   → interp-insts (select-exp e (Var x)) (inputs , regs , ρ) ≡ just (inputs' , regs' , ρ')
--   → nth ρ' x ≡ just v
--   → ρ' ≡ update ρ x v
-- write-var-update (Atom (Num n)) x inputs inputs' regs regs' ρ ρ' v rax-lt x-lt refl eq
--     rewrite nth-update ρ x n x-lt
--     with eq
-- ... | refl = refl
-- write-var-update (Atom (Var y)) x inputs inputs' regs regs' ρ ρ' v rax-lt x-lt eq1 eq2
--     with nth ρ y
-- ... | just v'
--     with eq1
-- ... | refl
--     rewrite nth-update ρ x v' x-lt
--     with eq2
-- ... | refl = refl
-- write-var-update Read x (i , stream) inputs' regs regs' ρ ρ' v rax-lt x-lt eq1 eq2
--     with nth (update regs rax (stream i)) rax in eq3
-- ... | just v'
--     rewrite nth-update regs rax (stream i) rax-lt
--     with eq1 | eq3
-- ... | refl | refl
--     rewrite nth-update ρ x (stream i) x-lt
--     with eq2
-- ... | refl = refl
-- write-var-update (Sub a₁ a₂) x inputs inputs' regs regs' ρ ρ' v rax-lt x-lt eq1 eq2
--     with interp-arg (to-arg a₁) (inputs , regs , ρ)
-- ... | just v₁
--     with interp-arg (to-arg a₂) (inputs , update regs 0 v₁ , ρ)
-- ... | just v₂
--     rewrite nth-update regs rax v₁ rax-lt
--     with nth (update (update regs 0 v₁) 0 (v₁ - v₂)) 0 in eq
-- ... | just v'
--     with eq1
-- ... | refl 
--     rewrite nth-update ρ x v' x-lt
--     with eq2
-- ... | refl = refl


-- select-exp-correct : ∀ (e : CExp) (ρ : Env ℤ) (inputs : Inputs) (dest : Dest) (regs : List ℤ)
--   → DestOK dest (length ρ) (length regs)
--   → DestOK (Reg rax) (length ρ) (length regs)
--   → OutSyncExp (interp-CExp e ρ inputs) (interp-insts (select-exp e dest) (inputs , regs , ρ)) dest
-- select-exp-correct (Atom a) ρ inputs dest regs destOk raxOk
--     rewrite to-arg-correct a ρ inputs regs 
--     with interp-arg (to-arg a) (inputs , regs , ρ)
-- ... | nothing = tt
-- ... | just v'
--     with write dest v' (inputs , regs , ρ) | dest
-- ... | (inputs' , regs' , ρ') | Var x
--     with destOk
-- ... | VarOK lt = refl , nth-update ρ x v' lt
-- select-exp-correct (Atom a) ρ inputs dest regs destOk raxOk
--     | just v' | (inputs' , regs' , ρ') | Reg x
--     with destOk
-- ... | RegOK lt = refl , nth-update regs x v' lt
-- select-exp-correct Read ρ (i , stream) dest regs destOk (RegOK lt)
--   rewrite nth-update regs rax (stream i) lt
--   with dest | destOk
-- ... | Reg x | RegOK xlt rewrite nth-update (update regs 0 (stream i)) x (stream i) (update-length-lemma x 0 (stream i) regs xlt) = refl , refl
-- ... | Var x | VarOK xlt = refl , nth-update ρ x (stream i) xlt
-- select-exp-correct (Sub a₁ a₂) ρ inputs dest regs destOk (RegOK rax-lt)
--     rewrite to-arg-correct a₁ ρ inputs regs
--     with interp-arg (to-arg a₁) (inputs , regs , ρ)
-- ... | nothing = tt
-- ... | just v₁
--     rewrite to-arg-correct a₂ ρ inputs (update regs 0 v₁)
--     with interp-arg (to-arg a₂) (inputs , update regs 0 v₁ , ρ)
-- ... | nothing = tt
-- ... | just v₂
--     rewrite nth-update (update regs 0 v₁) 0 (v₁ - v₂) (update-length-lemma 0 0 v₁ regs rax-lt)
--     | nth-update regs 0 v₁ rax-lt 
--     with dest | destOk
-- ... | Var x | VarOK xlt
--     rewrite nth-update (update regs 0 v₁) 0 (v₁ - v₂) (update-length-lemma 0 0 v₁ regs rax-lt)
--     | nth-update ρ x (v₁ - v₂) xlt
--     = refl , refl
-- ... | Reg x | RegOK xlt
--     with update-length-lemma x 0 v₁ regs xlt
-- ... | xlt2
-- --   x < length (update regs 0 v₁)
--     with update-length-lemma x 0 (v₁ - v₂) (update regs 0 v₁) xlt2
-- ... | xlt3    
-- --   x < length (update (update regs 0 v₁) 0 (v₁ - v₂))
--     rewrite nth-update (update regs 0 v₁) 0 (v₁ - v₂) (update-length-lemma 0 0 v₁ regs rax-lt)
--     | nth-update (update (update regs 0 v₁) 0 (v₁ Data.Integer.+ - v₂)) x (v₁ - v₂) xlt3
--     = refl , refl

-- Evolved : StateX86 → StateX86 → Set
-- Evolved ((i , stream) , regs , ρ) ((i' , stream') , regs' , ρ') =
--   stream ≡ stream' × i ≤ i' × length regs ≡ length regs' × length ρ ≡ length ρ'

-- write-evolved : ∀ (d : Dest) (v : ℤ) (s : StateX86)
--   → Evolved s (write d v s)
-- write-evolved (Var x) v (inputs , regs , ρ) rewrite update-length ρ x v = refl , ≤-refl , refl , refl
-- write-evolved (Reg x) v (inputs , regs , ρ) rewrite update-length regs x v = refl , ≤-refl , refl , refl

-- interp-inst-evolved : ∀ (i : Inst) (s s' : StateX86)
--   → interp-inst i s ≡ just s'
--   → Evolved s s'
-- interp-inst-evolved (MovQ a d) s s' interp-eq
--     with interp-arg a s | interp-eq
-- ... | just v | refl = write-evolved d v s
-- interp-inst-evolved (SubQ a d) s s' interp-eq
--     with interp-arg a s
-- ... | just v₁
--     with interp-dest d s | interp-eq
-- ... | just v₂ | refl = write-evolved d (v₂ - v₁) s
-- interp-inst-evolved ReadInt (inputs , regs , ρ) (inputs' , regs' , ρ') refl
--   rewrite update-length regs rax ((inputs .proj₂ (inputs .proj₁))) =
--   refl , n≤1+n _  , refl , refl

-- Evolved-trans : ∀(s1 s2 s3 : StateX86)
--   → Evolved s1 s2
--   → Evolved s2 s3
--   → Evolved s1 s3
-- Evolved-trans s1 s2 s3 (a , b , c , d) (e , f , g , h) =
--   trans a e , ≤-trans b f , trans c g , trans d h

-- interp-insts-evolved : ∀ (is : List Inst) (s s' : StateX86)
--   → interp-insts is s ≡ just s'
--   → Evolved s s'
-- interp-insts-evolved [] s s' refl = refl , ≤-refl , refl , refl
-- interp-insts-evolved (i ∷ is) s s' eq2
--     with interp-inst i s in eq1
-- ... | just s2 =
--     let E1 = interp-inst-evolved i s s2 eq1 in
--     let IH = interp-insts-evolved is s2 s' eq2 in
--     Evolved-trans s s2 s' E1 IH

-- select-stmt-correct : ∀ (s : CStmt) (ρ : Env ℤ) (inputs : Inputs) (regs : List ℤ)
--   → CStmtOK s (length ρ)
--   → DestOK (Reg rax) (length ρ) (length regs)
--   → OutSync (interp-stmt s ρ inputs) (interp-insts (select-stmt s) (inputs , regs , ρ))
-- select-stmt-correct (Return e) ρ inputs regs sOk raxOk
--     with interp-CExp e ρ inputs
--     | interp-insts (select-exp e (Reg rax)) (inputs , regs , ρ)
--     | select-exp-correct e ρ inputs (Reg rax) regs raxOk raxOk
-- ... | just v | just (inputs' , regs' , ρ') | refl , eq = refl , eq
-- ... | nothing | nothing | zz = tt
-- select-stmt-correct (Assign x e rest) ρ inputs regs (AssignOK xlt eOk sOk) raxOk
--     rewrite interp-insts-++ (select-exp e (Var x)) (select-stmt rest) (inputs , regs , ρ)
--     with interp-CExp e ρ inputs
--     | interp-insts (select-exp e (Var x)) (inputs , regs , ρ) in eq
--     | select-exp-correct e ρ inputs (Var x) regs (VarOK xlt) raxOk
-- ... | nothing | nothing | cc = tt
-- ... | just (v , inputs') | just (inputs' , regs' , ρ') | refl , nth-ρx-v
--     rewrite sym (update-length ρ x v )
--     with interp-insts-evolved (select-exp e (Var x)) (inputs , regs , ρ)  (inputs' , regs' , ρ') eq
-- ... | a , b , reg-len , var-len
--     with raxOk
-- ... | RegOK rax-lt
--     rewrite write-var-update e x inputs inputs' regs regs' ρ ρ' v rax-lt (update-length-lemma2 x x v ρ xlt) eq nth-ρx-v 
--     | reg-len
--     =
--     select-stmt-correct rest (update ρ x v) inputs' regs' sOk (RegOK rax-lt)

-- select-inst-correct : ∀ (p : CProg)
--   → CProgOK p 
--   → interp-x86-var (select-inst p) ≡ interp-prog p
-- select-inst-correct (Program n s) (ProgramOK sok) = extensionality Goal
--   where
--   sok2 : CStmtOK s (length (replicate n 0ℤ))
--   sok2 rewrite length-replicate n {0ℤ} = sok

--   Goal : (inputs : Inputs)
--     → run-x86 (interp-insts (select-stmt s)) n inputs
--     ≡ run (interp-stmt s (replicate n 0ℤ)) inputs
--   Goal inputs
--       with interp-insts (select-stmt s) (inputs , [ 0ℤ ] , replicate n 0ℤ)
--       | interp-stmt s (replicate n (ℤ.pos 0)) inputs
--       | select-stmt-correct s (replicate n 0ℤ) inputs [ 0ℤ ] sok2 (RegOK (s≤s _≤_.z≤n))
--   ... | nothing | just (inputs' , regs' , ρ') | ()
--   ... | nothing | nothing | sync = refl
--   ... | just (inputs' , regs' , ρ') | just (v , inputs'') | refl , eq = eq

wrote : Dest → ℤ → StateX86 → StateX86 → Set
wrote (Var x) v (s , regs , ρ) (s′ , regs′ , ρ′) = s ≡ s′ × ρ′ ≡ update ρ x v     -- Ok to change rax
wrote (Reg x) v (s , regs , ρ) (s′ , regs′ , ρ′) = s ≡ s′ ×  nth regs′ x ≡ just v  ×  ρ′ ≡ ρ

wrote-write : ∀ (dest : Dest) (st : StateX86) (v : ℤ)
  → wrote dest v st (write dest v st)
wrote-write (Var x) (s , regs , ρ) v = refl , refl
wrote-write (Reg x) (s , regs , ρ) v = refl , nth-up , refl
    where
    nth-up : nth (update regs x v) x ≡ just v
    nth-up = nth-update regs x v {!!} -- need x to be well-formed

wrote-write2 : ∀ (dest : Dest) (s : Inputs) (regs regs′ ρ : Env ℤ) (v : ℤ)
  → wrote dest v (s , regs , ρ) (write dest v (s , regs′ , ρ))
wrote-write2 (Var x) s regs regs′ ρ v = refl , refl
wrote-write2 (Reg x) s regs regs′ ρ v = refl , nth-up , refl 
    where
    nth-up : nth (update regs′ x v) x ≡ just v
    nth-up = nth-update regs′ x v {!!} -- need x to be well-formed

select-exp-correct : ∀ (e : CExp) (ρ : Env ℤ) (s s′ : Inputs) (dest : Dest) (regs : List ℤ) (v : ℤ)
  → interp-CExp e ρ s ≡ just (v , s′)
  → Σ[ st′ ∈ StateX86 ] (s , regs , ρ) ⊩ select-exp e dest ⇓ st′ × wrote dest v (s′ , regs , ρ) st′
select-exp-correct (Atom a) ρ s s′ dest regs v ie
    with interp-atm a ρ in ia | ie
... | just v | refl =
    let m : (s , regs , ρ) ⊢ MovQ (to-arg a) dest ⇓ write dest v (s , regs , ρ)
        m = ⇓movq{to-arg a}{dest}{(s , regs , ρ)}{v} Goal in
    let conc : (s , regs , ρ) ⊩ MovQ (to-arg a) dest ∷ [] ⇓ write dest v (s , regs , ρ)
        conc = ⇓cons m ⇓null in
    write dest v (s , regs , ρ) , conc , wrote-write dest (s , regs , ρ) v 
    where
    Goal : interp-arg (to-arg a) (s , regs , ρ) ≡ just v
    Goal rewrite sym (to-arg-correct a ρ s regs) = ia

select-exp-correct Read ρ s s′ dest regs v ie =
  let regs′ = update regs rax v in
  let r : (s , regs , ρ) ⊢ ReadInt ⇓ (s′ , regs′ , ρ)
      r = ⇓read{s}{s′}{regs}{ρ}{v} ie in
  let m : (s′ , update regs rax v , ρ) ⊢ MovQ (Reg rax) dest ⇓ write dest v (s′ , regs′ , ρ)
      m = ⇓movq{Reg rax}{dest}{(s′ , regs′ , ρ)}{v} nth-up in
  let rm : (s , regs , ρ) ⊩ ReadInt ∷ (MovQ (Reg rax) dest) ∷ [] ⇓ write dest v (s′ , regs′ , ρ)
      rm = ⇓cons r (⇓cons m ⇓null) in
  write dest v (s′ , regs′ , ρ) , rm , wrote-write2 dest s′ regs regs′ ρ v 
  where
  nth-up : nth (update regs rax v) rax ≡ just v
  nth-up = nth-update regs rax v {!!}

select-exp-correct (Sub a₁ a₂) ρ s s′ dest regs v ie
    with interp-atm a₁ ρ in ia₁
... | just v₁ 
    with interp-atm a₂ ρ in ia₂ | ie
... | just v₂ | refl
    =
    let m1 : (s , regs , ρ) ⊢ MovQ (to-arg a₁) (Reg rax) ⇓ (s , update regs rax v₁ , ρ)
        m1 = ⇓movq{to-arg a₁}{Reg rax}{(s , regs , ρ)}{v₁} itoa1 in
    let sub : (s , update regs rax v₁ , ρ) ⊢ SubQ (to-arg a₂) (Reg rax) ⇓ (s , update (update regs rax v₁) rax (v₁ - v₂) , ρ)
        sub = ⇓subq{to-arg a₂}{Reg rax}{(s , update regs rax v₁ , ρ)}{v₁}{v₂} itoa2 nth-up in
    let m2 = ⇓movq{Reg rax}{dest}{(s , update (update regs rax v₁) rax (v₁ - v₂) , ρ)}{v₁ - v₂} nth-up2 in
    write dest (v₁ - v₂) (s , update (update regs rax v₁) rax (v₁ - v₂) , ρ) ,
    ⇓cons m1 (⇓cons sub (⇓cons m2 ⇓null)) ,
    Goal dest

    where
    itoa1 : interp-arg (to-arg a₁) (s , regs , ρ) ≡ just v₁
    itoa1 rewrite sym (to-arg-correct a₁ ρ s regs) = ia₁
    
    itoa2 : interp-arg (to-arg a₂) (s , update regs rax v₁ , ρ) ≡ just v₂
    itoa2 rewrite sym (to-arg-correct a₂ ρ s (update regs rax v₁)) = ia₂

    nth-up : nth (update regs rax v₁) rax ≡ just v₁
    nth-up = nth-update regs rax v₁ {!!}

    nth-up2 : nth (update (update regs rax v₁) rax (v₁ - v₂)) rax ≡ just (v₁ - v₂)
    nth-up2 = nth-update (update regs rax v₁) rax (v₁ - v₂) {!!}

    Goal : ∀ dest → wrote dest (v₁ - v₂) (s , regs , ρ) (write dest (v₁ - v₂) (s , update (update regs rax v₁) rax (v₁ - v₂) , ρ))
    Goal (Var x) = refl , refl 
    Goal (Reg x) = refl , nth-update (update (update regs rax v₁) rax (v₁ - v₂)) x (v₁ - v₂) {!!} , refl
     
⇓-++ : ∀{st1 st2 st3 : StateX86}{is1 is2 : List Inst}
  → st1 ⊩ is1 ⇓ st2
  → st2 ⊩ is2 ⇓ st3
  → st1 ⊩ is1 ++ is2 ⇓ st3
⇓-++ {is1 = []} ⇓null is2⇓ = is2⇓
⇓-++ {is1 = i ∷ is1} (⇓cons i⇓ is1⇓) is2⇓ = ⇓cons i⇓ (⇓-++ is1⇓ is2⇓)

select-stmt-correct : ∀ (st : CStmt) (ρ ρ′ : Env ℤ) (s s′ : Inputs) (regs : List ℤ) (v : ℤ)
  → (s , ρ) ⊢ᶜ st ⇓ v ⊣ (s′ , ρ′)
  → Σ[ regs′ ∈ Env ℤ ] (s , regs , ρ) ⊩ select-stmt st ⇓ (s′ , regs′ , ρ′) × nth regs′ 0 ≡ just v
select-stmt-correct (Return e) ρ ρ′ s s′ regs v (⇓return ie) 
    with select-exp-correct e ρ s s′ (Reg rax) regs v ie
... | (s′ , regs′ , ρ′) , se⇓st′ , refl , nth-rax-v , refl
    = regs′ , se⇓st′ , nth-rax-v
select-stmt-correct (Assign x e st) ρ ρ′ s s′ regs v (⇓assign{s′ = s′₁}{v₁ = v₁} ie st⇓v)
    with select-exp-correct e ρ s s′₁ (Var x) regs v₁ ie
... | (s′₁ , regs′ , ρ″) , se⇓ , refl , refl
    with select-stmt-correct st (update ρ x v₁) ρ′ _ s′ regs′ v st⇓v
... | regs″ , sst⇓ , nth-rax-v
    = regs″ , (⇓-++ se⇓ sst⇓) , nth-rax-v

select-inst-correct : ∀ (p : CProg) (inputs : Inputs) (v : ℤ)
  → interp-prog p inputs v
  → interp-x86-var (select-inst p) inputs v
select-inst-correct (Program n st) inputs v ((s′ , ρ′) , st⇓v)
    with select-stmt-correct st (replicate n 0ℤ) ρ′ inputs s′ [ 0ℤ ] v st⇓v
... | regs′ , sst⇓ , nth-rax-v =
    s′ , regs′ , ρ′ , sst⇓ , nth-rax-v
