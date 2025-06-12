module LVarSelectCorrect where

open import Agda.Builtin.Unit
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; _≤ᵇ_; _+_; z≤n; s≤s)
open import Data.Nat.Properties
open import Data.Product
open import Data.Integer using (ℤ; -_; _-_; 0ℤ)
open import Data.List
open import Data.Maybe
open import Relation.Binary.PropositionalEquality
   using (_≡_; refl; trans; sym; cong; cong-app; subst)

open import Utilities
open import LVar

--------------- Proof of correctness for Select Instructions ------------------------

data DestOK : Dest → ℕ → Set where
  RegOK : ∀ {x nr : ℕ} → x < nr → DestOK (Reg x) nr
  VarOK : ∀ {x nr : ℕ} → DestOK (Var x) nr

data InstOK : Inst → ℕ → Set where
  MovQOK : ∀ {src : Arg}{dst : Dest}{nr : ℕ}
    → DestOK dst nr
    → InstOK (MovQ src dst) nr
  SubQOK : ∀ {src : Arg}{dst : Dest}{nr : ℕ}
    → DestOK dst nr
    → InstOK (SubQ src dst) nr
  ReadIntOK : ∀{nr : ℕ}
    → DestOK (Reg rax) nr
    → InstOK ReadInt nr

InstsOK : List Inst → ℕ → Set
InstsOK [] nr = ⊤
InstsOK (i ∷ is) nr = InstOK i nr × InstsOK is nr

X86VarOK : X86Var → ℕ → Set
X86VarOK (Program nv is) nr = InstsOK is nr

to-arg-correct : ∀ (a : Atm) (ρ : Env ℤ) (inputs : Inputs) (regs : List ℤ) 
  → (interp-atm a ρ) ≡ (interp-arg (to-arg a) (inputs , regs , ρ))
to-arg-correct (Num n) ρ inputs regs = refl
to-arg-correct (Var x) ρ inputs regs
    with nth ρ x
... | nothing = refl
... | just v = refl

StateOK : StateX86 → Set
StateOK (s , regs , ρ) = 0 < length regs

wrote : Dest → ℤ → StateX86 → StateX86 → Set
wrote (Var x) v (s , regs , ρ) (s′ , regs′ , ρ′) = s ≡ s′ × ρ′ ≡ update ρ x v × length regs′ ≡ length regs     -- Ok to change rax
wrote (Reg x) v (s , regs , ρ) (s′ , regs′ , ρ′) = s ≡ s′ ×  nth regs′ x ≡ just v  ×  ρ′ ≡ ρ  × length regs′ ≡ length regs

wrote-write : ∀ (dest : Dest) (st : StateX86) (v : ℤ)
  → DestOK dest 1
  → StateOK st
  → wrote dest v st (write dest v st)
wrote-write (Var x) (s , regs , ρ) v dest-ok st-ok = refl , refl , refl
wrote-write (Reg x) (s , regs , ρ) v (RegOK lt) st-ok = refl , nth-up , refl , update-length regs x v
    where
    nth-up : nth (update regs x v) x ≡ just v
    nth-up = nth-update regs x v (≤-trans lt st-ok)

wrote-write2 : ∀ (dest : Dest) (s : Inputs) (regs regs′ ρ : Env ℤ) (v : ℤ)
  → length regs′ ≡ length regs
  → DestOK dest 1
  → 0 < length regs
  → wrote dest v (s , regs , ρ) (write dest v (s , regs′ , ρ))
wrote-write2 (Var x) s regs regs′ ρ v len-regs′ dest-ok regs-pos = refl , refl , len-regs′
wrote-write2 (Reg x) s regs regs′ ρ v len-regs′ (RegOK lt) regs-pos = refl , nth-up , refl , trans (update-length regs′ x v) len-regs′
    where
    nth-up : nth (update regs′ x v) x ≡ just v
    nth-up = nth-update regs′ x v (subst (λ X → x < X) (sym len-regs′) (≤-trans lt regs-pos))

select-exp-correct : ∀ (e : CExp) (ρ : Env ℤ) (s s′ : Inputs) (dest : Dest) (regs : List ℤ) (v : ℤ)
  → interp-CExp e ρ s ≡ just (v , s′)
  → 0 < length regs
  → DestOK dest 1
  → Σ[ st′ ∈ StateX86 ] (s , regs , ρ) ⊩ select-exp e dest ⇓ st′ × wrote dest v (s′ , regs , ρ) st′
  
select-exp-correct (Atom a) ρ s s′ dest regs v ie regs-pos dest-ok
    with interp-atm a ρ in ia | ie
... | just v | refl =
    let m : (s , regs , ρ) ⊢ MovQ (to-arg a) dest ⇓ write dest v (s , regs , ρ)
        m = ⇓movq{to-arg a}{dest}{(s , regs , ρ)}{v} Goal in
    let conc : (s , regs , ρ) ⊩ MovQ (to-arg a) dest ∷ [] ⇓ write dest v (s , regs , ρ)
        conc = ⇓cons m ⇓null in
    write dest v (s , regs , ρ) , conc , wrote-write dest (s , regs , ρ) v dest-ok regs-pos
    where
    Goal : interp-arg (to-arg a) (s , regs , ρ) ≡ just v
    Goal rewrite sym (to-arg-correct a ρ s regs) = ia

select-exp-correct Read ρ s s′ dest regs v ie regs-pos dest-ok =
  let regs′ = update regs rax v in
  let r : (s , regs , ρ) ⊢ ReadInt ⇓ (s′ , regs′ , ρ)
      r = ⇓read{s}{s′}{regs}{ρ}{v} ie in
  let m : (s′ , update regs rax v , ρ) ⊢ MovQ (Reg rax) dest ⇓ write dest v (s′ , regs′ , ρ)
      m = ⇓movq{Reg rax}{dest}{(s′ , regs′ , ρ)}{v} nth-up in
  let rm : (s , regs , ρ) ⊩ ReadInt ∷ (MovQ (Reg rax) dest) ∷ [] ⇓ write dest v (s′ , regs′ , ρ)
      rm = ⇓cons r (⇓cons m ⇓null) in
  write dest v (s′ , regs′ , ρ) , rm , wrote-write2 dest s′ regs regs′ ρ v (update-length regs rax v) dest-ok regs-pos
  where
  nth-up : nth (update regs rax v) rax ≡ just v
  nth-up = nth-update regs rax v regs-pos

select-exp-correct (Sub a₁ a₂) ρ s s′ dest regs v ie regs-pos dest-ok
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
    Goal dest dest-ok

    where
    itoa1 : interp-arg (to-arg a₁) (s , regs , ρ) ≡ just v₁
    itoa1 rewrite sym (to-arg-correct a₁ ρ s regs) = ia₁
    
    itoa2 : interp-arg (to-arg a₂) (s , update regs rax v₁ , ρ) ≡ just v₂
    itoa2 rewrite sym (to-arg-correct a₂ ρ s (update regs rax v₁)) = ia₂

    nth-up : nth (update regs rax v₁) rax ≡ just v₁
    nth-up = nth-update regs rax v₁ regs-pos

    len-up-pos : 0 < length (update regs rax v₁)
    len-up-pos rewrite update-length regs rax v₁ = regs-pos

    nth-up2 : nth (update (update regs rax v₁) rax (v₁ - v₂)) rax ≡ just (v₁ - v₂)
    nth-up2 = nth-update (update regs rax v₁) rax (v₁ - v₂) len-up-pos

    len-up-up-pos : ∀ x → DestOK (Reg x) 1 → x < length (update (update regs rax v₁) rax (v₁ - v₂))
    len-up-up-pos x (RegOK lt) rewrite update-length (update regs 0 v₁) rax (v₁ - v₂)
       | update-length regs 0 v₁ = ≤-trans lt regs-pos

    Goal : ∀ dest → DestOK dest 1 → wrote dest (v₁ - v₂) (s , regs , ρ)
                                     (write dest (v₁ - v₂) (s , update (update regs rax v₁) rax (v₁ - v₂) , ρ))
    Goal (Var x) d-ok = refl , refl , trans (update-length (update regs rax v₁) rax (v₁ - v₂)) (update-length regs rax v₁)
    Goal (Reg x) d-ok = refl , nth-update (update (update regs rax v₁) rax (v₁ - v₂)) x (v₁ - v₂) (len-up-up-pos x d-ok) , refl ,
          trans (update-length (update (update regs rax v₁) rax (v₁ - v₂)) x (v₁ - v₂))
          (trans (update-length (update regs rax v₁) rax (v₁ - v₂)) (update-length regs rax v₁))
     
⇓-++ : ∀{st1 st2 st3 : StateX86}{is1 is2 : List Inst}
  → st1 ⊩ is1 ⇓ st2
  → st2 ⊩ is2 ⇓ st3
  → st1 ⊩ is1 ++ is2 ⇓ st3
⇓-++ {is1 = []} ⇓null is2⇓ = is2⇓
⇓-++ {is1 = i ∷ is1} (⇓cons i⇓ is1⇓) is2⇓ = ⇓cons i⇓ (⇓-++ is1⇓ is2⇓)

select-stmt-correct : ∀ (st : CStmt) (ρ ρ′ : Env ℤ) (s s′ : Inputs) (regs : List ℤ) (v : ℤ)
  → (s , ρ) ⊢ᶜ st ⇓ v ⊣ (s′ , ρ′)
  → 0 < length regs
  → Σ[ regs′ ∈ Env ℤ ] (s , regs , ρ) ⊩ select-stmt st ⇓ (s′ , regs′ , ρ′) × nth regs′ 0 ≡ just v
select-stmt-correct (Return e) ρ ρ′ s s′ regs v (⇓return ie) regs-pos
    with select-exp-correct e ρ s s′ (Reg rax) regs v ie regs-pos (RegOK (s≤s z≤n))
... | (s′ , regs′ , ρ′) , se⇓st′ , refl , nth-rax-v , refl , len-regs′
    = regs′ , se⇓st′ , nth-rax-v
select-stmt-correct (Assign x e st) ρ ρ′ s s′ regs v (⇓assign{s′ = s′₁}{v₁ = v₁} ie st⇓v) regs-pos
    with select-exp-correct e ρ s s′₁ (Var x) regs v₁ ie regs-pos VarOK
... | (s′₁ , regs′ , ρ″) , se⇓ , refl , refl , len-regs′ 
    with select-stmt-correct st (update ρ x v₁) ρ′ _ s′ regs′ v st⇓v (subst (λ X → 0 < X) (sym len-regs′)  regs-pos)
... | regs″ , sst⇓ , nth-rax-v
    = regs″ , (⇓-++ se⇓ sst⇓) , nth-rax-v

select-inst-correct : ∀ (p : CProg) (inputs : Inputs) (v : ℤ)
  → interp-prog p inputs v
  → interp-x86-var (select-inst p) inputs v
select-inst-correct (Program n st) inputs v ((s′ , ρ′) , st⇓v)
    with select-stmt-correct st (replicate n 0ℤ) ρ′ inputs s′ [ 0ℤ ] v st⇓v (s≤s z≤n)
... | regs′ , sst⇓ , nth-rax-v =
    s′ , regs′ , ρ′ , sst⇓ , nth-rax-v
