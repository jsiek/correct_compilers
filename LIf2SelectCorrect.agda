module LIf2SelectCorrect where

open import Agda.Builtin.Bool renaming (Bool to 𝔹)
open import Agda.Builtin.Unit
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; _≤ᵇ_; _+_; z≤n; s≤s)
open import Data.Nat.Properties
open import Data.Product hiding (map)
open import Data.Integer using (ℤ; -_; _-_; 0ℤ)
open import Data.List
open import Data.Maybe using (nothing; just)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst)

open import Utilities
open import LIf2

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

BlocksOK : List Block → ℕ → Set
BlocksOK [] nr = ⊤
BlocksOK (b ∷ bs) nr = InstsOK b nr × BlocksOK bs nr

X86VarOK : X86Var → ℕ → Set
X86VarOK (Program nv start bs) nr = BlocksOK bs nr

to-arg-correct : ∀ (a : Atm) (ρ : Env Value) (inputs : Inputs) (regs : List Value) 
  → (interp-atm a ρ) ≡ (interp-arg (to-arg a) (inputs , regs , ρ))
to-arg-correct (Num n) ρ inputs regs = refl
to-arg-correct (Bool b) ρ inputs regs = refl
to-arg-correct (Var x) ρ inputs regs
    with nth ρ x
... | nothing = refl
... | just v = refl

StateOK : StateX86 → Set
StateOK (s , regs , ρ) = 0 < length regs

wrote : Dest → Value → StateX86 → StateX86 → Set
wrote (Var x) v (s , regs , ρ) (s′ , regs′ , ρ′) = s ≡ s′ × ρ′ ≡ update ρ x v × length regs′ ≡ length regs     -- Ok to change rax
wrote (Reg x) v (s , regs , ρ) (s′ , regs′ , ρ′) = s ≡ s′ ×  nth regs′ x ≡ just v  ×  ρ′ ≡ ρ  × length regs′ ≡ length regs

wrote-write : ∀ (dest : Dest) (st : StateX86) (v : Value)
  → DestOK dest 1
  → StateOK st
  → wrote dest v st (write dest v st)
wrote-write (Var x) (s , regs , ρ) v dest-ok st-ok = refl , refl , refl
wrote-write (Reg x) (s , regs , ρ) v (RegOK lt) st-ok = refl , nth-up , refl , update-length regs x v
    where
    nth-up : nth (update regs x v) x ≡ just v
    nth-up = nth-update regs x v (≤-trans lt st-ok)

wrote-write2 : ∀ (dest : Dest) (s : Inputs) (regs regs′ ρ : Env Value) (v : Value)
  → length regs′ ≡ length regs
  → DestOK dest 1
  → 0 < length regs
  → wrote dest v (s , regs , ρ) (write dest v (s , regs′ , ρ))
wrote-write2 (Var x) s regs regs′ ρ v len-regs′ dest-ok regs-pos = refl , refl , len-regs′
wrote-write2 (Reg x) s regs regs′ ρ v len-regs′ (RegOK lt) regs-pos = refl , nth-up , refl , trans (update-length regs′ x v) len-regs′
    where
    nth-up : nth (update regs′ x v) x ≡ just v
    nth-up = nth-update regs′ x v (subst (λ X → x < X) (sym len-regs′) (≤-trans lt regs-pos))

select-assign-correct : ∀ (e : CExp) (ρ : Env Value) (s s′ : Inputs) (dest : Dest) (regs : List Value) (v : Value) (B : List Block) 
  → interp-CExp e ρ s ≡ just (v , s′)
  → 0 < length regs
  → DestOK dest 1
  → Σ[ st′ ∈ StateX86 ] (s , regs , ρ) , B ⊩ select-assign e dest ⇓ st′ , true × wrote dest v (s′ , regs , ρ) st′
  
select-assign-correct (Atom a) ρ s s′ dest regs v B ie regs-pos dest-ok
    with interp-atm a ρ in ia | ie
... | just v | refl =
    let m : (s , regs , ρ) , B ⊢ MovQ (to-arg a) dest ⇓ write dest v (s , regs , ρ) , true
        m = ⇓movq{to-arg a}{dest}{(s , regs , ρ)}{v} Goal in
    let conc : (s , regs , ρ) , B ⊩ MovQ (to-arg a) dest ∷ [] ⇓ write dest v (s , regs , ρ) , true
        conc = ⇓cons m ⇓null in
    write dest v (s , regs , ρ) , conc , wrote-write dest (s , regs , ρ) v dest-ok regs-pos
    where
    Goal : interp-arg (to-arg a) (s , regs , ρ) ≡ just v
    Goal rewrite sym (to-arg-correct a ρ s regs) = ia

select-assign-correct Read ρ s s′ dest regs v B ie regs-pos dest-ok =
  let regs′ = update regs rax v in
  let r : (s , regs , ρ) , B ⊢ ReadInt ⇓ (s′ , regs′ , ρ) , true
      r = ⇓read{s}{s′}{regs}{ρ}{v} ie in
  let m : (s′ , update regs rax v , ρ) , B ⊢ MovQ (Reg rax) dest ⇓ write dest v (s′ , regs′ , ρ) , true
      m = ⇓movq{Reg rax}{dest}{(s′ , regs′ , ρ)}{v} nth-up in
  let rm : (s , regs , ρ) , B ⊩ (ReadInt ∷ (MovQ (Reg rax) dest) ∷ []) ⇓ (write dest v (s′ , regs′ , ρ)) , true
      rm = ⇓cons r (⇓cons m ⇓null) in
  write dest v (s′ , regs′ , ρ) , rm , wrote-write2 dest s′ regs regs′ ρ v (update-length regs rax v) dest-ok regs-pos
  where
  nth-up : nth (update regs rax v) rax ≡ just v
  nth-up = nth-update regs rax v regs-pos

select-assign-correct (Sub a₁ a₂) ρ s s′ dest regs v B ie regs-pos dest-ok
    with interp-atm a₁ ρ in ia₁
... | just (Bool b₁)
    with interp-atm a₂ ρ in ia₂ | ie
... | just (Int v₂) | ()
select-assign-correct (Sub a₁ a₂) ρ s s′ dest regs v B ie regs-pos dest-ok
    | just (Int v₁)
    with interp-atm a₂ ρ in ia₂ | ie
... | just (Int v₂) | refl
    =
    let m1 : (s , regs , ρ) , B ⊢ MovQ (to-arg a₁) (Reg rax) ⇓ (s , update regs rax (Int v₁) , ρ) , true
        m1 = ⇓movq{to-arg a₁}{Reg rax}{(s , regs , ρ)}{Int v₁} itoa1 in
    let sub : (s , update regs rax (Int v₁) , ρ) , B ⊢ SubQ (to-arg a₂) (Reg rax) ⇓ (s , update (update regs rax (Int v₁)) rax (Int (v₁ - v₂)) , ρ) , true
        sub = ⇓subq{to-arg a₂}{Reg rax}{(s , update regs rax (Int v₁) , ρ)}{Int v₁}{Int v₂} itoa2 nth-up refl in
    let m2 = ⇓movq{Reg rax}{dest}{(s , update (update regs rax (Int v₁)) rax (Int (v₁ - v₂)) , ρ)}{Int (v₁ - v₂)} nth-up2 in
    write dest (Int (v₁ - v₂)) (s , update (update regs rax (Int v₁)) rax (Int (v₁ - v₂)) , ρ) ,
    ⇓cons m1 (⇓cons sub (⇓cons m2 ⇓null)) ,
    Goal dest dest-ok

    where
    itoa1 : interp-arg (to-arg a₁) (s , regs , ρ) ≡ just (Int v₁)
    itoa1 rewrite sym (to-arg-correct a₁ ρ s regs) = ia₁
    
    itoa2 : interp-arg (to-arg a₂) (s , update regs rax (Int v₁) , ρ) ≡ just (Int v₂)
    itoa2 rewrite sym (to-arg-correct a₂ ρ s (update regs rax (Int v₁))) = ia₂

    nth-up : nth (update regs rax (Int v₁)) rax ≡ just (Int v₁)
    nth-up = nth-update regs rax (Int v₁) regs-pos

    len-up-pos : 0 < length (update regs rax (Int v₁))
    len-up-pos rewrite update-length regs rax (Int v₁) = regs-pos

    nth-up2 : nth (update (update regs rax (Int v₁)) rax (Int (v₁ - v₂))) rax ≡ just (Int (v₁ - v₂))
    nth-up2 = nth-update (update regs rax (Int v₁)) rax (Int (v₁ - v₂)) len-up-pos

    len-up-up-pos : ∀ x → DestOK (Reg x) 1 → x < length (update (update regs rax (Int v₁)) rax (Int (v₁ - v₂)))
    len-up-up-pos x (RegOK lt) rewrite update-length (update regs 0 (Int v₁)) rax (Int (v₁ - v₂))
       | update-length regs 0 (Int v₁) = ≤-trans lt regs-pos

    Goal : ∀ dest → DestOK dest 1 → wrote dest (Int (v₁ - v₂)) (s , regs , ρ)
                                     (write dest (Int (v₁ - v₂)) (s , update (update regs rax (Int v₁)) rax (Int (v₁ - v₂)) , ρ))
    Goal (Var x) d-ok = refl , refl , trans (update-length (update regs rax (Int v₁)) rax (Int (v₁ - v₂))) (update-length regs rax (Int v₁))
    Goal (Reg x) d-ok = refl , nth-update (update (update regs rax (Int v₁)) rax (Int (v₁ - v₂))) x (Int (v₁ - v₂)) (len-up-up-pos x d-ok) , refl ,
          trans (update-length (update (update regs rax (Int v₁)) rax (Int (v₁ - v₂))) x (Int (v₁ - v₂)))
          (trans (update-length (update regs rax (Int v₁)) rax (Int (v₁ - v₂))) (update-length regs rax (Int v₁)))
select-assign-correct (Eq a₁ a₂) ρ s s′ dest regs v B ie regs-pos dest-ok
    with interp-atm a₁ ρ in ia₁
... | just v₁
    with interp-atm a₂ ρ in ia₂
... | just v₂
    with equal v₁ v₂ in e₁₂ | ie
... | just v | refl =
    let cmp : (s , regs , ρ) , B ⊢ CmpQ (to-arg a₁) (to-arg a₂) ⇓ (s , update regs rax v , ρ) , true
        cmp = ⇓cmpq{a₁ = to-arg a₁}{to-arg a₂} itoa1 itoa2 e₁₂ in
    let mov : (s , update regs rax v , ρ) , B ⊢ MovQ (Reg rax) dest ⇓ write dest v (s , update regs rax v , ρ) , true
        mov = ⇓movq{Reg rax}{dest}{s , update regs rax v , ρ}{v} (nth-update regs rax v regs-pos) in

    write dest v (s , update regs rax v , ρ) ,
    ⇓cons cmp (⇓cons mov ⇓null) ,
    wrote-write2 dest s regs (update regs rax v) ρ v (update-length regs rax v) dest-ok regs-pos

    where
    itoa1 : interp-arg (to-arg a₁) (s , regs , ρ) ≡ just v₁
    itoa1 rewrite sym (to-arg-correct a₁ ρ s regs) = ia₁
    
    itoa2 : interp-arg (to-arg a₂) (s , regs , ρ) ≡ just v₂
    itoa2 rewrite sym (to-arg-correct a₂ ρ s regs) = ia₂

⇓-++ : ∀{st1 st2 st3 : StateX86}{is1 is2 : List Inst} {B : List Block} {b : 𝔹}
  → st1 , B ⊩ is1 ⇓ st2 , true
  → st2 , B ⊩ is2 ⇓ st3 , b
  → st1 , B ⊩ is1 ++ is2 ⇓ st3 , b
⇓-++ {is1 = []} ⇓null is2⇓ = is2⇓
⇓-++ {is1 = i ∷ is1} (⇓cons i⇓ is1⇓) is2⇓ = ⇓cons i⇓ (⇓-++ is1⇓ is2⇓)

⇓-++-halt : ∀{st1 st2 st3 : StateX86}{is1 is2 : List Inst} {B : List Block} {b : 𝔹}
  → st1 , B ⊩ is1 ⇓ st2 , false
  → st2 , B ⊩ is2 ⇓ st3 , b
  → st1 , B ⊩ is1 ++ is2 ⇓ st2 , false
⇓-++-halt {is1 = i ∷ is1} (⇓cons x is1⇓) is2⇓ = ⇓cons x (⇓-++-halt is1⇓ is2⇓)
⇓-++-halt {is1 = i ∷ is1} (⇓cons-halt x) is2⇓ = ⇓cons-halt x

select-stmt-correct : ∀ (st : CStmt) (ρ ρ′ : Env Value) (s s′ : Inputs) (regs : List Value) (v : Value) (B : CFG)
  → (s , ρ) , B ⊢ᶜ st ⇓ v ⊣ (s′ , ρ′)
  → 0 < length regs
  → Σ[ regs′ ∈ Env Value ] Σ[ b ∈ 𝔹 ]
    (s , regs , ρ) , (map select-stmt B) ⊩ select-stmt st ⇓ (s′ , regs′ , ρ′) , b × nth regs′ rax ≡ just v
select-stmt-correct (Return e) ρ ρ′ s s′ regs v B (⇓return ie) regs-pos
    with select-assign-correct e ρ s s′ (Reg rax) regs v (map select-stmt B) ie regs-pos (RegOK (s≤s z≤n))
... | (s′ , regs′ , ρ′) , se⇓st′ , refl , nth-rax-v , refl , len-regs′
    = regs′ , true , se⇓st′ , nth-rax-v
select-stmt-correct (Assign x e st) ρ ρ′ s s′ regs v B (⇓assign{s′ = s′₁}{v₁ = v₁} ie st⇓v) regs-pos
    with select-assign-correct e ρ s s′₁ (Var x) regs v₁ (map select-stmt B) ie regs-pos VarOK
... | (s′₁ , regs′ , ρ″) , se⇓ , refl , refl , len-regs′ 
    with select-stmt-correct st (update ρ x v₁) ρ′ _ s′ regs′ v B st⇓v (subst (λ X → 0 < X) (sym len-regs′)  regs-pos)
... | regs″ , b₂ , sst⇓ , nth-rax-v =
      regs″ , b₂ , ⇓-++ se⇓ sst⇓ , nth-rax-v
select-stmt-correct (IfEq a₁ a₂ thn els) ρ ρ′ s s′ regs v B (⇓if-true{t = t} ia₁ ia₂ eqv nth t⇓v) regs-pos
    with select-stmt-correct t ρ ρ′ s s′ (update regs rax (Bool true)) v B t⇓v (≤-trans regs-pos (≤-reflexive (sym (update-length regs rax (Bool true)))))
... | regs′ , b , st⇓ , nth-rax-v =
    let ia1 = to-arg-correct a₁ ρ s regs in
    let ia2 = to-arg-correct a₂ ρ s regs in
    let cmp : (s , regs , ρ) , map select-stmt B ⊢ CmpQ (to-arg a₁) (to-arg a₂) ⇓ s , update regs rax (Bool true) , ρ , true
        cmp = ⇓cmpq{to-arg a₁}{to-arg a₂}{B = map select-stmt B} (trans (sym ia1) ia₁) (trans (sym ia2) ia₂) eqv in
    let je : (s , update regs rax (Bool true) , ρ) , map select-stmt B ⊢ JmpEq thn ⇓ s′ , regs′ , ρ′ , false
        je = ⇓jmpeq-true{s}{update regs rax (Bool true)}{l = thn} (nth-update regs rax (Bool true) regs-pos) (nth-map{xs = B} select-stmt nth) st⇓ in
    let cmp-je = ⇓cons cmp (⇓cons-halt{is = [ Jmp els ]} je) in
    regs′ , false , cmp-je , nth-rax-v
select-stmt-correct (IfEq a₁ a₂ thn els) ρ ρ′ s s′ regs v B (⇓if-false{t = t} ia₁ ia₂ eqv nth t⇓v) regs-pos
    with select-stmt-correct t ρ ρ′ s s′ (update regs rax (Bool false)) v B t⇓v (≤-trans regs-pos (≤-reflexive (sym (update-length regs rax (Bool false)))))
... | regs′ , b , st⇓ , nth-rax-v =
    let ia1 = to-arg-correct a₁ ρ s regs in
    let ia2 = to-arg-correct a₂ ρ s regs in
    let cmp : (s , regs , ρ) , map select-stmt B ⊢ CmpQ (to-arg a₁) (to-arg a₂) ⇓ s , update regs rax (Bool false) , ρ , true
        cmp = ⇓cmpq{to-arg a₁}{to-arg a₂}{B = map select-stmt B} (trans (sym ia1) ia₁) (trans (sym ia2) ia₂) eqv in
    let je : (s , update regs rax (Bool false) , ρ) , map select-stmt B ⊢ JmpEq thn ⇓ s , update regs rax (Bool false) , ρ , true
        je = ⇓jmpeq-false{s}{update regs rax (Bool false)} (nth-update regs rax (Bool false) regs-pos) in
    let j : (s , update regs 0 (Bool false) , ρ) , map select-stmt B ⊢ Jmp els ⇓ s′ , regs′ , ρ′ , false
        j = ⇓jmp (nth-map{xs = B} select-stmt nth) st⇓ in
    let cmp-je-j = ⇓cons cmp (⇓cons je (⇓cons-halt{is = []} j)) in
    regs′ , false , cmp-je-j , nth-rax-v
select-stmt-correct (Goto l) ρ ρ′ s s′ regs v B (⇓goto{t = t} nth t⇓v) regs-pos
    with select-stmt-correct t ρ ρ′ s s′ regs v B t⇓v regs-pos
... | regs′ , b , st⇓ , nth-rax-v =
    regs′ , false , ⇓cons-halt (⇓jmp{b = b} (nth-map{xs = B} select-stmt nth) st⇓) , nth-rax-v

select-inst-correct : ∀{p}{inputs}{v}
  → interp-prog p inputs v
  → interp-x86-var (select-inst p) inputs v
select-inst-correct {Program n l B}{inputs}{v} ((s′ , ρ′) , (⇓goto{t = t} nth t⇓v))
    with select-stmt-correct t (replicate n (Int 0ℤ)) ρ′ inputs s′ [ Int 0ℤ ] v B t⇓v (s≤s z≤n)
... | regs′ , b , sst⇓ , nth-rax-v =
    s′ , regs′ , ρ′ , false , ⇓jmp (nth-map{xs = B} select-stmt nth) sst⇓ , nth-rax-v

