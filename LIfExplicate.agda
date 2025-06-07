--------------- Proof of correctness for Explicate Control -------------------

-- This one is broken because big-step doesn't work. See below.

explicate-tail-correct : ∀ {e : IL1-Exp}{ρ : Env Value}{B B' : Blocks}{t : CTail}{s : Inputs}{r : Value × Inputs}
  → explicate-tail e B ≡ (t , B')
  → interp-il1-exp e ρ s ≡ just r
  →  ρ , s , B' ⊢ t ⇓ r
  
explicate-assign-correct : ∀{y : Id}{e : IL1-Exp} {t t' : CTail}{ρ : Env Value}
   {B₂ B₃ : Blocks} {s s1 : Inputs} {v : Value}{r : Value × Inputs}
  → explicate-assign y e t B₂ ≡ (t' , B₃)
  → interp-il1-exp e ρ s ≡ just (v , s1)
  → (update ρ y v) , s1 , B₃ ⊢ t ⇓ r
  → ρ , s , B₃ ⊢ t' ⇓ r

explicate-pred-correct : ∀ (e₁ : IL1-Exp) (t₁ t₂ t₃ : CTail) (ρ : Env Value)
    (B₄ B₅ : Blocks) (s s1 : Inputs) (r : Value × Inputs) (b : 𝔹)
  → explicate-pred e₁ t₂ t₃ B₄ ≡ (t₁ , B₅)
  → interp-il1-exp e₁ ρ s ≡ just (Value.Bool b , s1)
  -- Problem! ρ is incorrect below, if e₁ is Assign, ρ changes!
  → ρ , s1 , B₅ ⊢ (if b then t₂ else t₃) ⇓ r
  → ρ , s , B₅ ⊢ t₁ ⇓ r

explicate-assign-correct {y} {Atom a} {t} {t'} {ρ} {B₂} {B₃} {s} ea ie t⇓ = {!!}
explicate-assign-correct {y} {Read} {t} {t'} {ρ} {B₂} {B₃} {s} ea ie t⇓ = {!!}
explicate-assign-correct {y} {Uni op a} {t} {t'} {ρ} {B₂} {B₃} {s} ea ie t⇓ = {!!}
explicate-assign-correct {y} {Bin op a₁ a₂} {t} {t'} {ρ} {B₂} {B₃} {s} ea ie t⇓ = {!!}
explicate-assign-correct {y} {Assign x e₁ e₂} {t} {t'} {ρ} {B₂} {B₃} {s} ea ie t⇓ = {!!}
explicate-assign-correct {y} {If e₁ e₂ e₃} {t} {t'} {ρ} {B₂} {B₃} {s} ea ie t⇓ = {!!}

explicate-tail-correct {(Atom a)} refl ie = return-⇓ ie
explicate-tail-correct {Read} refl ie = return-⇓ ie
explicate-tail-correct {(Uni op a)} refl ie = return-⇓ ie
explicate-tail-correct {(Bin op a₁ a₂)} refl ie = return-⇓ ie
explicate-tail-correct {(Assign x e₁ e₂)}{ρ}{B}{B'}{t}{s}{r} et ie
    with explicate-tail e₂ B in et2
... | t₂ , B₁
    with interp-il1-exp e₁ ρ s in ie1 | ie
... | nothing | ()
... | just (v₁ , s1) | ie2
    with explicate-tail-correct {e₂} et2 ie2
... | t₂⇓r
    =
    let B₁↝B' = explicate-assign-blocks x e₁ t₂ t B₁ B' et in
    let B'⊢t₂⇓r = eval-tail-blocks t₂ (update ρ x v₁) B₁ B' s1 (r .proj₂) (r .proj₁) B₁↝B' t₂⇓r in
    explicate-assign-correct {e = e₁} et ie1 B'⊢t₂⇓r
explicate-tail-correct {(If e₁ e₂ e₃)}{ρ}{B}{B'}{t}{s}{r} et ie
    with explicate-tail e₂ B in et2
... | t₂ , B₁
    with explicate-tail e₃ B₁ in et3
... | t₃ , B₂
    with interp-il1-exp e₁ ρ s in ie1 | ie
... | nothing | ()
... | just (Int n , s1) | ()
... | just (Bool true , s1) | ie2 =
    let t₂⇓r = explicate-tail-correct {e₂} et2 ie2 in
    let B₁↝B₂ = explicate-tail-blocks e₃ B₁ B₂ t₃ et3 in
    let B₂↝B' = explicate-pred-blocks e₁ t₂ t₃ t B₂ B' et in
    let B'⊢t₂⇓r = eval-tail-blocks t₂ ρ B₁ B' s1 (r .proj₂) (r .proj₁) (↝-trans B₁↝B₂ B₂↝B') t₂⇓r in
    explicate-pred-correct e₁ t t₂ t₃ ρ B₂ B' s s1 r true et ie1 B'⊢t₂⇓r
... | just (Bool false , s1) | ie2 =
    let t₃⇓r = explicate-tail-correct {e₃} et3 ie2 in
    let B₂↝B' = explicate-pred-blocks e₁ t₂ t₃ t B₂ B' et in
    let B'⊢t₃⇓r = eval-tail-blocks t₃ ρ B₂ B' s1 (r .proj₂) (r .proj₁) B₂↝B' t₃⇓r in
    explicate-pred-correct e₁ t t₂ t₃ ρ B₂ B' s s1 r false et ie1 B'⊢t₃⇓r

explicate-pred-correct (Atom a) t₁ t₂ t₃ ρ B B′ s s1 r b refl ie eb
    with interp-atm a ρ in ia | ie
... | nothing | ()
... | just (Bool true) | refl =
    if-⇓-true cond (goto-⇓ nth-t₂ eb)
    where
    nth-t₂ : nth ((B ++ t₂ ∷ []) ++ t₃ ∷ []) (length B) ≡ just t₂
    nth-t₂ rewrite ++-assoc B [ t₂ ] [ t₃ ] | sym (+-identityʳ (length B))
       | nth-++-+ B (t₂ ∷ t₃ ∷ []) 0 = refl
    cond : interp-CExp (Bin Eq a (Bool true)) ρ s ≡ just (Bool true , s)
    cond rewrite ia = refl
... | just (Bool false) | refl =
    if-⇓-false cond (goto-⇓ nth-t₃ eb)
    where
    nth-t₃ : nth ((B ++ t₂ ∷ []) ++ t₃ ∷ []) (length (B ++ t₂ ∷ [])) ≡ just t₃
    nth-t₃ rewrite sym (+-identityʳ (length (B ++ t₂ ∷ [])))
        | nth-++-+ (B ++ t₂ ∷ []) [ t₃ ] 0 = refl
    cond : interp-CExp (Bin Eq a (Bool true)) ρ s ≡ just (Bool false , s)
    cond rewrite ia = refl
explicate-pred-correct Read t₁ t₂ t₃ ρ B₄ B₅ s s1 r b ep () eb
explicate-pred-correct (Uni Neg a) t₁ t₂ t₃ ρ B₄ B₅ s s1 r b ep ie eb
    with interp-atm a ρ | ie
... | nothing | ()
... | just (Int x) | ()
... | just (Bool x) | ()
explicate-pred-correct (Uni Not a) t₁ t₂ t₃ ρ B B′ s s1 r b refl ie eb
    with interp-atm a ρ in ia | ie
... | nothing | ()
... | just (Bool true) | refl =
    if-⇓-true cond (goto-⇓ nth-t₃ eb)
    where
    nth-t₃ : nth ((B ++ t₃ ∷ []) ++ t₂ ∷ []) (length B) ≡ just t₃
    nth-t₃ rewrite ++-assoc B [ t₃ ] [ t₂ ] | sym (+-identityʳ (length B))
      | nth-++-+ B (t₃ ∷ t₂ ∷ []) 0 = refl
    cond : interp-CExp (Bin Eq a (Bool true)) ρ s ≡ just (Bool true , s)
    cond rewrite ia = refl
... | just (Bool false) | refl =
    if-⇓-false cond (goto-⇓ nth-t₂ eb)
    where
    nth-t₂ : nth ((B ++ t₃ ∷ []) ++ t₂ ∷ []) (length (B ++ t₃ ∷ [])) ≡ just t₂
    nth-t₂ rewrite sym (+-identityʳ (length (B ++ t₃ ∷ [])))
        | nth-++-+ (B ++ t₃ ∷ []) [ t₂ ] 0 = refl

    cond : interp-CExp (Bin Eq a (Bool true)) ρ s ≡ just (Bool false , s)
    cond rewrite ia = refl
explicate-pred-correct (Bin op a₁ a₂) t₁ t₂ t₃ ρ B₄ B₅ s s1 r b refl ie eb
    with interp-atm a₁ ρ in ia1 | interp-atm a₂ ρ in ia2
... | just v₁ | just v₂
    with b
... | true    
    = if-⇓-true cond (goto-⇓ nth-t₂ eb)
    where
    nth-t₂ : nth ((B₄ ++ t₂ ∷ []) ++ t₃ ∷ []) (length B₄) ≡ just t₂
    nth-t₂ rewrite ++-assoc B₄ [ t₂ ] [ t₃ ]
        | nth-++-length B₄ (t₃ ∷ []) t₂ = refl

    cond : interp-CExp (Bin op a₁ a₂) ρ s ≡ just (Bool true , s1)
    cond rewrite ia1 | ia2 = ie
... | false
    = if-⇓-false cond (goto-⇓ nth-t₃ eb)
    where
    nth-t₃ : nth ((B₄ ++ t₂ ∷ []) ++ t₃ ∷ []) (length (B₄ ++ t₂ ∷ [])) ≡ just t₃
    nth-t₃ rewrite nth-++-length (B₄ ++ t₂ ∷ []) [] t₃ = refl
    cond : interp-CExp (Bin op a₁ a₂) ρ s ≡ just (Bool false , s1)
    cond rewrite ia1 | ia2 = ie
explicate-pred-correct (Assign x e₁ e₂) t-out thn els ρ B B' s s1 r b ep ie eb
    with explicate-pred e₂ thn els B in et2
... | t₂ , B₁    
    with interp-il1-exp e₁ ρ s in ie1 | ie
... | nothing | ()
... | just (v₁ , s2) | ie′
    =
    let t₂⇓r = explicate-pred-correct e₂ t₂ thn els (update ρ x v₁) B B₁ s2 s1 r b et2 ie′ {!!} in
    {!!}
explicate-pred-correct (If e₁ e₂ e₃) t₁ t₂ t₃ ρ B₄ B₅ s s1 r b ep ie eb = {!!}


explicate-correct : ∀ (p : IL1-Prog) (s : Inputs) (v : Value)
  → interp-IL1 p s ≡ just v
  → eval-CIf (explicate p) s  v
explicate-correct (Program n e) s v ip
    with explicate-tail e [] in ete
... | t , B
    with create-block t B in cb
... | lbl , B'    
    with interp-il1-exp e (replicate n (Int (ℤ.pos 0))) s in ie | ip
... | nothing | ()
... | just (v , s1) | refl
    =
    let ρ₀ = replicate n (Int (ℤ.pos 0)) in
    let t⇓ = explicate-tail-correct {e}{ρ₀}{[]}{B} ete ie in
    s1 , goto-⇓ eq (eval-tail-blocks t ρ₀ B (B ++ t ∷ []) s s1 _ ((t ∷ []) , refl) t⇓)
    where
    eq : nth (B ++ t ∷ []) (foldr (λ _ → suc) 0 B) ≡ just t
    eq rewrite sym (+-identityʳ (length B)) | nth-++-+ B (t ∷ []) 0 = refl

