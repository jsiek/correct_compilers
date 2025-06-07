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
     
