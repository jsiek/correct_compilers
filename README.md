# correct_compilers

Experiments in proving compiler correctness

The main correctness theorem for LVar is in

    LVarCorrect.agda

LVar (Exp)           (LVar.agda)
  |
  | rco              (LVarRCOCorrect.agda)
  V
LMonVar (Atm,Mon)
  |
  | lift-locals      (LVarLiftCorrect.agda)
  V
 IL (IL-Exp, IL-Prog)
  |
  | explicate        (LVarExplicateCorrect.agda)
  V
CVar (CExp, CStmt, CProg)
  |
  | select-inst      (LVarSelectCorrect.agda)
  V
X86Var (Arg, Inst)

