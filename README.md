# correct_compilers

Experiments in proving compiler correctness


## The LVar Language (Let + Integers)

The main correctness theorem for LVar is in

    LVarCorrect.agda

LVar (Exp)           (LVar.agda)
  |
  | rco              (LVarRCOCorrect.agda)
  V
LMonVar (Atm,Mon)
  |
  | lift-locals      (LVarInterpILShifts.agda + LVarLiftCorrect.agda)
  V
 ILVar (IL-Exp, IL-Prog)
  |
  | explicate        (LVarExplicateCorrect.agda)
  V
CVar (CExp, CStmt, CProg)
  |
  | select-inst      (LVarSelectCorrect.agda)
  V
X86Var (Arg, Inst)


## The LIf Language (If + Booleans + Let + Integers)

The main correctness theorem for LVar is in

    LIf2Correct.agda
    
LIf (Exp)  (LIf2.agda)
  |
  |
  V
LMonIf (Atm,Mon)
  |
  | lift-locals      (LIf2InterpILShifts.agda + LIf2LiftCorrect.agda)
  V
 ILIf (IL-Exp, IL-Prog)
  |
  | explicate        (LIf2ExplicateCorrect.agda)
  V
CIf (CExp, CStmt, CProg)
  |
  | select-inst      (LIf2SelectCorrect.agda)
  V
X86If (Arg, Inst)
