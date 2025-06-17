# correct_compilers

Experiments in proving compiler correctness. Starting with parts of
the compilers from my _Essentials of Compilation_ textbook.


## The LVar Language (Let + Integers)

The main correctness theorem for LVar is in

    LVarCorrect.agda

Here's the sequence of compiler passes, intermediate languages, and the
Agda files that prove their correctess.

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

Here's the sequence of compiler passes, intermediate languages, and the
Agda files that prove their correctess.

    LIf (Exp)  (LIf2.agda)
      |
      | rco              (LIf2RCOCorrect.agda)
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


# Related Work

## Chez Scheme (Dybvig)

The above compiler passes all descend from Dybvig's Chez Scheme
compiler and the course notes that Dybvig used for his compiler course
at Indiana University.

## A New One-Pass Transformation into Monadic Normal Form (Olivier Danvy, 2003)

The explicate pass, at a high level, does the same thing as Olivier's
one-pass transformation.

## Modern Compiler Implementation in Java (Appel and Palsberg, 2003)

The explicate pass is also similar to the algorithm presented in this
compiler textbook.

## Compilers: Principles, Techniques, and Tools (Aho, Sethi, Ullman, 1986)

The classic dragon book gives an attribute grammar formulation of
an algorithm that is very similar to explicate.

## CakeML

The translation from stackLang to labLang handles the conversion from structured control-flow into gotos, so it serves a similar purpose to explicate control. However, CakeML does not use a control-flow translation for Boolean expressions or do the case-of-case optimization, but instead takes the straightforward approach of translation each `if` directly into a conditional jump.