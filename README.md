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

The main correctness theorem for LIf is in

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

## CompCert (Xavier Leroy et al.)

The RTLgen pass in CompCert is roughly equivalent to the `explicate`
pass, including the control-flow translation of Boolean expressions.
The RTLgen pass translates from the CminorSel intermediate language to
RTL. The proof of correctness for RTLgen is mechanized in Coq, and
relates a big-step semantics for CminorSel expressions to a small-step
semantics for RTL (and relates a small-step semantics for CminorSel
statement to the semantics of RTL). The CminorSel language still
includes `let` binding, whereas we translate `let` bindings into
assignment statements in a prior separate nanopass.

## A New One-Pass Transformation into Monadic Normal Form (Olivier Danvy, 2003)

The `explicate` pass, at a high level, does the same thing as Olivier's
one-pass transformation.

## Chez Scheme (Dybvig)

The above compiler passes all descend from Dybvig's Chez Scheme
compiler and the course notes that Dybvig used for his compiler course
at Indiana University.

## Modern Compiler Implementation in Java (Appel and Palsberg, 2003)

The `explicate` pass is also similar to the algorithm presented in this
compiler textbook.

## Compilers: Principles, Techniques, and Tools (Aho, Sethi, Ullman, 1986)

The classic dragon book gives an attribute grammar formulation of
an algorithm that is very similar to `explicate`.

## CakeML

The translation from stackLang to labLang handles the conversion from
structured control-flow into gotos, so it serves a similar purpose to
`explicate` control. However, CakeML does not use a control-flow
translation of Boolean expressions or do the case-of-case
optimization, but instead takes the straightforward approach of
translation each `if` directly into a conditional jump.

## A Transformation-Based Optimiser for Haskell (Peyton Jones and Santos, 1998)

The `explicate` pass performs the case-of-case optimization that is present in GHC.