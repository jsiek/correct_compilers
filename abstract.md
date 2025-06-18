Title: Verified Nanopasses for Compiling Conditionals

We present a proof of correctness in Agda for four nanopasses that
translate a source language with let binding, integer arithmetic,
conditional expressions and Booleans into an intermediate language
that is roughly x86 assembly with variables (prior to register
allocation).  The most interesting of these four nanopasses is a
translation of conditional expressions into goto-style control flow
that uses the continuation-oriented approach of Olivier Danvy's
one-pass transformation into monadic normal form (2003).