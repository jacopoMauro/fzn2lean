# LeanFzn global-constraint library

MiniZinc searches this directory before its standard library when it
flattens a model for LeanFzn. A file `fzn_<global>.mzn` that declares the
predicate without a body keeps that global as one FlatZinc constraint;
every global without a file here is decomposed by the standard library.

It is empty on purpose. Add a global only after `leanfzn solve` compiles
the `fzn_*` constraint through a proved translation (see
`../README.md`, "Keeping globals intact"). Otherwise every model that
uses it becomes `=====UNSUPPORTED=====`.
