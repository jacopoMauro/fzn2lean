/-
File: LeanFzn.lean

Purpose:
  Library root of the LeanFzn verified FlatZinc stack: re-exports the
  parser, semantics, checker, and global-constraint modules so clients
  import a single name.

Dependencies:
  All 14 modules under `LeanFzn/`: FznAST, FznLexer, FznGrammar,
  FznParser, FznSemantics, FznSuffix, FznCorrectness, FznCompleteness,
  FznAssembled, FznPretty, FznStdLib, FznSolution, FznGlobals, FznCheck.

Why:
  Standard Lean practice: a root import file gives downstream files and
  executables one stable import target instead of fourteen.

DAG:
  FznAST/FznLexer -> ... -> FznCheck -> LeanFzn -> Main, solver/*
-/

import LeanFzn.FznAST
import LeanFzn.FznLexer
import LeanFzn.FznSemantics
import LeanFzn.FznGrammar
import LeanFzn.FznSuffix
import LeanFzn.FznParser
import LeanFzn.FznCorrectness
import LeanFzn.FznCompleteness
import LeanFzn.FznAssembled
import LeanFzn.FznPretty
import LeanFzn.FznStdLib
import LeanFzn.FznSolution
import LeanFzn.FznGlobals
import LeanFzn.FznCheck
