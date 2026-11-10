/-
File: LeanFzn/Compiler/Bounds.lean

Purpose:
  The U1 bound-derivation front end (PLAN.md task U1).  A model can
  declare an unbounded integer variable (`var int: x;`), which the
  finite-domain compiler cannot search.  This module narrows such a
  variable to a finite interval when the model's CONSTRAINTS force one,
  and leaves the model unsupported otherwise.

  The design separates an UNTRUSTED recognizer from a VERIFIED checker:

  * `deriveCerts` scans the model and proposes a list of `BoundCert`
    entries.  Each entry names a variable, a proposed interval and a
    rule justification.  Nothing in this file's recognizer is proved;
    it is an ordinary executable search for plausible certificates.
  * `checkCerts` replays the certificate from the model's declared
    bounds.  Each rule is checked exactly against the model's
    constraints and the bounds already derived, so a wrong proposal is
    rejected.  Only the checked environment is used for tightening.
  * `tightenModel` rewrites `.par .int` declarations to `.intRange lo
    hi` for the checked entries.  All other declarations are unchanged.

  The rules are the three of PLAN.md U1:

  * `caseSplit`: reified equalities `r1 <-> X = a`, `r2 <-> X = b`,
    with the clauses `-c \/ r1` and `c \/ r2`, give `X` inside the hull
    of the two anchors' intervals.
  * `forced`: the clauses `-c \/ r` and `c \/ r` force `r` true
    (`-c \/ -r` and `c \/ -r` force it false).
  * `linear`: an `int_lin_eq` row with a nonzero coefficient on `X`
    and checked bounds on every other term gives `X` a lower and upper
    bound.  General coefficients use floor/ceiling division; a zero
    coefficient is rejected.  The division only happens in the
    recognizer: the checker accepts the proposed interval through
    exact multiplication inequalities, so a division bug can never
    introduce an unsound bound.

  `boundsModel` returns `none` when any unbounded integer variable has
  no checked derivation.  `compileModelFull` (in `Normalize.lean`)
  turns that `none` into the honest unsupported error; it never invents
  a bound.

  Soundness, the model-equivalence theorem and well-formedness
  preservation are in `Compiler/Proofs/Bounds.lean`.

Dependencies:
  - LeanFzn.Compiler.Compile (for the `Model` types and `compileModel`
    context).
-/

import LeanFzn.Compiler.Compile

namespace LeanFzn.Compiler
open LeanFzn LeanFzn.Semantics

/-! ## Certificate data -/

/-- The sort of a tracked variable: integer-valued or Boolean. -/
inductive BoundSort where
  | int
  | bool
  deriving Repr, DecidableEq, Inhabited, BEq

/-- A checked or proposed interval for one variable. -/
structure BoundEntry where
  var : Ident
  sort : BoundSort
  lo : Int
  hi : Int
  deriving Repr, DecidableEq, Inhabited, BEq

/-- An anchor of a reified equality: an integer literal or a variable. -/
inductive BoundAnchor where
  | lit (k : Int)
  | var (x : Ident)
  deriving Repr, DecidableEq, Inhabited, BEq

/-- The rule justifying one certificate entry.  Constraint references are
    indices into the source model's `constraints` list. -/
inductive BoundRule where
  /-- `reif1` is `int_eq_reif(X, a1, r1)`, `reif2` is
      `int_eq_reif(X, a2, r2)`, `clause1` is `bool_clause([r1],[c])` and
      `clause2` is `bool_clause([c,r2],[])`. -/
  | caseSplit (reif1 : Nat) (r1 : Ident) (anchor1 : BoundAnchor)
      (reif2 : Nat) (r2 : Ident) (anchor2 : BoundAnchor)
      (c : Ident) (clause1 clause2 : Nat)
  /-- `clause1 = bool_clause([r],[c])`, `clause2 = bool_clause([c,r],[])`
      and `value = true`; with `value = false` the negated clauses
      `bool_clause([],[c,r])` and `bool_clause([c],[r])`. -/
  | forced (r c : Ident) (value : Bool) (clause1 clause2 : Nat)
  /-- `row` is an `int_lin_eq` row; `coeff` is the coefficient at the
      unique occurrence of the certified variable. -/
  | linear (row : Nat) (coeff : Int)
  deriving Repr, Inhabited

/-- One proposed entry: variable, sort, interval and rule. -/
structure BoundCert where
  var : Ident
  sort : BoundSort
  lo : Int
  hi : Int
  rule : BoundRule
  deriving Repr, Inhabited

/-- The checked environment of a certificate. -/
def BoundCert.entry (c : BoundCert) : BoundEntry :=
  ⟨c.var, c.sort, c.lo, c.hi⟩

/-- Look up a variable's entry in a checked environment (first match
    wins). -/
def lookupEntry (x : Ident) : List BoundEntry → Option BoundEntry
  | [] => none
  | e :: es => if e.var.name = x.name then some e else lookupEntry x es

/-! ## Constraint-shape helpers -/

/-- The identifier of a basic expression, if it is one. -/
def identOfBasic : BasicExpr → Option Ident
  | .ident x => some x
  | _ => none

/-- The anchor of a reified-equality operand. -/
def anchorOf : BasicExpr → Option BoundAnchor
  | .lit (.int k) => some (.lit k)
  | .ident x => some (.var x)
  | _ => none

/-- Split a reified equality `int_eq_reif(X, a, r)` with target `X`;
    returns the reified result and the anchor. -/
def eqReifRow (c : ConstraintItem) (x : Ident) :
    Option (Ident × BoundAnchor) :=
  match c.name.name, c.args with
  | "int_eq_reif", [.basic (.ident y), .basic a, .basic (.ident r)] =>
      if y.name = x.name then
        (anchorOf a).map (fun an => (r, an))
      else none
  | _, _ => none

/-- The shape `bool_clause([r],[c])`, returned as `(r,c)`. -/
def clauseSplit1 (c : ConstraintItem) : Option (Ident × Ident) :=
  match c.name.name, c.args with
  | "bool_clause", [.array [.ident r], .array [.ident cc]] => some (r, cc)
  | _, _ => none

/-- The shape `bool_clause([c,r],[])`, returned as `(c,r)`. -/
def clauseSplit2 (c : ConstraintItem) : Option (Ident × Ident) :=
  match c.name.name, c.args with
  | "bool_clause", [.array [.ident cc, .ident r], .array []] => some (cc, r)
  | _, _ => none

/-- The shape `bool_clause([],[c,r])` (the negative of the first
    forced clause), returned as `(c,r)`. -/
def clauseSplit1Neg (c : ConstraintItem) : Option (Ident × Ident) :=
  match c.name.name, c.args with
  | "bool_clause", [.array [], .array [.ident cc, .ident r]] => some (cc, r)
  | _, _ => none

/-- The shape `bool_clause([c],[r])` (the negative of the second
    forced clause), returned as `(c,r)`. -/
def clauseSplit2Neg (c : ConstraintItem) : Option (Ident × Ident) :=
  match c.name.name, c.args with
  | "bool_clause", [.array [.ident cc], .array [.ident r]] => some (cc, r)
  | _, _ => none

/-- A row of the linear rule: the `(coefficient, variable)` pairs in
    order, and the right-hand side. -/
def pairsOfRow : ArrayLiteral → ArrayLiteral → Option (List (Int × Ident))
  | [], [] => some []
  | .lit (.int k) :: cs, .ident x :: xs =>
      (pairsOfRow cs xs).map (fun ps => (k, x) :: ps)
  | _, _ => none

/-- The `int_lin_eq(coeffs, vars, rhs)` shape. -/
def linearRow (c : ConstraintItem) : Option (List (Int × Ident) × Int) :=
  match c.name.name, c.args with
  | "int_lin_eq", [.array cs, .array xs, .basic (.lit (.int b))] =>
      (pairsOfRow cs xs).map (fun ps => (ps, b))
  | _, _ => none

/-- Split a pair list at the first occurrence of `x`. -/
def splitPair (x : Ident) :
    List (Int × Ident) → Option (List (Int × Ident) × Int × List (Int × Ident))
  | [] => none
  | (c, y) :: rest =>
      if y.name = x.name then some ([], c, rest)
      else (splitPair x rest).map (fun t => ((c, y) :: t.1, t.2.1, t.2.2))

/-! ## Checker -/

/-- The lower contribution of one term: `c*lo` for `c >= 0`, `c*hi`
    for `c < 0`.  `none` when the variable has no checked integer
    interval. -/
def termLo? (env : List BoundEntry) (p : Int × Ident) : Option Int :=
  match lookupEntry p.2 env with
  | some e =>
      match e.sort with
      | .int => some (if 0 ≤ p.1 then p.1 * e.lo else p.1 * e.hi)
      | .bool => none
  | none => none

/-- The upper contribution of one term. -/
def termHi? (env : List BoundEntry) (p : Int × Ident) : Option Int :=
  match lookupEntry p.2 env with
  | some e =>
      match e.sort with
      | .int => some (if 0 ≤ p.1 then p.1 * e.hi else p.1 * e.lo)
      | .bool => none
  | none => none

/-- Sum of the lower contributions. -/
def sumLo? (env : List BoundEntry) : List (Int × Ident) → Option Int
  | [] => some 0
  | p :: ps => do
      let a ← termLo? env p
      let b ← sumLo? env ps
      pure (a + b)

/-- Sum of the upper contributions. -/
def sumHi? (env : List BoundEntry) : List (Int × Ident) → Option Int
  | [] => some 0
  | p :: ps => do
      let a ← termHi? env p
      let b ← sumHi? env ps
      pure (a + b)

/-- The checked interval of an anchor. -/
def anchorBounds (env : List BoundEntry) : BoundAnchor → Option (Int × Int)
  | .lit k => some (k, k)
  | .var x =>
      match lookupEntry x env with
      | some e => if e.sort = .int then some (e.lo, e.hi) else none
      | none => none

/-- Check one certificate against the already checked environment.
    Returns the entry to append, or `none` if any shape, reference or
    arithmetic check fails.  The conditions are dependent `if`s so the
    soundness proof can read them off directly. -/
def checkCert (m : Model) (env : List BoundEntry)
    (cert : BoundCert) : Option BoundEntry :=
  match cert.rule with
  | .caseSplit i1 r1 a1 i2 r2 a2 cc j1 j2 =>
      if hsort : cert.sort = .int then
        match m.constraints[i1]?, m.constraints[i2]?,
            m.constraints[j1]?, m.constraints[j2]?,
            anchorBounds env a1, anchorBounds env a2 with
        | some row1, some row2, some cl1, some cl2,
            some (lo1, hi1), some (lo2, hi2) =>
            if hcond :
                eqReifRow row1 cert.var = some (r1, a1) ∧
                eqReifRow row2 cert.var = some (r2, a2) ∧
                clauseSplit1 cl1 = some (r1, cc) ∧
                clauseSplit2 cl2 = some (cc, r2) ∧
                cert.lo ≤ min lo1 lo2 ∧
                max hi1 hi2 ≤ cert.hi then
              some cert.entry
            else none
        | _, _, _, _, _, _ => none
      else none
  | .forced r cc value j1 j2 =>
      if hsort : cert.sort = .bool then
        if hname : cert.var.name = r.name then
          match m.constraints[j1]?, m.constraints[j2]? with
          | some cl1, some cl2 =>
              if hcond :
                  (value = true ∧
                    clauseSplit1 cl1 = some (r, cc) ∧
                    clauseSplit2 cl2 = some (cc, r) ∧
                    cert.lo ≤ 1 ∧ 1 ≤ cert.hi) ∨
                  (value = false ∧
                    clauseSplit1Neg cl1 = some (cc, r) ∧
                    clauseSplit2Neg cl2 = some (cc, r) ∧
                    cert.lo ≤ 0 ∧ 0 ≤ cert.hi) then
                some cert.entry
              else none
          | _, _ => none
        else none
      else none
  | .linear row coeff =>
      if hsort : cert.sort = .int then
        match m.constraints[row]? with
        | none => none
        | some c =>
            match linearRow c with
            | none => none
            | some (ps, b) =>
                match splitPair cert.var ps with
                | none => none
                | some (pre, cj, post) =>
                    match sumLo? env pre, sumHi? env pre,
                        sumLo? env post, sumHi? env post with
                    | some loPre, some hiPre, some loPost, some hiPost =>
                        let smin := loPre + loPost
                        let smax := hiPre + hiPost
                        let l := b - smax
                        let u := b - smin
                        if hcond :
                            cj = coeff ∧ coeff ≠ 0 ∧
                            (0 < coeff →
                              coeff * (cert.lo - 1) < l ∧
                                u < coeff * (cert.hi + 1)) ∧
                            (coeff < 0 →
                              coeff * (cert.hi + 1) < l ∧
                                u < coeff * (cert.lo - 1)) then
                          some cert.entry
                        else none
                    | _, _, _, _ => none
      else none

/-- Replay a certificate from the model's declared bounds. -/
def checkCerts (m : Model) (env : List BoundEntry) :
    List BoundCert → Option (List BoundEntry)
  | [] => some env
  | cert :: rest =>
      match checkCert m env cert with
      | some e => checkCerts m (env ++ [e]) rest
      | none => none

/-! ## Declared bounds -/

/-- The interval a variable declaration contributes without any
    constraint reasoning.  Unbounded `var int` contributes nothing;
    interval declarations and Booleans contribute their declared
    bounds. -/
def nativeEntry : VarDeclItem → Option BoundEntry
  | .basic ty n _ _ =>
      match ty with
      | .par .bool => some ⟨n, .bool, 0, 1⟩
      | .intRange lo hi => some ⟨n, .int, lo, hi⟩
      | _ => none
  | .array .. => none

/-- The declared bounds of every finitely declared variable. -/
def nativeEnv (m : Model) : List BoundEntry :=
  m.variables.filterMap nativeEntry

/-- An unbounded integer declaration. -/
def isUnboundedInt : VarDeclItem → Bool
  | .basic (.par .int) _ _ _ => true
  | _ => false

/-- The unbounded integer declarations of a model. -/
def unboundedDecls (m : Model) : List VarDeclItem :=
  m.variables.filter isUnboundedInt

/-- A checked integer entry for `x` is present. -/
def hasIntEntry (env : List BoundEntry) (x : Ident) : Bool :=
  env.any (fun e => e.var.name == x.name && e.sort == .int)

/-! ## Untrusted recognizer -/

/-- Reified equalities of `X`. -/
def reifCandidates (m : Model) (x : Ident) :
    List (Nat × Ident × BoundAnchor) :=
  (m.constraints.zipIdx).filterMap (fun p =>
    match eqReifRow p.1 x with
    | some (r, a) => some (p.2, r, a)
    | none => none)

/-- Clause shapes `bool_clause([r],[c])` with their indices. -/
def clause1List (m : Model) : List (Ident × Ident × Nat) :=
  (m.constraints.zipIdx).filterMap (fun p =>
    match clauseSplit1 p.1 with
    | some (r, c) => some (r, c, p.2)
    | none => none)

/-- Clause shapes `bool_clause([c,r],[])` with their indices. -/
def clause2List (m : Model) : List (Ident × Ident × Nat) :=
  (m.constraints.zipIdx).filterMap (fun p =>
    match clauseSplit2 p.1 with
    | some (c, r) => some (c, r, p.2)
    | none => none)

/-- Find a first-side clause for `r`. -/
def findClause1 (cl : List (Ident × Ident × Nat)) (r : Ident) :
    Option (Ident × Nat) :=
  match cl with
  | [] => none
  | (r', c, j) :: rest =>
      if r'.name = r.name then some (c, j) else findClause1 rest r

/-- Find a second-side clause for `r`. -/
def findClause2 (cl : List (Ident × Ident × Nat)) (r : Ident) :
    Option (Ident × Nat) :=
  match cl with
  | [] => none
  | (c, r', j) :: rest =>
      if r'.name = r.name then some (c, j) else findClause2 rest r

/-- Try the case-split rule for `x`. -/
def findCaseSplit (m : Model) (env : List BoundEntry) (x : Ident) :
    Option BoundCert :=
  let reifs := reifCandidates m x
  let cl1 := clause1List m
  let cl2 := clause2List m
  (reifs.flatMap (fun p1 =>
    match findClause1 cl1 p1.2.1 with
    | none => []
    | some (c1, j1) =>
        reifs.filterMap (fun p2 =>
          match findClause2 cl2 p2.2.1 with
          | none => none
          | some (c2, j2) =>
              if c1.name = c2.name then
                match anchorBounds env p1.2.2, anchorBounds env p2.2.2 with
                | some (lo1, hi1), some (lo2, hi2) =>
                    some ⟨x, .int, min lo1 lo2, max hi1 hi2,
                      .caseSplit p1.1 p1.2.1 p1.2.2 p2.1 p2.2.1 p2.2.2
                        c1 j1 j2⟩
                | _, _ => none
              else none))).head?

/-- Floor division by a positive natural, for the recognizer only. -/
def floorDivI (a : Int) (b : Nat) : Int := Int.fdiv a (Int.ofNat b)

/-- Ceiling division by a positive natural, for the recognizer only. -/
def ceilDivI (a : Int) (b : Nat) : Int := -Int.fdiv (-a) (Int.ofNat b)

/-- Try the linear rule for `x`, given its index in the model's
    constraint list and the parsed row. -/
def linearCertFor (env : List BoundEntry) (x : Ident) (row : Nat)
    (ps : List (Int × Ident)) (b : Int) : Option BoundCert :=
  match splitPair x ps with
  | none => none
  | some (pre, cj, post) =>
      if cj = 0 then none
      else
        match sumLo? env pre, sumHi? env pre,
            sumLo? env post, sumHi? env post with
        | some loPre, some hiPre, some loPost, some hiPost =>
            let smin := loPre + loPost
            let smax := hiPre + hiPost
            let l := b - smax
            let u := b - smin
            if 0 < cj then
              some ⟨x, .int, ceilDivI l cj.natAbs, floorDivI u cj.natAbs,
                .linear row cj⟩
            else
              some ⟨x, .int, ceilDivI (-u) (-cj).natAbs,
                floorDivI (-l) (-cj).natAbs, .linear row cj⟩
        | _, _, _, _ => none

/-- Try the linear rule over all rows. -/
def findLinear (m : Model) (env : List BoundEntry) (x : Ident) :
    Option BoundCert :=
  let rec go : List (ConstraintItem × Nat) → Option BoundCert
    | [] => none
    | (c, i) :: rest =>
        match linearRow c with
        | none => go rest
        | some (ps, b) =>
            match linearCertFor env x i ps b with
            | some cert => some cert
            | none => go rest
  go (m.constraints.zipIdx)

/-- All entries derivable in one pass from the current environment.
    The pass is parallel: every certificate uses only entries present
    before the pass. -/
def derivePass (m : Model) (env : List BoundEntry) : List BoundCert :=
  (unboundedDecls m).filterMap (fun d =>
    if hasIntEntry env d.name then none
    else
      match findCaseSplit m env d.name with
      | some cert => some cert
      | none => findLinear m env d.name)

/-- Run derivation passes until no new entry appears or the fuel runs
    out.  Returns the environment and the certificate sequence. -/
def deriveCerts (m : Model) (fuel : Nat) (env : List BoundEntry)
    (certs : List BoundCert) : List BoundEntry × List BoundCert :=
  match fuel with
  | 0 => (env, certs)
  | k + 1 =>
      match derivePass m env with
      | [] => (env, certs)
      | fresh =>
          deriveCerts m k (env ++ fresh.map BoundCert.entry)
            (certs ++ fresh)

/-! ## Tightening -/

/-- The checked interval for a name, if any. -/
def checkedIntBound (env : List BoundEntry) (x : Ident) : Option (Int × Int) :=
  match lookupEntry x env with
  | some e => if e.sort = .int then some (e.lo, e.hi) else none
  | none => none

/-- Tighten one variable declaration. -/
def tightenDecl (env : List BoundEntry) : VarDeclItem → VarDeclItem
  | .basic ty n anns v =>
      match ty with
      | .par .int =>
          match checkedIntBound env n with
          | some (lo, hi) => .basic (.intRange lo hi) n anns v
          | none => .basic ty n anns v
      | _ => .basic ty n anns v
  | .array ty n anns es => .array ty n anns es

/-- Rewrite the model's variable declarations to the checked intervals.
    Parameters, constraints and the solve item are unchanged. -/
def tightenModel (m : Model) (env : List BoundEntry) : Model :=
  { m with variables := m.variables.map (tightenDecl env) }

/-- The U1 bounds pass.  Models without unbounded integer variables are
    unchanged.  Otherwise the recognizer proposes certificates, the
    checker replays them, and every unbounded integer declaration must
    have a checked interval; any gap returns `none` (unsupported). -/
def boundsModel (m : Model) : Option Model :=
  let unb := unboundedDecls m
  if unb.isEmpty then some m
  else
    let (_, certs) :=
      deriveCerts m (m.variables.length + 1) (nativeEnv m) []
    match checkCerts m (nativeEnv m) certs with
    | none => none
    | some env =>
        if unb.all (fun d => hasIntEntry env d.name) then
          some (tightenModel m env)
        else none

end LeanFzn.Compiler
