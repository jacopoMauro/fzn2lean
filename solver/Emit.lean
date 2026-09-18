import Lean
import solver.Domain

-- The positional round-trip lemmas below case-analyze `Pos.Raw`
-- through `byteIdx` projections that the simp linter flags as
-- unused after `rcases`; the projections are load-bearing in the
-- *other* branch of each `by_cases`.
set_option linter.unusedSimpArgs false

/-!
# Solution-text emission (PLAN.md 6.1, 6.2)

A solver that finds a satisfying assignment must report it in the
exact format the verified checker parses (Section 4.3.3.1 of the
MiniZinc 2.10.0 handbook): `name = value;` lines, followed by the
FlatZinc separator line `----------`.

This module defines that format:

* `emitScalar` — the FlatZinc text of one scalar `Value`: Booleans as
  `true`/`false`, integers in (signed) decimal form;
* `emitEntry` — one `name = value;` line;
* `emitSolution` — the full solution text of a list of
  `(name, value)` pairs: the entries, one per line, then the
  separator.

Only scalar entries are emitted, by construction of the search
slots: the slots of `solver/Domain.lean` are initializer-free basic
variables, so their values are always integers or Booleans, and every
*array* variable of this grammar carries an initializer
(`<array-var-type> ... "=" <array-literal> ";"`) — exactly the
variables whose values the checker's store completion
(`LeanFzn.Solution.completedStore`) derives from the entries, the
same way it completes Gecode's reference solution strings (whose
alias arrays `ab = [b1, b2, ...]` may be assigned or omitted).

Soundness of the solver therefore does not rest on a string-level
round-trip theorem about the emitter: the search leaf of
`solver/Solve.lean` checks every emitted text with the verified
checker itself, and only accepts a `.sat` result whose text the
checker accepted.  The emission format is validated end-to-end by
the test suite (every emitted text is re-parsed and re-checked).
-/

namespace LeanFzn.Solver

open LeanFzn LeanFzn.Solution

/-- The FlatZinc text of one integer: decimal form, negative numbers
    with a leading `-` (the lexer's `<int-literal>` shape). -/
def emitInt (i : Int) : String :=
  toString i

/-- The FlatZinc text of one scalar solution value: `true`/`false`
    for Booleans, the decimal form for integers.  Set and array
    values never occur as slot values (the search slots are basic
    variables); the placeholders keep the function total. -/
def emitScalar : Value → String
  | .bool true => "true"
  | .bool false => "false"
  | .int i => emitInt i
  | .setOfInt _ => "<unemittable set value>"
  | .array _ => "<unemittable array value>"

/-- One solution line `name = value;` — the shape
    `parseScalarEntry` parses (an identifier, `=`, a scalar literal,
    `;`). -/
def emitEntry (name : String) (v : Value) : String :=
  s!"{name} = {emitScalar v};"

/-- The solution text of a list of assignments: one `name = value;`
    line per pair, followed by the FlatZinc separator `----------`
    (stripped by `stripSeparators` before entry parsing, exactly as
    for a solver-produced solution string). -/
def emitSolution : List (String × Value) → String
  | [] => "----------"
  | p :: rest => emitEntry p.1 p.2 ++ "\n" ++ emitSolution rest

/-! ## The accumulator fast twin (IDEAS 1.6)

`emitSolution` right-recurses with `++`, so every entry level
re-allocates the whole prefix — O(n²) character copies for `n`
entries, paid at every search leaf.  The fast twin folds *left*
into a string accumulator: the runtime's `lean_string_append`
mutates the accumulator in place whenever it is uniquely
referenced (the fold's own variable), so the whole emission is
amortized O(n) — the string counterpart of the `String.Builder`
idiom, which this toolchain's core library does not provide. -/

/-- One accumulation step: append one entry's line to the
    accumulator. -/
private def emitAccStep (acc : String) (p : String × Value) : String :=
  acc ++ emitEntry p.1 p.2 ++ "\n"

/-- The accumulator loop: left-to-right appends of the entry
    lines, then the separator. -/
private def emitSolutionGo : String → List (String × Value) → String
  | acc, [] => acc ++ "----------"
  | acc, p :: rest => emitSolutionGo (emitAccStep acc p) rest

/-- The fast twin: fold the entries into an accumulator, then the
    separator. -/
def emitSolutionFast (ps : List (String × Value)) : String :=
  emitSolutionGo "" ps

/-- The accumulation law: stepping the accumulator with one entry
    and continuing equals appending that entry's line before the
    continuation — the induction invariant behind
    `emitSolutionFast_eq`. -/
private theorem emitSolutionGo_acc : ∀ (acc : String) (p : String × Value)
    (rest : List (String × Value)),
    emitSolutionGo (emitAccStep acc p) rest
      = acc ++ (emitEntry p.1 p.2 ++ "\n" ++ emitSolutionGo "" rest) := by
  intro acc p rest
  induction rest generalizing acc p with
  | nil =>
      show (acc ++ emitEntry p.1 p.2 ++ "\n") ++ "----------"
        = acc ++ (emitEntry p.1 p.2 ++ "\n" ++ ("" ++ "----------"))
      simp only [String.empty_append, String.append_assoc]
  | cons q rest' ih =>
      show emitSolutionGo (emitAccStep (emitAccStep acc p) q) rest'
        = acc ++ (emitEntry p.1 p.2 ++ "\n"
            ++ emitSolutionGo (emitAccStep "" q) rest')
      rw [ih (emitAccStep acc p) q, ih "" q]
      simp only [emitAccStep, String.empty_append, String.append_assoc]

/-- **The fast twin is the reference `emitSolution`**: folding the
    entries into an accumulator, then appending the separator,
    produces exactly the right-recursive definition's text (IDEAS
    1.6's proof obligation; string equality is the observable,
    trivially preserved). -/
theorem emitSolutionFast_eq (ps : List (String × Value)) :
    emitSolutionFast ps = emitSolution ps := by
  induction ps with
  | nil => rfl
  | cons p rest ih =>
      have hstep : emitSolutionGo "" (p :: rest)
          = emitEntry p.1 p.2 ++ "\n" ++ emitSolutionGo "" rest :=
        emitSolutionGo_acc "" p rest
      show emitSolutionGo "" (p :: rest)
        = emitEntry p.1 p.2 ++ "\n" ++ emitSolution rest
      rw [hstep, show emitSolutionGo "" rest = emitSolutionFast rest from rfl, ih]

/- The compiled `emitSolution` runs the accumulator twin (equal by
    `emitSolutionFast_eq`). -/
attribute [implemented_by emitSolutionFast] emitSolution

/-! ## The round-trip theorem (IDEAS item 2) — infrastructure

`parseSolution (stripSeparators (emitSolution ps))` re-lexes and
re-parses the emitted text back into the entry list.  The intended
invariant — the emitter's format is exactly what `parseScalarEntry`
reads — is thereby pinned by a theorem, so a leaf fast path can build
the entry list directly (skipping string build, separator strip,
lexing, and entry parsing) with the string route still available as
the reference.

The full theorem decomposes into four layers, each an independent
lemma of lasting value (they are the project's first character- and
byte-level facts about `String.splitOn`, the lexer, and the decimal
printer):

* **Byte dictionary** (`byteLenL`, `utf8GetAux_append`, …): the
  project has no Mathlib, and Lean 4.33 core provides no bridge
  between `String`'s positional operations (`get`, `atEnd`, `next`,
  `extract` — all byte-indexed through `utf8GetAux`/`go₁`/`go₂`) and
  character lists.  The dictionary below supplies it: `byteLenL l`
  is the byte length of a char list, and the `*_append*` lemmas read
  the positional operations on a concatenation `l₁ ++ l₂` through
  their char-list parts.
* **Decimal round-trip** (`repr_val`): the digit fold of the
  lexer's `parseDecNat` over `Nat.repr n` (the nonnegative part of
  `emitInt`'s `toString`) reconstructs `n` — the numeric core of the
  emit/parse round-trip, by strong induction on `n` through
  `Nat.toDigitsCore`.

Layer status:

1. **PROVEN** — `splitOn_intercalate_newline`: splitting the
   `"\n"`-intercalation of `'\n'`-free nonempty lines on `"\n"`
   recovers the lines.  Built on the master bridge `splitOn_eq_list`
   (legacy `String.splitOn` with a single-char separator equals the
   char-level `List.splitOn` mapped through `ofList`), itself built
   on `splitOnAux_eq_splitAux` (a functional induction over
   `splitOnAux` at the aligned state) and `splitAux_spec` (splitting
   `ofList (pre ++ seg ++ rest)` from the segment start yields
   exactly the char-level `List.splitOnP` splits).
2. Still open — the lexer cons law `tokenize (s ++ "\n" ++ t) = …`
   (the character-offset twins `skipTrivia_offset`/`takeWhile_offset`
   were validated in the scratch space `probeL5.lean`);
3. the identifier half is PROVEN (`tokenize_ident`, see the
   identifier-half section below); the Boolean half of the value
   round-trip is PROVEN (`tokenize_bool` via `tokenize_keyword`);
   the lexer cons law is COMPLETE (`tokenize_cons_newline_full`,
   the full left-composition stack — see the layer-status notes);
   still open — the integer half's master assembly
   (`tokenize_int_nonneg`) and the negative-`Int` half of the
   decimal round-trip (`lexInt` on the `-`-prefixed form).

Each remaining layer is a bounded, mechanical induction on top of
the dictionary below; no new ideas are needed, only volume.  The
compilation of this file is checked after every addition, and
nothing below uses `sorry`/`native_decide`/new axioms. -/


section Roundtrip

/-! ### The byte dictionary

`String.Pos.Raw` positions are byte indices; `utf8GetAux` walks a
character list counting each character's UTF-8 size.  `byteLenL`
is that count, and the lemmas below are the append-alignment facts
every positional proof needs. -/

/-- The number of bytes a list of characters occupies in UTF-8. -/
def byteLenL (l : List Char) : Nat := l.foldl (fun p c => p + c.utf8Size) 0

/-- The byte fold is additive in its accumulator. -/
private theorem foldl_addit (l : List Char) :
    ∀ (n : Nat),
    l.foldl (fun p c => p + c.utf8Size) n
      = n + l.foldl (fun p c => p + c.utf8Size) 0 := by
  induction l with
  | nil => intro n; rfl
  | cons c cs ih =>
      intro n
      show List.foldl (fun p c => p + c.utf8Size) (n + c.utf8Size) cs
        = n + List.foldl (fun p c => p + c.utf8Size) (0 + c.utf8Size) cs
      rw [ih (n + c.utf8Size)]
      rw [show List.foldl (fun p c => p + c.utf8Size) (0 + c.utf8Size) cs
          = c.utf8Size + List.foldl (fun p c => p + c.utf8Size) 0 cs from by
        rw [show (0 : Nat) + c.utf8Size = c.utf8Size from Nat.zero_add _]
        rw [ih c.utf8Size]]
      omega

/-- A cons adds its head's UTF-8 size. -/
theorem byteLenL_cons (c : Char) (cs : List Char) :
    byteLenL (c :: cs) = c.utf8Size + byteLenL cs := by
  unfold byteLenL
  rw [List.foldl_cons, Nat.zero_add]
  exact foldl_addit cs c.utf8Size

/-- The byte length of an append is the sum of the byte lengths. -/
theorem byteLenL_append (l₁ l₂ : List Char) :
    byteLenL (l₁ ++ l₂) = byteLenL l₁ + byteLenL l₂ := by
  induction l₁ with
  | nil => simp [byteLenL]
  | cons c cs ih =>
      show byteLenL (c :: (cs ++ l₂)) = byteLenL (c :: cs) + byteLenL l₂
      rw [byteLenL_cons, byteLenL_cons, ih]
      omega

/-- `String.ofList` concatenates like list append. -/
theorem ofList_append (l l' : List Char) :
    String.ofList (l ++ l') = String.ofList l ++ String.ofList l' := by
  apply String.toList_inj.mp
  show (String.ofList (l ++ l')).toList = (String.ofList l ++ String.ofList l').toList
  rw [String.toList_ofList, String.toList_append, String.toList_ofList, String.toList_ofList]

/-- The byte length of a one-character string. -/
private theorem utf8ByteSize_ofList_singleton (c : Char) :
    (String.ofList [c]).utf8ByteSize = c.utf8Size := by
  have h1 : String.ofList [c] = String.singleton c := rfl
  rw [h1]
  exact String.utf8ByteSize_singleton

/-- The byte length of `ofList l` is `byteLenL l`. -/
theorem utf8ByteSize_ofList (l : List Char) :
    (String.ofList l).utf8ByteSize = byteLenL l := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
      show (String.ofList (c :: cs)).utf8ByteSize = byteLenL (c :: cs)
      rw [show String.ofList (c :: cs) = String.ofList [c] ++ String.ofList cs from by
        rw [← ofList_append]
        rfl,
        String.utf8ByteSize_append]
      rw [utf8ByteSize_ofList_singleton, ih, byteLenL_cons]

/-- Every string is the `ofList` of its characters, so the byte
    length of `s.toList` is `s`'s byte size. -/
theorem byteLenL_toList (s : String) : byteLenL s.toList = s.utf8ByteSize := by
  have h1 : String.ofList s.toList = s := String.ofList_toList
  have h2 := utf8ByteSize_ofList s.toList
  rw [h1] at h2
  exact h2.symm

/-- **Master alignment lemma for `utf8GetAux`**: reading the
    concatenated list `l₁ ++ l₂` from offset `r`, with the target
    `q` beyond `l₁`'s bytes, is reading `l₂` from the offset that
    skips `l₁`.  This is the workhorse behind every `get`-on-append
    fact. -/
theorem utf8GetAux_append {l₁ l₂ : List Char} :
    ∀ (r q : String.Pos.Raw),
    r.byteIdx + byteLenL l₁ ≤ q.byteIdx →
    String.Pos.Raw.utf8GetAux (l₁ ++ l₂) r q
      = String.Pos.Raw.utf8GetAux l₂ (⟨r.byteIdx + byteLenL l₁⟩ : String.Pos.Raw) q := by
  induction l₁ with
  | nil => intro r q _; rfl
  | cons c cs ih =>
      intro r q hge
      have h1 : c.utf8Size > 0 := Char.utf8Size_pos c
      have hbl : byteLenL (c :: cs) = c.utf8Size + byteLenL cs := byteLenL_cons c cs
      rw [List.cons_append, String.Pos.Raw.utf8GetAux.eq_2]
      have hne : ¬ (r = q) := by
        rcases r with ⟨ri⟩
        rcases q with ⟨qi⟩
        simp only [String.Pos.Raw.mk.injEq]
        intro hcon
        rw [hcon] at hge
        omega
      rw [if_neg hne]
      have ih2 := ih (r + c) q (by
        show (r + c).byteIdx + byteLenL cs ≤ q.byteIdx
        rw [show (r + c).byteIdx = r.byteIdx + c.utf8Size from rfl]
        omega)
      rw [ih2]
      show String.Pos.Raw.utf8GetAux l₂ ⟨r.byteIdx + c.utf8Size + byteLenL cs⟩ q
        = String.Pos.Raw.utf8GetAux l₂ ⟨r.byteIdx + byteLenL (c :: cs)⟩ q
      have harr : r.byteIdx + c.utf8Size + byteLenL cs
          = r.byteIdx + byteLenL (c :: cs) := by rw [hbl]; omega
      rw [harr]

/-- A target before the reading offset is never matched: the scan
    returns `default`. -/
theorem utf8GetAux_default_left {l : List Char} :
    ∀ (r q : String.Pos.Raw), q.byteIdx < r.byteIdx →
    String.Pos.Raw.utf8GetAux l r q = default := by
  induction l with
  | nil => intro r q _; rfl
  | cons c cs ih =>
      intro r q hlt
      rw [String.Pos.Raw.utf8GetAux.eq_2]
      rcases r with ⟨ri⟩
      rcases q with ⟨qi⟩
      have hlt' : qi < ri := by simpa only [String.Pos.Raw.byteIdx] using hlt
      clear hlt
      have hne : ¬ ((⟨ri⟩ : String.Pos.Raw) = ⟨qi⟩) := by
        simp only [String.Pos.Raw.mk.injEq]
        omega
      rw [if_neg hne]
      exact ih ((⟨ri⟩ : String.Pos.Raw) + c) ⟨qi⟩ (by
        show qi < ((⟨ri⟩ : String.Pos.Raw) + c).byteIdx
        show qi < ri + c.utf8Size
        omega)

/-- A target inside the first part of an append never reaches the
    second part. -/
theorem utf8GetAux_appendIn {l₁ l₂ : List Char} :
    ∀ (r q : String.Pos.Raw),
    r.byteIdx ≤ q.byteIdx → q.byteIdx < r.byteIdx + byteLenL l₁ →
    String.Pos.Raw.utf8GetAux l₁ r q
      = String.Pos.Raw.utf8GetAux (l₁ ++ l₂) r q := by
  induction l₁ with
  | nil =>
      intro r q hle hlt
      exact absurd hlt (by
        show q.byteIdx < r.byteIdx + byteLenL [] → False
        intro hc
        have : byteLenL [] = 0 := rfl
        omega)
  | cons c cs ih =>
      intro r q hle hlt
      have h1 : c.utf8Size > 0 := Char.utf8Size_pos c
      have hbl : byteLenL (c :: cs) = c.utf8Size + byteLenL cs := byteLenL_cons c cs
      rcases r with ⟨ri⟩
      rcases q with ⟨qi⟩
      have hle' : ri ≤ qi := by simpa only [String.Pos.Raw.byteIdx] using hle
      have hlt' : qi < ri + byteLenL (c :: cs) := by
        simpa only [String.Pos.Raw.byteIdx] using hlt
      clear hle hlt
      rw [hbl] at hlt'
      clear hbl
      show String.Pos.Raw.utf8GetAux (c :: cs) ⟨ri⟩ ⟨qi⟩
        = String.Pos.Raw.utf8GetAux (c :: (cs ++ l₂)) ⟨ri⟩ ⟨qi⟩
      rw [String.Pos.Raw.utf8GetAux.eq_2, String.Pos.Raw.utf8GetAux.eq_2]
      by_cases hcase : (⟨ri⟩ : String.Pos.Raw) = ⟨qi⟩
      · rw [if_pos hcase, if_pos hcase]
      · rw [if_neg hcase, if_neg hcase]
        show String.Pos.Raw.utf8GetAux cs ((⟨ri⟩ : String.Pos.Raw) + c) ⟨qi⟩
          = String.Pos.Raw.utf8GetAux (cs ++ l₂) ((⟨ri⟩ : String.Pos.Raw) + c) ⟨qi⟩
        by_cases hmid : qi < ri + c.utf8Size
        · rw [utf8GetAux_default_left (l := cs) _ _ (by
            show qi < ((⟨ri⟩ : String.Pos.Raw) + c).byteIdx
            exact hmid),
            utf8GetAux_default_left (l := cs ++ l₂) _ _ (by
            show qi < ((⟨ri⟩ : String.Pos.Raw) + c).byteIdx
            exact hmid)]
        · have hne2 : ((⟨ri⟩ : String.Pos.Raw) + c).byteIdx
                ≤ (⟨qi⟩ : String.Pos.Raw).byteIdx := by
            show ri + c.utf8Size ≤ qi
            omega
          have hlt2 : (⟨qi⟩ : String.Pos.Raw).byteIdx
              < ((⟨ri⟩ : String.Pos.Raw) + c).byteIdx + byteLenL cs := by
            show qi < ri + c.utf8Size + byteLenL cs
            have := hlt'
            omega
          exact ih ((⟨ri⟩ : String.Pos.Raw) + c) ⟨qi⟩ hne2 hlt2

/-- `get` on a concatenation, target inside the left factor. -/
theorem get_append_left {s t : String} {p : String.Pos.Raw}
    (hlt : p.byteIdx < s.utf8ByteSize) :
    String.Pos.Raw.get (s ++ t) p = String.Pos.Raw.get s p := by
  show String.Pos.Raw.utf8GetAux (s ++ t).toList 0 p
    = String.Pos.Raw.utf8GetAux s.toList 0 p
  rw [String.toList_append]
  have h := utf8GetAux_appendIn (l₁ := s.toList) (l₂ := t.toList) 0 p (by
    show (0 : String.Pos.Raw).byteIdx ≤ p.byteIdx
    show (0 : Nat) ≤ p.byteIdx
    omega) (by
    show p.byteIdx < (0 : String.Pos.Raw).byteIdx + byteLenL s.toList
    show p.byteIdx < 0 + byteLenL s.toList
    rw [byteLenL_toList]
    omega)
  rw [h]

/-- `next` on a concatenation, position inside the left factor. -/
theorem next_append_left {s t : String} {p : String.Pos.Raw}
    (hlt : p.byteIdx < s.utf8ByteSize) :
    String.Pos.Raw.next (s ++ t) p = String.Pos.Raw.next s p := by
  unfold String.Pos.Raw.next
  rw [get_append_left hlt]

/-- `atEnd` is false strictly inside a concatenation. -/
theorem atEnd_append_left {s t : String} {p : String.Pos.Raw}
    (hlt : p.byteIdx < s.utf8ByteSize) :
    String.Pos.Raw.atEnd (s ++ t) p = false := by
  show decide (p.byteIdx ≥ (s ++ t).utf8ByteSize) = false
  rw [String.utf8ByteSize_append]
  have h : ¬ (p.byteIdx ≥ s.utf8ByteSize + t.utf8ByteSize) := by omega
  simp only [h, decide_false]

/-- `extract.go₂` takes the whole list when the end position is at
    or beyond the list's bytes. -/
theorem extract_go₂_all {l : List Char} :
    ∀ (i e : String.Pos.Raw),
    i.byteIdx + byteLenL l ≤ e.byteIdx →
    String.Pos.Raw.extract.go₂ l i e = l := by
  induction l with
  | nil => intro i e h; rfl
  | cons c cs ih =>
      intro i e h
      show String.Pos.Raw.extract.go₂ (c :: cs) i e = c :: cs
      rw [show String.Pos.Raw.extract.go₂ (c :: cs) i e =
        (if i = e then [] else c :: String.Pos.Raw.extract.go₂ cs (i + c) e) from rfl]
      have hne : ¬ (i = e) := by
        rcases i with ⟨ii⟩
        rcases e with ⟨ee⟩
        simp only [String.Pos.Raw.mk.injEq]
        have h1 : c.utf8Size > 0 := Char.utf8Size_pos c
        have hbl : byteLenL (c :: cs) = c.utf8Size + byteLenL cs := byteLenL_cons c cs
        have h' : ii + byteLenL (c :: cs) ≤ ee := h
        omega
      rw [if_neg hne]
      rw [ih (i + c) e (by
        show (i + c).byteIdx + byteLenL cs ≤ e.byteIdx
        rw [show (i + c).byteIdx = i.byteIdx + c.utf8Size from rfl]
        have h1 : c.utf8Size > 0 := Char.utf8Size_pos c
        have h' : i.byteIdx + byteLenL (c :: cs) ≤ e.byteIdx := h
        have hbl : byteLenL (c :: cs) = c.utf8Size + byteLenL cs := byteLenL_cons c cs
        omega)]

/-! ### `String.intercalate` at `"\n"` -/

/-- `intercalate` joins a nonempty tail after the head. -/
theorem intercalate_cons_cons (t u : String) (l : List String) :
    "\n".intercalate (t :: u :: l) = t ++ "\n" ++ "\n".intercalate (u :: l) := by
  have hne : u :: l ≠ [] := by
    intro h
    cases h
  rw [String.intercalate_cons_of_ne_nil hne, String.append_assoc]

/-! ### Position lemmas at `byteLenL` boundaries (IDEAS item 2,
layer 1 infrastructure)

Reading a string whose characters are `l ++ c :: t` at the byte
position `byteLenL l` yields `c`; the position is at the end
exactly when the remaining characters are empty; stepping it
consumes `c`.  These are the `String`-level twins of the byte
dictionary's list-level facts, and the interface every positional
proof about the emitted solution text uses. -/

/-- The byte length of the empty list. -/
private theorem byteLenL_nil : byteLenL ([] : List Char) = 0 := rfl

/-- `get` at a `byteLenL` boundary reads the next character. -/
theorem get_ofList_at {l : List Char} {c : Char} {t : List Char} :
    String.Pos.Raw.get (String.ofList (l ++ c :: t)) ⟨byteLenL l⟩ = c := by
  show String.Pos.Raw.utf8GetAux (String.ofList (l ++ c :: t)).toList ⟨0⟩ ⟨byteLenL l⟩ = c
  rw [String.toList_ofList]
  have h1 := utf8GetAux_append (l₁ := l) (l₂ := c :: t) ⟨0⟩ ⟨byteLenL l⟩
    (by show (0 : Nat) + byteLenL l ≤ byteLenL l; omega)
  rw [h1]
  show String.Pos.Raw.utf8GetAux (c :: t) ⟨0 + byteLenL l⟩ ⟨byteLenL l⟩ = c
  rw [show (⟨0 + byteLenL l⟩ : String.Pos.Raw) = (⟨byteLenL l⟩ : String.Pos.Raw) from by
      exact congrArg String.Pos.Raw.mk (Nat.zero_add (byteLenL l)),
    String.Pos.Raw.utf8GetAux.eq_2, if_pos (rfl : (⟨byteLenL l⟩ : String.Pos.Raw) = ⟨byteLenL l⟩)]

/-- A boundary position is at the end exactly when the tail is
    empty. -/
theorem atEnd_ofList (l t : List Char) :
    String.Pos.Raw.atEnd (String.ofList (l ++ t)) ⟨byteLenL l⟩ = decide (t = []) := by
  show decide (byteLenL l ≥ (String.ofList (l ++ t)).utf8ByteSize) = _
  rw [utf8ByteSize_ofList, byteLenL_append]
  by_cases ht : t = []
  · subst ht
    show decide (byteLenL l ≥ byteLenL l + byteLenL ([] : List Char)) = decide (([] : List Char) = [])
    rw [show byteLenL ([] : List Char) = 0 from rfl]
    simp
  · have hf : decide (t = []) = false := by
      rw [decide_eq_false_iff_not]
      exact ht
    rw [hf]
    have hpos : byteLenL t > 0 := by
      cases t with
      | nil => exact absurd rfl ht
      | cons c cs =>
          rw [byteLenL_cons]
          have : c.utf8Size > 0 := Char.utf8Size_pos c
          omega
    have hnf : ¬ (byteLenL l ≥ byteLenL l + byteLenL t) := by omega
    simp only [hnf, decide_false]

/-- `next` at a `byteLenL` boundary steps past the character. -/
theorem next_ofList_at {l : List Char} {c : Char} {t : List Char} :
    String.Pos.Raw.next (String.ofList (l ++ c :: t)) ⟨byteLenL l⟩
      = ⟨byteLenL l + c.utf8Size⟩ := by
  unfold String.Pos.Raw.next
  rw [get_ofList_at]
  rfl

/-- **Slice transfer, `get`**: any string whose characters are
    `l ++ c :: t` reads `c` at `byteLenL l`. -/
theorem get_slice {s : String} {l : List Char} {c : Char} {t : List Char}
    (h : s.toList = l ++ c :: t) :
    String.Pos.Raw.get s ⟨byteLenL l⟩ = c := by
  have h1 : s = String.ofList (l ++ c :: t) := by
    rw [← h, String.ofList_toList]
  rw [h1]
  exact get_ofList_at

/-- **Slice transfer, `atEnd`**. -/
theorem atEnd_slice {s : String} {l : List Char} {t : List Char}
    (h : s.toList = l ++ t) :
    String.Pos.Raw.atEnd s ⟨byteLenL l⟩ = decide (t = []) := by
  have h1 : s = String.ofList (l ++ t) := by
    rw [← h, String.ofList_toList]
  rw [h1]
  exact atEnd_ofList l t

/-- **Slice transfer, `next`**. -/
theorem next_slice {s : String} {l : List Char} {c : Char} {t : List Char}
    (h : s.toList = l ++ c :: t) :
    String.Pos.Raw.next s ⟨byteLenL l⟩ = ⟨byteLenL l + c.utf8Size⟩ := by
  have h1 : s = String.ofList (l ++ c :: t) := by
    rw [← h, String.ofList_toList]
  rw [h1]
  exact next_ofList_at

/-! ### `Pos.Raw.extract` at char-list boundaries

`Pos.Raw.extract` is the char-list walk `go₁`/`go₂` behind a byte
comparison.  Two inductions show: `go₁` skips `l₁` characters to
the begin position and hands the rest to `go₂`, and `go₂` takes
exactly the accumulated segment before the end position — together
pinning `extract` on `ofList` concatenations to the corresponding
`ofList` segment. -/

/-- `go₁` skips to `b` after `l₁` characters and hands `go₂` the
    rest. -/
private theorem extract_go₁_skip : ∀ (l1 l2 : List Char) (i b e : String.Pos.Raw),
    b.byteIdx = i.byteIdx + byteLenL l1 →
    String.Pos.Raw.extract.go₁ (l1 ++ l2) i b e
      = String.Pos.Raw.extract.go₂ l2 b e := by
  intro l1
  induction l1 with
  | nil =>
      intro l2 i b e hb
      rw [byteLenL_nil] at hb
      have hib : i = b := by
        rcases i with ⟨ii⟩; rcases b with ⟨bi⟩
        simp only [String.Pos.Raw.mk.injEq] at hb ⊢
        omega
      cases l2 with
      | nil => rfl
      | cons c cs =>
          rw [show ([] : List Char) ++ (c :: cs) = c :: cs from rfl]
          simp [String.Pos.Raw.extract.go₁, hib]
  | cons c cs ih =>
      intro l2 i b e hb
      have hpos : c.utf8Size > 0 := Char.utf8Size_pos c
      have hib : ¬ (i = b) := by
        intro hcon
        rcases i with ⟨ii⟩; rcases b with ⟨bi⟩
        simp only [String.Pos.Raw.mk.injEq] at hcon hb
        rw [byteLenL_cons] at hb
        omega
      rw [List.cons_append]
      simp [String.Pos.Raw.extract.go₁, hib]
      rw [show (i + c : String.Pos.Raw) = ⟨i.byteIdx + c.utf8Size⟩ from rfl]
      exact ih l2 ⟨i.byteIdx + c.utf8Size⟩ b e (by
        rcases i with ⟨ii⟩; rcases b with ⟨bi⟩
        simp only [String.Pos.Raw.byteIdx] at hb ⊢
        rw [byteLenL_cons] at hb
        omega)

/-- `go₂` takes exactly `acc` characters before `e`. -/
private theorem extract_go₂_mid : ∀ (acc rest : List Char) (i e : String.Pos.Raw),
    e.byteIdx = i.byteIdx + byteLenL acc →
    String.Pos.Raw.extract.go₂ (acc ++ rest) i e = acc := by
  intro acc
  induction acc with
  | nil =>
      intro rest i e he
      rw [byteLenL_nil] at he
      have hie : i = e := by
        rcases i with ⟨ii⟩; rcases e with ⟨ei⟩
        simp only [String.Pos.Raw.mk.injEq] at he ⊢
        omega
      cases rest with
      | nil => rfl
      | cons c cs =>
          rw [show ([] : List Char) ++ (c :: cs) = c :: cs from rfl]
          simp [String.Pos.Raw.extract.go₂, hie]
  | cons c cs ih =>
      intro rest i e he
      have hpos : c.utf8Size > 0 := Char.utf8Size_pos c
      have hne : ¬ (i = e) := by
        intro hcon
        rcases i with ⟨ii⟩; rcases e with ⟨ei⟩
        simp only [String.Pos.Raw.mk.injEq] at hcon he
        rw [byteLenL_cons] at he
        omega
      rw [List.cons_append]
      simp [String.Pos.Raw.extract.go₂, hne]
      rw [show (i + c : String.Pos.Raw) = ⟨i.byteIdx + c.utf8Size⟩ from rfl]
      exact ih rest ⟨i.byteIdx + c.utf8Size⟩ e (by
        rcases i with ⟨ii⟩; rcases e with ⟨ei⟩
        simp only [String.Pos.Raw.byteIdx] at he ⊢
        rw [byteLenL_cons] at he
        omega)

/-- Reduce the match in `Pos.Raw.extract` by case-splitting the
    positions. -/
private theorem extract_reduce (s : String) (b e : String.Pos.Raw) :
    String.Pos.Raw.extract s b e
      = if b.byteIdx ≥ e.byteIdx then "" else
          String.ofList (String.Pos.Raw.extract.go₁ s.toList (0 : String.Pos.Raw) b e) := by
  cases b; cases e
  simp only [String.Pos.Raw.extract]

/-- **The segment characterization of `extract`**: the segment of
    `ofList (pre ++ acc ++ rest)` between the boundaries `pre` and
    `pre ++ acc` is exactly `ofList acc`. -/
theorem extract_ofList_seg (pre acc rest : List Char) :
    String.Pos.Raw.extract (String.ofList (pre ++ acc ++ rest))
      ⟨byteLenL pre⟩ ⟨byteLenL (pre ++ acc)⟩ = String.ofList acc := by
  rw [extract_reduce]
  simp only [String.toList_ofList]
  by_cases hacc : acc = []
  · subst hacc
    have hrew : (pre ++ ([] : List Char) ++ rest) = pre ++ rest := by
      rw [List.append_nil]
    have hrew2 : (pre ++ ([] : List Char)) = pre := List.append_nil pre
    rw [hrew, hrew2]
    have hcond : (⟨byteLenL pre⟩ : String.Pos.Raw).byteIdx
        ≥ (⟨byteLenL pre⟩ : String.Pos.Raw).byteIdx := Nat.le_refl _
    rw [if_pos hcond]
  · have hposacc : byteLenL acc > 0 := by
      cases acc with
      | nil => exact absurd rfl hacc
      | cons c cs =>
          rw [byteLenL_cons]
          have : c.utf8Size > 0 := Char.utf8Size_pos c
          omega
    have hcond : ¬ ((⟨byteLenL pre⟩ : String.Pos.Raw).byteIdx
        ≥ (⟨byteLenL (pre ++ acc)⟩ : String.Pos.Raw).byteIdx) := by
      simp only [byteLenL_append]
      omega
    rw [if_neg hcond]
    rw [byteLenL_append] at hcond ⊢
    rw [show pre ++ acc ++ rest = pre ++ (acc ++ rest) from List.append_assoc pre acc rest]
    have hzero : (⟨byteLenL pre⟩ : String.Pos.Raw).byteIdx
        = (0 : String.Pos.Raw).byteIdx + byteLenL pre := by
      show byteLenL pre = (0 : Nat) + byteLenL pre
      exact (Nat.zero_add (byteLenL pre)).symm
    rw [extract_go₁_skip pre (acc ++ rest) (0 : String.Pos.Raw)
      ⟨byteLenL pre⟩ ⟨byteLenL pre + byteLenL acc⟩ hzero]
    rw [extract_go₂_mid acc rest ⟨byteLenL pre⟩ ⟨byteLenL pre + byteLenL acc⟩ (by
      show (⟨byteLenL pre + byteLenL acc⟩ : String.Pos.Raw).byteIdx
          = (⟨byteLenL pre⟩ : String.Pos.Raw).byteIdx + byteLenL acc
      rfl)]

/-- **Slice transfer, `extract`**: the segment of any string whose
    characters are `pre ++ acc ++ rest` between the corresponding
    boundaries is `ofList acc`. -/
theorem extract_slice {s : String} {pre acc rest : List Char}
    (h : s.toList = pre ++ acc ++ rest) :
    String.Pos.Raw.extract s ⟨byteLenL pre⟩ ⟨byteLenL (pre ++ acc)⟩ = String.ofList acc := by
  have h1 : s = String.ofList (pre ++ acc ++ rest) := by
    rw [← h, String.ofList_toList]
  rw [h1]
  exact extract_ofList_seg pre acc rest

/-- **The `splitAux` spec**: splitting `ofList (pre ++ seg ++ rest)` from the
    segment start `byteLenL pre` and scan position `byteLenL (pre ++ seg)`
    (the scanned segment `seg` being q-free) yields, in order, the q-split
    of `seg ++ rest` mapped through `ofList`, prepended after the reversed
    accumulator (the accumulated items complete in reverse). -/
theorem splitAux_spec (q : Char → Bool) :
    ∀ (rest pre seg : List Char) (r : List String),
    (∀ x ∈ seg, q x = false) →
    String.splitAux (String.ofList (pre ++ seg ++ rest)) q
      ⟨byteLenL pre⟩ ⟨byteLenL (pre ++ seg)⟩ r
      = r.reverse ++ (List.splitOnP q (seg ++ rest)).map String.ofList := by
  intro rest
  induction rest with
  | nil =>
      intro pre seg r hfree
      rw [String.splitAux.eq_def]
      have hend : String.Pos.Raw.atEnd (String.ofList (pre ++ seg ++ [])) ⟨byteLenL (pre ++ seg)⟩ = true := by
        rw [atEnd_ofList]
        rfl
      simp only [hend]
      -- the pushed segment: extract ... = ofList seg
      have hextr : String.Pos.Raw.extract (String.ofList (pre ++ seg ++ ([] : List Char)))
          ⟨byteLenL pre⟩ ⟨byteLenL (pre ++ seg)⟩ = String.ofList seg := by
        rw [extract_ofList_seg]
      rw [hextr]
      -- (ofList seg :: r).reverse = r.reverse ++ [ofList seg]
      show (String.ofList seg :: r).reverse = _
      rw [List.reverse_cons]
      -- splitOnP q (seg ++ []) = [seg] under q-freedom
      have hsplit : List.splitOnP q (seg ++ ([] : List Char)) = [seg] := by
        rw [List.append_nil]
        exact List.splitOnP_eq_singleton hfree
      rw [hsplit]
      simp
  | cons c rest' ih =>
      intro pre seg r hfree
      rw [String.splitAux.eq_def]
      have hend : String.Pos.Raw.atEnd (String.ofList (pre ++ seg ++ c :: rest')) ⟨byteLenL (pre ++ seg)⟩ = false := by
        rw [atEnd_ofList]
        have hne : decide ((c :: rest' : List Char) = []) = false := by
          cases rest' <;> rfl
        exact hne
      simp only [hend, Bool.false_eq_true, if_false]
      have hget : String.Pos.Raw.get (String.ofList (pre ++ seg ++ c :: rest')) ⟨byteLenL (pre ++ seg)⟩ = c :=
        get_ofList_at
      by_cases hq : q c
      · -- separator char: push the segment [pre-seg], restart after c
        rw [hget, if_pos hq]
        -- next position = byteLenL (pre ++ seg) + c.utf8Size
        have hnext : String.Pos.Raw.next (String.ofList (pre ++ seg ++ c :: rest'))
            ⟨byteLenL (pre ++ seg)⟩ = ⟨byteLenL (pre ++ seg) + c.utf8Size⟩ := by
          unfold String.Pos.Raw.next
          rw [hget]
          rfl
        rw [hnext]
        -- the pushed segment extract: [byteLenL pre, byteLenL (pre ++ seg)) = ofList seg
        have hextr : String.Pos.Raw.extract (String.ofList (pre ++ seg ++ c :: rest'))
            ⟨byteLenL pre⟩ ⟨byteLenL (pre ++ seg)⟩ = String.ofList seg := by
          have hsplit : pre ++ seg ++ c :: rest' = (pre ++ seg) ++ (c :: rest') := by rw [List.append_assoc]
          rw [hsplit]
          exact extract_ofList_seg pre seg (c :: rest')
        rw [hextr]
        -- recurse: IH with pre' = pre ++ seg ++ [c], seg' = []
        have hpre' : ∀ (x : Char), x ∈ ([] : List Char) → q x = false := by intro x h; exact absurd h (by simp)
        have hih := ih (pre ++ seg ++ [c]) [] (String.ofList seg :: r) hpre'
        have hstr : (pre ++ seg ++ [c]) ++ [] ++ rest' = pre ++ seg ++ c :: rest' := by
          simp
        rw [hstr] at hih
        -- align positions: byteLenL (pre ++ seg) + c.utf8Size = byteLenL (pre ++ seg ++ [c])
        have hbl : byteLenL (pre ++ seg) + c.utf8Size = byteLenL (pre ++ seg ++ [c]) := by
          rw [byteLenL_append (pre ++ seg) [c], byteLenL_cons c [],
            show byteLenL ([] : List Char) = 0 from rfl]
          omega
        rw [hbl]
        rw [show pre ++ seg ++ [c] ++ [] = pre ++ seg ++ [c] from List.append_nil _] at hih
        rw [hih]
        -- now: (ofList seg :: r).reverse ++ map ofList (splitOnP q (c :: rest'))
        --    = r.reverse ++ map ofList (splitOnP q (seg ++ c :: rest'))
        -- splitOnP q (seg ++ c :: rest') = modifyHead (cons into each of seg) ...
        -- since all of seg is q-free: splitOnP q (seg ++ c :: rest') = seg :: splitOnP q (c :: rest')
        have hs : List.splitOnP q (seg ++ c :: rest') = seg :: List.splitOnP q rest' := by
          clear hih hstr hpre' hget hend hnext hextr hbl
          induction seg with
          | nil =>
              have hstep : List.splitOnP q (c :: rest') = [] :: List.splitOnP q rest' := by
                rw [List.splitOnP_cons_eq_if_modifyHead, hq]
                simp
              exact hstep
          | cons a as ihseg =>
              have hfa : q a = false := hfree a (List.mem_cons_self ..)
              have hfas : ∀ (x : Char), x ∈ as → q x = false := by
                intro x hx
                exact hfree x (by simp [hx])
              rw [List.cons_append]
              rw [List.splitOnP_cons_eq_if_modifyHead, hfa, if_neg (by simp [hfa])]
              rw [ihseg hfas]
              show List.modifyHead (fun t => a :: t) (as :: List.splitOnP q rest')
                  = (a :: as) :: List.splitOnP q rest'
              simp [List.modifyHead]
        rw [hs]
        simp [List.reverse_cons]
      · -- non-separator char: extend the segment
        have hqf : q c = false := by
          cases hqc : q c with
          | true => exact absurd hqc hq
          | false => rfl
        rw [hget, if_neg (show ¬ (q c = true) from by
          rw [hqf]
          intro hc
          exact Bool.noConfusion hc)]
        have hnext : String.Pos.Raw.next (String.ofList (pre ++ seg ++ c :: rest'))
            ⟨byteLenL (pre ++ seg)⟩ = ⟨byteLenL (pre ++ seg) + c.utf8Size⟩ := by
          unfold String.Pos.Raw.next
          rw [hget]
          rfl
        rw [hnext]
        -- recursion with seg' = seg ++ [c]
        have hfree' : ∀ (x : Char), x ∈ seg ++ [c] → q x = false := by
          intro x hx
          rcases List.mem_append.mp hx with h | h
          · exact hfree x h
          · have hxc : x = c := by
              rcases List.mem_singleton.mp h with rfl
              rfl
            rw [hxc]
            exact hqf
        have hih := ih pre (seg ++ [c]) r hfree'
        have hstr : pre ++ (seg ++ [c]) ++ rest' = pre ++ seg ++ c :: rest' := by simp
        rw [hstr] at hih
        -- align the goal's scan position with the IH's
        have hbl2 : byteLenL (pre ++ seg) + c.utf8Size = byteLenL (pre ++ (seg ++ [c])) := by
          rw [byteLenL_append pre (seg ++ [c]), byteLenL_append pre seg]
          rw [byteLenL_append seg [c], byteLenL_cons c [], show byteLenL ([] : List Char) = 0 from rfl]
          omega
        rw [hbl2]
        rw [hih]
        -- splitOnP q ((seg ++ [c]) ++ rest') = splitOnP q (seg ++ c :: rest')
        have hstr2 : (seg ++ [c]) ++ rest' = seg ++ c :: rest' := by
          simp
        rw [hstr2]
        -- the remaining if-False closes by rfl
        rfl

/-- `Pos.Raw` addition: shifting the summand. -/
private theorem pos_add (d : Nat) (r : String.Pos.Raw) (c : Char) :
    (⟨d + r.byteIdx⟩ : String.Pos.Raw) + c = ⟨d + (r.byteIdx + c.utf8Size)⟩ := by
  have h : (⟨d + r.byteIdx⟩ : String.Pos.Raw) + c = ⟨(d + r.byteIdx) + c.utf8Size⟩ := rfl
  rw [h, Nat.add_assoc]

private theorem utf8GetAux_shift' (l : List Char) (d : Nat) :
    ∀ (r q : String.Pos.Raw), d ≤ q.byteIdx →
    String.Pos.Raw.utf8GetAux l ⟨d + r.byteIdx⟩ q
      = String.Pos.Raw.utf8GetAux l r (⟨q.byteIdx - d⟩ : String.Pos.Raw) := by
  induction l with
  | nil => intro _ _ _; rfl
  | cons c cs ih =>
      intro r q hq
      show String.Pos.Raw.utf8GetAux (c :: cs) ⟨d + r.byteIdx⟩ q = _
      rw [String.Pos.Raw.utf8GetAux.eq_2, String.Pos.Raw.utf8GetAux.eq_2]
      by_cases h : (⟨d + r.byteIdx⟩ : String.Pos.Raw) = q
      · have hrq : r = (⟨q.byteIdx - d⟩ : String.Pos.Raw) := by
          rcases r with ⟨ri⟩; rcases q with ⟨qi⟩
          simp only [String.Pos.Raw.mk.injEq] at h hq ⊢
          omega
        rw [if_pos h, if_pos (hrq ▸ rfl)]
      · rw [if_neg h]
        have hne : ¬ (r = (⟨q.byteIdx - d⟩ : String.Pos.Raw)) := by
          intro he
          rcases r with ⟨ri⟩; rcases q with ⟨qi⟩
          simp only [String.Pos.Raw.mk.injEq] at he h hq ⊢
          omega
        rw [if_neg hne, pos_add]
        exact ih ⟨r.byteIdx + c.utf8Size⟩ q (by omega)

theorem get_ofList_shift (l1 l2 : List Char) (k : Nat) :
    String.Pos.Raw.get (String.ofList (l1 ++ l2)) ⟨byteLenL l1 + k⟩
      = String.Pos.Raw.get (String.ofList l2) ⟨k⟩ := by
  show String.Pos.Raw.utf8GetAux (String.ofList (l1 ++ l2)).toList ⟨0⟩ ⟨byteLenL l1 + k⟩ = _
  rw [String.toList_ofList]
  rw [utf8GetAux_append (l₁ := l1) (l₂ := l2) ⟨0⟩ ⟨byteLenL l1 + k⟩
    (by show (0 : Nat) + byteLenL l1 ≤ byteLenL l1 + k; omega)]
  have hnorm : ∀ (n : Nat), (⟨(⟨0⟩ : String.Pos.Raw).byteIdx + n⟩ : String.Pos.Raw) = ⟨n⟩ := by
    intro n
    show (⟨(⟨0⟩ : String.Pos.Raw).byteIdx + n⟩ : String.Pos.Raw) = ⟨n⟩
    have h0 : (⟨0⟩ : String.Pos.Raw).byteIdx = 0 := rfl
    rw [h0, Nat.zero_add]
  rw [hnorm]
  have hq : byteLenL l1 ≤ (⟨byteLenL l1 + k⟩ : String.Pos.Raw).byteIdx := by
    show byteLenL l1 ≤ byteLenL l1 + k
    omega
  have hshift := utf8GetAux_shift' l2 (byteLenL l1) (0 : String.Pos.Raw) ⟨byteLenL l1 + k⟩ hq
  rw [show (⟨byteLenL l1 + k⟩ : String.Pos.Raw).byteIdx - byteLenL l1 = k from by
    show byteLenL l1 + k - byteLenL l1 = k
    omega] at hshift
  have h0 : (0 : String.Pos.Raw).byteIdx = 0 := rfl
  rw [h0, Nat.add_zero] at hshift
  rw [hshift]
  show String.Pos.Raw.utf8GetAux l2 (0 : String.Pos.Raw) ⟨k⟩
      = String.Pos.Raw.utf8GetAux (String.ofList l2).toList (⟨0⟩ : String.Pos.Raw) ⟨k⟩
  rw [String.toList_ofList]
  rfl

theorem atEnd_ofList_shift (l1 l2 : List Char) (k : Nat) :
    String.Pos.Raw.atEnd (String.ofList (l1 ++ l2)) ⟨byteLenL l1 + k⟩
      = String.Pos.Raw.atEnd (String.ofList l2) ⟨k⟩ := by
  show decide (byteLenL l1 + k ≥ (String.ofList (l1 ++ l2)).utf8ByteSize)
      = decide (k ≥ (String.ofList l2).utf8ByteSize)
  rw [utf8ByteSize_ofList (l1 ++ l2), byteLenL_append, utf8ByteSize_ofList l2]
  simp only [Nat.add_le_add_iff_left]

theorem next_ofList_shift (l1 l2 : List Char) (k : Nat) :
    (String.Pos.Raw.next (String.ofList (l1 ++ l2)) ⟨byteLenL l1 + k⟩).byteIdx
      = byteLenL l1 + (String.Pos.Raw.next (String.ofList l2) ⟨k⟩).byteIdx := by
  have h1 : (String.Pos.Raw.next (String.ofList (l1 ++ l2)) ⟨byteLenL l1 + k⟩).byteIdx
      = byteLenL l1 + k + (String.Pos.Raw.get (String.ofList l2) ⟨k⟩).utf8Size := by
    show (String.Pos.Raw.next (String.ofList (l1 ++ l2)) ⟨byteLenL l1 + k⟩).byteIdx = _
    have hnext : String.Pos.Raw.next (String.ofList (l1 ++ l2)) ⟨byteLenL l1 + k⟩
        = (⟨byteLenL l1 + k⟩ : String.Pos.Raw) + String.Pos.Raw.get (String.ofList (l1 ++ l2)) ⟨byteLenL l1 + k⟩ := rfl
    rw [hnext, show String.Pos.Raw.get (String.ofList (l1 ++ l2)) ⟨byteLenL l1 + k⟩
        = String.Pos.Raw.get (String.ofList l2) ⟨k⟩ from get_ofList_shift l1 l2 k]
    rfl
  have h2 : (String.Pos.Raw.next (String.ofList l2) ⟨k⟩).byteIdx
      = k + (String.Pos.Raw.get (String.ofList l2) ⟨k⟩).utf8Size := rfl
  rw [h1, h2]
  omega

/-! ### The decimal round-trip

The lexer's `parseDecNat` is exactly the digit fold below, and
`Nat.repr` (the nonnegative half of `emitInt`'s `toString`) is the
digit list of the number — so the fold reconstructs the number. -/

/-- The numeric value of a decimal digit character. -/
def toDigit (c : Char) : Nat := c.toNat - '0'.toNat

/-- `Nat.digitChar` inverts `toDigit` on digit values. -/
theorem digitChar_toDigit (n : Nat) (h : n < 10) : toDigit (Nat.digitChar n) = n := by
  have h1 : (Nat.digitChar n).toNat = '0'.toNat + n := by
    revert n
    decide +revert
  unfold toDigit
  omega

/-- `toDigitsCore` pushes a prefix accumulator to the front of its
    result. -/
private theorem toDigitsCore_acc (fuel n : Nat) (acc : List Char) :
    Nat.toDigitsCore 10 fuel n acc = Nat.toDigitsCore 10 fuel n [] ++ acc := by
  induction fuel generalizing n acc with
  | zero => rfl
  | succ fuel' ih =>
      rw [Nat.toDigitsCore.eq_2, Nat.toDigitsCore.eq_2]
      by_cases hz : n / 10 = 0
      · rw [if_pos hz, if_pos hz]
        show (n % 10).digitChar :: acc = ((n % 10).digitChar :: []) ++ acc
        rfl
      · rw [if_neg hz, if_neg hz]
        rw [ih (n / 10) ((n % 10).digitChar :: acc), ih (n / 10) ((n % 10).digitChar :: [])]
        simp only [List.append_assoc, List.cons_append]
        rfl

/-- **The decimal round-trip**: the digit fold over the decimal
    representation of `n` (with enough fuel, as `Nat.toDigits`
    supplies) reconstructs `n`. -/
theorem toDigitsCore_val : ∀ (n : Nat) (fuel : Nat), n < fuel →
    (Nat.toDigitsCore 10 fuel n []).foldl (fun acc c => acc * 10 + toDigit c) 0 = n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
      intro fuel hfuel
      cases fuel with
      | zero => omega
      | succ fuel' =>
          have hfuel' : n ≤ fuel' := by omega
          rw [Nat.toDigitsCore.eq_2]
          by_cases hz : n / 10 = 0
          · rw [if_pos hz]
            show ((n % 10).digitChar :: ([] : List Char)).foldl
                (fun acc c => acc * 10 + toDigit c) 0 = n
            rw [List.foldl_cons, List.foldl_nil]
            rw [digitChar_toDigit (n % 10)
              (show n % 10 < 10 from Nat.mod_lt (x := n) (y := 10) (hy := Nat.succ_pos 9))]
            have hn10 : n < 10 := by
              rcases Nat.div_eq_zero_iff.mp hz with h | h
              · exact absurd h (by omega)
              · exact h
            have hmod : n % 10 = n := Nat.mod_eq_of_lt hn10
            omega
          · rw [if_neg hz]
            have hdigit : n / 10 < n := by
              have h1 : n / 10 * 10 ≤ n := Nat.div_mul_le_self n 10
              have h2 : n % 10 < 10 :=
                Nat.mod_lt (x := n) (y := 10) (hy := Nat.succ_pos 9)
              have h3 : n / 10 ≠ 0 := hz
              have h4 : 10 * (n / 10) + n % 10 = n := Nat.div_add_mod n 10
              omega
            have hrec := ih (n / 10) hdigit fuel' (by omega)
            rw [toDigitsCore_acc fuel' (n / 10) ((n % 10).digitChar :: [])]
            show List.foldl (fun acc c => acc * 10 + toDigit c) 0
                (Nat.toDigitsCore 10 fuel' (n / 10) [] ++ [(n % 10).digitChar]) = n
            rw [List.foldl_append, List.foldl_cons, List.foldl_nil, hrec]
            rw [digitChar_toDigit (n % 10)
              (show n % 10 < 10 from Nat.mod_lt (x := n) (y := 10) (hy := Nat.succ_pos 9))]
            have := Nat.div_add_mod n 10
            omega

/-- `Nat.toDigits` is the fueled digit generator. -/
private theorem toDigits_eq (n : Nat) :
    Nat.toDigits 10 n = Nat.toDigitsCore 10 (n + 1) n [] := rfl

/-- **The `Nat.repr` round-trip**: the `parseDecNat`-shaped digit
    fold over the printed form of `n` reconstructs `n`. -/
theorem repr_val (n : Nat) :
    (Nat.repr n).foldl (fun acc c => acc * 10 + toDigit c) 0 = n := by
  show (String.ofList (Nat.toDigits 10 n)).foldl (fun acc c => acc * 10 + toDigit c) 0 = n
  rw [String.foldl_eq_foldl_toList, String.toList_ofList, toDigits_eq]
  exact toDigitsCore_val n (n + 1) (Nat.lt_succ_self n)

/-- A `String.foldl` over `ofList` is the `List.foldl`. -/
theorem foldl_ofList {α} (f : α → Char → α) (init : α) (l : List Char) :
    (String.ofList l).foldl f init = l.foldl f init := by
  rw [String.foldl_eq_foldl_toList, String.toList_ofList]


/-- `get` on the single-char separator string at position ⟨0⟩. -/
private theorem get_sep0 (c : Char) :
    String.Pos.Raw.get (String.ofList [c]) ⟨0⟩ = c := by
  show String.Pos.Raw.utf8GetAux (String.ofList [c]).toList ⟨0⟩ ⟨0⟩ = c
  rw [String.toList_ofList, String.Pos.Raw.utf8GetAux.eq_2,
    if_pos (rfl : (⟨0⟩ : String.Pos.Raw) = ⟨0⟩)]

/-- `next` on the single-char separator string at position ⟨0⟩. -/
private theorem next_sep0 (c : Char) :
    String.Pos.Raw.next (String.ofList [c]) ⟨0⟩ = ⟨c.utf8Size⟩ := by
  unfold String.Pos.Raw.next
  rw [get_sep0]
  exact congrArg String.Pos.Raw.mk (Nat.zero_add c.utf8Size)

/-- The single-char separator is exhausted after its only char. -/
private theorem atEnd_sep (c : Char) :
    String.Pos.Raw.atEnd (String.ofList [c]) ⟨c.utf8Size⟩ = true := by
  show decide (c.utf8Size ≥ (String.ofList [c]).utf8ByteSize) = true
  rw [utf8ByteSize_ofList]
  have hbl : byteLenL [c] = c.utf8Size := by
    rw [byteLenL_cons]
    show c.utf8Size + (List.foldl (fun p c => p + c.utf8Size) 0 ([] : List Char)) = c.utf8Size
    simp
  rw [hbl]
  simp

set_option maxHeartbeats 2000000 in
/-- For a single-character separator, `splitOnAux` at the aligned state
    (`j` at separator position 0) computes exactly `splitAux` with the
    equality predicate. -/
theorem splitOnAux_eq_splitAux (c : Char) (s : String) :
    ∀ (b i j : String.Pos.Raw) (r : List String),
    j = (⟨0⟩ : String.Pos.Raw) →
    String.splitOnAux s (String.ofList [c]) b i j r
      = String.splitAux s (fun x => x == c) b i r := by
  intro b i j r
  induction b, i, j, r using String.splitOnAux.induct (s := s) (sep := String.ofList [c]) with
  | case1 b₁ i₁ j₁ r₁ hend =>
      intro _
      rw [String.splitOnAux, String.splitAux]
      simp only [hend, if_true, dif_pos trivial]
  | case2 b₁ i₁ j₁ r₁ hnotend hmatch _ _ hsepend IH =>
      intro hj
      -- the char equality
      have hget : String.Pos.Raw.get s i₁ = c := by
        have hbeq : (String.Pos.Raw.get s i₁ == String.Pos.Raw.get (String.ofList [c]) j₁) = true := hmatch
        rw [beq_iff_eq] at hbeq
        rw [hj, get_sep0] at hbeq
        exact hbeq
      have hnextj : String.Pos.Raw.next (String.ofList [c]) j₁ = ⟨c.utf8Size⟩ := by
        rw [hj, next_sep0]
      -- the separator-end condition, specialized (zeta-reducing the let)
      have hsepend' : String.Pos.Raw.atEnd (String.ofList [c])
          (String.Pos.Raw.next (String.ofList [c]) j₁) = true := by
        rw [hnextj]
        exact atEnd_sep c
      rw [String.splitOnAux.eq_def]
      simp only [hnotend, if_false, hmatch, hsepend', if_true]
      rw [String.splitAux.eq_def]
      simp only [hnotend, if_false]
      have hcond : (String.Pos.Raw.get s i₁ == c) = true := by
        rw [hget]
        simp
      rw [hcond, if_pos rfl]
      simp only [dif_neg (by decide : ¬ (false = true))]
      -- the pushed extract: (next s i₁).unoffsetBy (next sep j₁) = i₁
      have hunoff : (String.Pos.Raw.next s i₁).unoffsetBy (String.Pos.Raw.next (String.ofList [c]) j₁)
          = i₁ := by
        rw [hnextj, show String.Pos.Raw.next s i₁
            = (⟨i₁.byteIdx + (String.Pos.Raw.get s i₁).utf8Size⟩ : String.Pos.Raw) from rfl, hget]
        show (⟨(i₁.byteIdx + c.utf8Size) - c.utf8Size⟩ : String.Pos.Raw) = i₁
        exact congrArg String.Pos.Raw.mk (Nat.add_sub_cancel _ _)
      rw [hunoff]
      simp only [if_neg (by decide : ¬ (false = true))]
      -- the IH at rfl, with its conclusion transported through hunoff
      have hIH : s.splitOnAux (String.ofList [c]) (String.Pos.Raw.next s i₁)
          (String.Pos.Raw.next s i₁) (⟨0⟩ : String.Pos.Raw)
          (String.Pos.Raw.extract s b₁ i₁ :: r₁)
          = s.splitAux (fun x => x == c) (String.Pos.Raw.next s i₁)
              (String.Pos.Raw.next s i₁) (String.Pos.Raw.extract s b₁ i₁ :: r₁) := by
        have h := IH rfl
        rw [hunoff] at h
        exact h
      exact hIH
  | case3 b₁ i₁ j₁ r₁ hnotend hmatch _ _ hnotsepend IH =>
      intro hj
      -- vacuous: a single-char separator is fully consumed after one match step
      have hnext : String.Pos.Raw.next (String.ofList [c]) j₁ = ⟨c.utf8Size⟩ := by
        rw [hj, next_sep0]
      have hnend : String.Pos.Raw.atEnd (String.ofList [c]) (String.Pos.Raw.next (String.ofList [c]) j₁) = true := by
        rw [hnext]
        exact atEnd_sep c
      -- hnotsepend is the negation of exactly this
      exact absurd hnend hnotsepend
  | case4 b₁ i₁ j₁ r₁ hnotend hnomatch IH =>
      intro hj
      subst hj
      -- mismatch: both sides advance i past the non-matching char
      rw [String.splitOnAux.eq_def]
      simp only [hnotend, Bool.not_eq_true', decide_false, if_false, hnomatch, if_true]
      rw [String.splitAux.eq_def]
      simp only [hnotend, Bool.not_eq_true', decide_false, if_false]
      simp only [dif_neg (by decide : ¬ (false = true)), if_neg (by decide : ¬ (false = true))]
      -- the splitOnAux side's mismatch position: next s (i₁.unoffsetBy ⟨0⟩) = next s i₁
      have hunoff0 : i₁.unoffsetBy (⟨0⟩ : String.Pos.Raw) = i₁ := by
        show (⟨i₁.byteIdx - 0⟩ : String.Pos.Raw) = i₁
        exact congrArg String.Pos.Raw.mk (Nat.sub_zero _)
      rw [hunoff0]
      -- the condition (fun x => x == c) (get s i₁) = (get s i₁ == c) is false
      have hcond' : ¬ (String.Pos.Raw.get s i₁ == c) = true := by
        have := hnomatch
        rw [get_sep0] at this
        exact this
      rw [if_neg hcond']
      exact IH rfl



/-- `String.splitOn` with a single-char separator equals the char-level
    `List.splitOn` mapped through `ofList` (the master bridge). -/
theorem splitOn_eq_list (c : Char) (s : String) :
    s.splitOn (String.ofList [c])
      = (List.splitOn c s.toList).map String.ofList := by
  rw [show s.splitOn (String.ofList [c])
      = (if (String.ofList [c]) == "" then [s] else
          String.splitOnAux s (String.ofList [c]) ⟨0⟩ ⟨0⟩ ⟨0⟩ []) from rfl]
  have hne : ¬ ((String.ofList [c]) == "") = true := by
    intro h
    have hq : String.ofList [c] = "" := by
      rw [show (String.ofList [c] == "") = decide (String.ofList [c] = "") from rfl] at h
      exact of_decide_eq_true h
    have hlen := congrArg String.length hq
    rw [String.length_ofList, String.length_empty] at hlen
    exact nomatch hlen
  rw [if_neg hne]
  rw [splitOnAux_eq_splitAux c s ⟨0⟩ ⟨0⟩ ⟨0⟩ [] rfl]
  -- splitAux from 0/0 with the top-level accumulator []
  show String.splitAux s (fun x => x == c) ⟨0⟩ ⟨0⟩ []
      = (List.splitOn c s.toList).map String.ofList
  -- instantiate the spec at pre = [], seg = [], rest = s.toList
  -- the spec instance, with the string rewritten to `s` itself
  have hstr : String.ofList ([] ++ [] ++ s.toList) = s := by
    rw [List.nil_append, List.nil_append, String.ofList_toList]
  have hspec0 := splitAux_spec (fun x => x == c) s.toList [] [] []
    (by intro x h; exact absurd h (by simp))
  rw [hstr] at hspec0
  -- the spec's positions: byteLenL [] = 0, so ⟨byteLenL []⟩ = ⟨0⟩ etc.
  have hb0 : byteLenL ([] : List Char) = 0 := rfl
  rw [hb0] at hspec0
  rw [show (⟨0⟩ : String.Pos.Raw) = (⟨byteLenL ([] : List Char)⟩ : String.Pos.Raw) from by
      rw [show byteLenL ([] : List Char) = 0 from rfl]] at hspec0 ⊢
  -- normalize hspec0's second position (`byteLenL ([] ++ [])` → `byteLenL []`) and its
  -- splitOnP argument, then conclude
  have hnil2 : ([] : List Char) ++ ([] : List Char) = [] := rfl
  rw [hnil2, List.nil_append] at hspec0
  rw [hspec0]
  -- List.splitOnP (· == c) l = List.splitOn c l
  rw [show List.splitOnP (fun x => x == c) s.toList = List.splitOn c s.toList from rfl]
  simp


/-- **The `splitOn "\n"` intercalate law** (IDEAS item 2, layer 1): splitting
    the `"\n"`-intercalation of nonempty `'\n'`-free lines on `"\n"`
    recovers the lines. -/
theorem splitOn_intercalate_newline (l : List String)
    (hfree : ∀ x ∈ l, '\n' ∉ x.toList) (hne : l ≠ []) :
    (String.intercalate "\n" l).splitOn "\n" = l := by
  rw [show ("\n" : String) = String.ofList ['\n'] from rfl, splitOn_eq_list]
  -- toList of the intercalation is the char-level intercalation
  rw [String.toList_intercalate]
  rw [show ("\n" : String).toList = ['\n'] from rfl]
  rw [List.splitOn_intercalate '\n' (ls := (l.map String.toList))]
  · -- map ofList ∘ map toList = id on each string
    have hmap : (l.map String.toList).map String.ofList = l := by
      have key : ∀ (l : List String), (l.map String.toList).map String.ofList = l := by
        intro l'
        induction l' with
        | nil => rfl
        | cons y ys ihy =>
            rw [List.map_cons, List.map_cons, ihy, String.ofList_toList]
      exact key l
    rw [hmap]
  · intro ll hll
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hll
    exact hfree x hx
  · intro hc
    cases l with
    | nil => exact hne rfl
    | cons x xs => exact absurd hc (by simp)

end Roundtrip

/-! ## The lexer cons law (IDEAS item 2, layer 2)

Tokenizing `s ++ "\n" ++ t` is tokenizing `s`, then tokenizing `t`:
the newline separator is whitespace to the lexer, and no token of a
well-formed entry line straddles the boundary (the separator
prevents both token continuation across the join and comment
run-on, since `%`-comments end at the newline).  The law is stated
with the hypothesis that the token stream of `s` alone is exactly
`toks` (the tokenizer's only exit is the end of input, so the walk
consumed all of `s`), and — crucially — that tokenizing `s` ends at
a *hard* boundary: the last character before the join does not
continue a token that `t`'s first character could extend.  The
newline separator provides this by construction for entry lines;
the general statement carries it as a hypothesis on `skipTrivia`. -/

section LexerCons

open LeanFzn.Lexer
theorem arrGetElem_append_left {s t : Array Char} {i : Nat} (h : i < s.size) :
    (s ++ t)[i]'(by rw [Array.size_append]; omega) = s[i]'h := by
  rw [Array.getElem_append_left h]

theorem takeWhile_append_left {p : Char → Bool} {s t : Array Char}
    {pos : Nat} {acc : String}
    (hstop : (takeWhile p s pos acc).2 < s.size) :
    takeWhile p (s ++ t) pos acc = takeWhile p s pos acc := by
  have key : ∀ (q : Nat) (acc : String),
      (takeWhile p s q acc).2 < s.size →
      takeWhile p (s ++ t) q acc = takeWhile p s q acc := by
    intro q acc
    induction q, acc using takeWhile.induct (p := p) (s := s) with
    | case1 q acc h c hpc ih =>
        intro hq
        have hlt : q < (s ++ t).size := by rw [Array.size_append]; omega
        rw [takeWhile.eq_def, takeWhile.eq_def]
        simp only [h, hlt, dif_pos]
        rw [show (s ++ t)[q]'hlt = s[q]'h from arrGetElem_append_left h]
        rw [if_pos hpc]
        have h1 : takeWhile p s q acc
            = takeWhile p s (q + 1) (acc.push c) := by
          rw [takeWhile.eq_def]; simp only [h, dif_pos]
          rw [show p (s[q]'h) = true from hpc]
          rw [show (s[q]'h) = c from rfl]
          simp only [reduceIte]
        rw [h1] at hq
        rw [show p (s[q]'h) = true from hpc]
        simp only [reduceIte]
        exact ih hq
    | case2 q acc h c hpc =>
        intro hq
        have hlt : q < (s ++ t).size := by rw [Array.size_append]; omega
        rw [takeWhile.eq_def, takeWhile.eq_def]
        simp only [h, hlt, dif_pos]
        rw [show (s ++ t)[q]'hlt = s[q]'h from arrGetElem_append_left h]
        rw [if_neg hpc, if_neg hpc]
    | case3 q acc h =>
        intro hq
        -- past the end of s the s-walk stops at q; hq forces
        -- q < s.size, contradicting h
        have hq' : q < s.size := by
          have h1 := takeWhile_ge p s q acc
          rw [takeWhile.eq_def, dif_neg h] at hq
          simp only at hq
          omega
        exact absurd hq' h
  exact key pos acc hstop


/-- `skipTrivia` agrees on the appended array while the skip's result
    stays inside the first array, provided `s` has no `%` from the
    position on (so the skip never runs a comment past the join). -/
theorem skipTrivia_append_left {s t : Array Char} {pos : Nat}
    (hnopct : ∀ (q : Nat), pos ≤ q → ∀ h : q < s.size, s[q]'h ≠ '%')
    (hstop : skipTrivia s pos < s.size) :
    skipTrivia (s ++ t) pos = skipTrivia s pos := by
  have key : ∀ (q : Nat), pos ≤ q → skipTrivia s q < s.size →
      skipTrivia (s ++ t) q = skipTrivia s q := by
    intro q
    induction q using skipTrivia.induct (s := s) with
    | case1 q h c hw ih =>
        intro hle hstop
        have hlt : q < (s ++ t).size := by rw [Array.size_append]; omega
        have heq : (s ++ t)[q]'hlt = s[q]'h := arrGetElem_append_left h
        have hw' : isWhitespace (s[q]'h) = true := hw
        rw [skipTrivia.eq_def]
        rw [dif_pos hlt]
        rw [heq]
        rw [if_pos hw']
        rw [skipTrivia.eq_def (s := s) (pos := q)]
        rw [dif_pos h]
        rw [if_pos hw']
        -- the s-walk stepped to q+1 and stopped inside s (hstop)
        have hstop' : skipTrivia s (q + 1) < s.size := by
          have h1 : skipTrivia s q = skipTrivia s (q + 1) := by
            rw [skipTrivia.eq_def (s := s) (pos := q)]
            rw [dif_pos h]
            rw [if_pos hw']
          rw [h1] at hstop
          exact hstop
        exact ih (by omega) hstop'
    | case2 q h c hw hc ih =>
        intro hle hstop
        -- the '%' branch contradicts hnopct
        exact absurd (show (s[q]'h) = '%' from by simpa using hc)
          (hnopct q hle h)
    | case3 q h c hw hc =>
        intro hle hstop
        have hlt : q < (s ++ t).size := by rw [Array.size_append]; omega
        have heq : (s ++ t)[q]'hlt = s[q]'h := arrGetElem_append_left h
        have hw' : ¬ isWhitespace (s[q]'h) = true := hw
        have hc' : ¬((s[q]'h) == '%') = true := hc
        rw [skipTrivia.eq_def]
        rw [dif_pos hlt]
        rw [heq]
        rw [if_neg hw']
        rw [if_neg hc']
        rw [skipTrivia.eq_def (s := s) (pos := q)]
        rw [dif_pos h]
        rw [if_neg hw']
        rw [if_neg hc']
    | case4 q h =>
        intro hle hstop
        -- the s-walk stopped at q ≥ s.size, contradicting hstop
        rw [skipTrivia.eq_def (s := s) (pos := q)] at hstop
        rw [dif_neg h] at hstop
        exact absurd hstop h
  exact key pos (Nat.le_refl pos) hstop


theorem arrGetElem!_of_lt {a : Array Char} {i : Nat} (h : i < a.size) :
    a[i]! = a[i]'h := by
  rw [Array.getElem!_eq_getD, Array.getElem_eq_getD (α := Char) default]

theorem arrGetElem!_append_left {s t : Array Char} {i : Nat} (hle : i < s.size) :
    (s ++ t)[i]! = s[i]! := by
  have hlt : i < (s ++ t).size := by rw [Array.size_append]; omega
  rw [arrGetElem!_of_lt (h := hlt), arrGetElem!_of_lt (h := hle)]
  exact arrGetElem_append_left hle

/-- If the character at `pos` satisfies the scan predicate, the scan
    advances strictly past `pos` (the room lemma behind the taken
    branches of the prefix conditions). -/
theorem takeWhile_step_of {s : Array Char} {pos : Nat} {p : Char → Bool}
    (hlt : pos < s.size) (hp : p (s[pos]'hlt) = true) :
    pos + 1 ≤ (takeWhile p s pos "").2 := by
  have key : takeWhile p s pos ""
      = takeWhile p s (pos + 1) (String.push "" (s[pos]'hlt)) := by
    rw [takeWhile.eq_def (s := s) (pos := pos) (acc := "")]
    rw [dif_pos hlt]
    rw [if_pos hp]
  have hge := takeWhile_ge p s (pos + 1) (String.push "" (s[pos]'hlt))
  rw [key]
  exact hge

/-- The bang read and the proof-carrying read agree (below the
    size). -/
theorem arrGetElem_bang_eq {a : Array Char} {i : Nat} (h : i < a.size) :
    a[i]! = a[i]'h := by
  rw [Array.getElem!_eq_getD, Array.getElem_eq_getD]

/-! ### The integer half of the lexer round-trip (IDEAS item 2)

`emitInt`'s nonnegative form is `Nat.repr n` = the digit string
`Nat.toDigits 10 n`.  The master assembly below tokenizes that text:
every guard of `lexUnsigned`/`lexInt` must be known to fail, so the
decimal arm is taken and its value is `parseDecNat` of the scanned
digits — which `toDigitsCore_val` reconstructs as `n`.  The char
exclusions are proved by transposition through the value bounds
exactly as in `isDigit_not_ws`/`isDigit_not_pct` above.
-/

/-- A digit char equals neither `'x'` nor `'o'`. -/
theorem digit_not_xo {c : Char} (hd : isDigit c = true) :
    (c == 'x') = false ∧ (c == 'o') = false := by
  unfold isDigit at hd
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hd
  obtain ⟨hge, hle⟩ := hd
  refine ⟨?_, ?_⟩
  · by_cases hc : c = 'x'
    · subst hc
      -- hle : 'x' ≤ '9' is decidable-false ('x' = 120 > '9' = 57):
      have hle' : ¬ (('x' : Char) ≤ '9') := by decide
      exact absurd hle hle'
    · show (c == 'x') = false
      by_cases hbeq : (c == 'x') = true
      · exact absurd (by simpa using hbeq) hc
      · exact Bool.not_eq_true _ |>.mp (by simpa using hbeq)
  · by_cases hc : c = 'o'
    · subst hc
      have hle' : ¬ (('o' : Char) ≤ '9') := by decide
      exact absurd hle hle'
    · show (c == 'o') = false
      by_cases hbeq : (c == 'o') = true
      · exact absurd (by simpa using hbeq) hc
      · exact Bool.not_eq_true _ |>.mp (by simpa using hbeq)

/-- A digit char is not `'-'`. -/
theorem digit_not_minus {c : Char} (hd : isDigit c = true) : (c == '-') = false := by
  unfold isDigit at hd
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hd
  obtain ⟨hge, _hle⟩ := hd
  -- digits start at '0', which is after '-': c = '-' gives '0' ≤ '-'
  by_cases hcc : (c == '-') = true
  · have hceq : c = '-' := by
      simpa using hcc
    subst hceq
    have hcontra : (('0' : Char)) ≤ '-' := hge
    exact absurd hcontra (by decide)
  · exact Bool.not_eq_true _ |>.mp hcc

/-- On a digit-headed array whose every char is a digit, `lexUnsigned`
    takes the decimal arm: both prefix guards fail (the second char,
    when present, is a digit — never `'x'`/`'o'`), and the decimal
    scan is nonempty because it consumed the head digit. -/
theorem lexUnsigned_decimal {s : Array Char} {pos : Nat}
    (hpos : pos < s.size)
    (hhead : isDigit s[pos]! = true)
    (hdigits : ∀ k : Nat, k < s.size → isDigit s[k]! = true) :
    lexUnsigned s pos =
      .ok ((parseDecNat (takeWhile isDigit s pos "").1 : Int),
           (takeWhile isDigit s pos "").2) := by
  rw [lexUnsigned]
  -- the hex/oct guard conjunctions are false (the char at pos+1 is a
  -- digit, never 'x'/'o'):
  have hsecondigit : pos + 1 < s.size → isDigit s[pos + 1]! = true := by
    intro h1
    exact hdigits (pos + 1) h1
  have hx : ¬ ((decide (pos + 1 < s.size) && s[pos]! == '0'
        && s[pos + 1]! == 'x') = true) := by
    intro hh
    rw [Bool.and_eq_true, Bool.and_eq_true] at hh
    obtain ⟨⟨h1, _⟩, hxneg⟩ := hh
    have h1n : pos + 1 < s.size := by simpa using h1
    have hstep := (digit_not_xo (hsecondigit h1n)).1
    rw [hstep] at hxneg
    exact Bool.noConfusion hxneg
  have ho : ¬ ((decide (pos + 1 < s.size) && s[pos]! == '0'
        && s[pos + 1]! == 'o') = true) := by
    intro hh
    rw [Bool.and_eq_true, Bool.and_eq_true] at hh
    obtain ⟨⟨h1, _⟩, honeg⟩ := hh
    have h1n : pos + 1 < s.size := by simpa using h1
    have hstep := (digit_not_xo (hsecondigit h1n)).2
    rw [hstep] at honeg
    exact Bool.noConfusion honeg
  rw [if_neg hx, if_neg ho]
  -- the decimal arm: the scan consumed at least the head digit, so
  -- its result cannot be empty.  Route: if the scan were empty, the
  -- one-step unfold's taken branch contradicts the head-digit fact.
  have hnonempty : ¬ ((takeWhile isDigit s pos "").1.isEmpty = true) := by
    intro hempty
    rw [takeWhile.eq_def (s := s) (pos := pos) (acc := "")] at hempty
    simp only [dif_pos hpos] at hempty
    -- the if test is on the no-bang read; transport hhead to it:
    have hposnb : s[pos]! = s[pos] := by
      have h1 : s[pos]! = s[pos]'hpos := by
        rw [Array.getElem!_eq_getD, Array.getElem_eq_getD]
      -- h1 : s[pos]! = s[pos]'hpos; the proof-carrying read is
      -- definitionally the plain read:
      have h2 : s[pos]'hpos = s[pos] := rfl
      rw [h2] at h1
      exact h1
    rw [hposnb] at hhead
    by_cases hdig : isDigit s[pos] = true
    · rw [if_pos hdig] at hempty
      -- hempty : (takeWhile isDigit s (pos+1) ("" push s[pos])).fst =
      -- "".  But the pushed accumulator keeps s[pos] as its first
      -- char (a takeWhile result is acc ++ scanned, and the acc is
      -- returned verbatim in the stop case).  Simplest sound route:
      -- the takeWhile result string at least contains the pushed
      -- char (acc prefix); derive the contradiction generically:
      exfalso
      -- If the scan stopped immediately (or not), the acc-prefix
      -- remains: use the length law takeWhile_length from the lexer
      -- module (it is public there):
      have hlen := takeWhile_length isDigit s (pos + 1)
        (String.singleton s[pos])
      -- hlen : result.len = 1 + (result.end - (pos+1)) ≥ 1 (the acc
      -- prefix).hempty says that very .1 is "" (length 0):
      rw [show ("".push s[pos]) = String.singleton s[pos] from rfl,
        String.isEmpty_iff] at hempty
      rw [hempty] at hlen
      simp at hlen
      -- hlen : 0 = 1 + (end - (pos+1)); a Nat difference is ≥ 0:
      omega
    · rw [if_neg hdig] at hempty
      -- the false branch is ("", pos): hdig contradicts hhead:
      exact absurd hhead hdig
  rw [if_neg hnonempty]

/-- Over an all-digit array, the digit scan from 0 runs to the end:
    the pair is the whole text and the array size.  Structural route:
    the walk consumes one digit per step; an induction over the
    remaining length with the definitional step closes it. -/
theorem takeWhile_digits_end {s : Array Char}
    (hall : ∀ k : Nat, k < s.size → isDigit s[k]! = true) :
    takeWhile isDigit s 0 "" = (String.ofList (s.toList), s.size) := by
  -- the general form: from any pos with an all-digit tail:
  have key : ∀ (m : Nat), m ≤ s.size → ∀ (pos : Nat) (_hp : pos + m = s.size)
      (acc : String),
      takeWhile isDigit s pos acc
        = (acc ++ String.ofList (((s.toList).drop pos)), s.size) := by
    intro m
    induction m with
    | zero =>
        intro _hle pos hp acc
        -- pos = s.size: the scan is past the end:
        have hs : pos = s.size := by omega
        subst hs
        rw [takeWhile.eq_def (s := s) (pos := s.size) (acc := acc)]
        rw [dif_neg (Nat.lt_irrefl _)]
        rw [List.drop_eq_nil_of_le (show s.toList.length ≤ s.size by simp)]
        simp
    | succ m' ih =>
        intro _hle pos hp acc
        have hpos : pos < s.size := by omega
        rw [takeWhile.eq_def (s := s) (pos := pos) (acc := acc)]
        rw [dif_pos hpos]
        -- the head char is a digit (all-digit array):
        have hh : isDigit s[pos] = true := by
          have hb : s[pos]! = s[pos] := by
            simp [hpos]
          rw [← hb]
          exact hall pos hpos
        rw [if_pos hh, String.push_eq_append]
        -- the recursion at pos + 1 with the extended accumulator;
        -- the drop shifts by one (the head is consumed):
        have hrec := ih (by omega) (pos + 1) (by omega)
          (acc ++ String.singleton s[pos])
        rw [hrec]
        -- the singleton prefix and the shifted drop compose to the
        -- unshifted drop (cons shape of the dropped list):
        have hlen : (s.toList).length = s.size := by simp
        have hpos2 : pos < (s.toList).length := by rw [hlen]; exact hpos
        have h1 : (s.toList).drop pos
            = s[pos] :: (s.toList).drop (pos + 1) :=
          List.drop_eq_getElem_cons hpos2
        rw [h1, String.ofList_cons, ← String.append_assoc]
  exact key s.size (Nat.le_refl _) 0 (Nat.zero_add _) ""
/-- `lexInt` on a digit-headed array: the `-` guard fails (the head
    is a digit), so the result is the `.intLit` mapping of `lexUnsigned`
    at `pos`. -/
theorem lexInt_nonneg_head {s : Array Char} {pos : Nat}
    (_hpos : pos < s.size)
    (hhead : isDigit s[pos]! = true) :
    lexInt s pos =
      (lexUnsigned s pos).map (fun p => (.intLit p.1, p.2)) := by
  rw [lexInt]
  -- the `-` guard is false: the decide fires only when both hold,
  -- and the head is a digit (never '-'):
  have hm : ¬ ((decide (pos < s.size) && (s[pos]! == '-')) = true) := by
    intro hh
    rw [Bool.and_eq_true] at hh
    obtain ⟨_h1, hneg⟩ := hh
    rw [digit_not_minus hhead] at hneg
    exact Bool.noConfusion hneg
  rw [if_neg hm]
  -- both forms case on lexUnsigned's outcome; `map` is that match:
  cases hlu : lexUnsigned s pos with
  | ok p => rfl
  | error e => rfl

/-- `lexUnsigned` agrees on the appended array when every digit scan
    the literal shape could take stops inside the first array (the
    stop bounds force all lookahead positions into `s` in the taken
    branches). -/
theorem lexUnsigned_append_left {s t : Array Char} {pos : Nat}
    (htw : ∀ (p : Char → Bool) (q : Nat), pos ≤ q →
      (takeWhile p s q "").2 < s.size) :
    lexUnsigned (s ++ t) pos = lexUnsigned s pos := by
  -- the decimal scan's stop inside s bounds pos itself
  have hposlt : pos < s.size :=
    Nat.lt_of_le_of_lt (takeWhile_ge isDigit s pos "")
      (htw isDigit pos (Nat.le_refl pos))
  -- the hex/octal/decimal prefix conditions agree
  have hcondx : (decide (pos + 1 < (s ++ t).size) && (s ++ t)[pos]! == '0' && (s ++ t)[pos + 1]! == 'x')
      = (decide (pos + 1 < s.size) && s[pos]! == '0' && s[pos + 1]! == 'x') := by
    rw [arrGetElem!_append_left (by omega : pos < s.size)]
    by_cases h1 : pos + 1 < s.size
    · rw [arrGetElem!_append_left h1]
      have hsz : decide (pos + 1 < (s ++ t).size) = decide (pos + 1 < s.size) := by
        rw [Array.size_append]
        by_cases h2 : pos + 1 < s.size
        · have : pos + 1 < s.size + t.size := by omega
          simp [h2, this]
        · have h3 : ¬ pos + 1 < s.size + t.size := by omega
          simp [h2, h3]
      rw [hsz]
    · -- pos + 1 ≥ s.size: the s-side condition is false; if the
      -- s++t side were true, the digit scan would run past pos+1
      have hsfalse : (decide (pos + 1 < s.size) && s[pos]! == '0' && s[pos + 1]! == 'x') = false := by
        have hd : decide (pos + 1 < s.size) = false := by
          rw [decide_eq_false (by omega : ¬ pos + 1 < s.size)]
        rw [hd]
        rfl
      rw [hsfalse]
      -- the s++t condition is false too: if its decide were true, the
      -- '0' at pos would make the digit scan run past pos+1
      cases hsd : decide (pos + 1 < (s ++ t).size) with
      | true =>
          -- the s++t condition's char read forces s[pos] = '0'
          by_cases hst0 : (s ++ t)[pos]! == '0'
          · have hst0char : (s ++ t)[pos]! = '0' := by
              apply eq_of_beq
              exact hst0
            have hs0 : (s[pos]'hposlt) = '0' := by
              rw [show s[pos]'hposlt = s[pos]! from (arrGetElem_bang_eq hposlt).symm]
              rw [show s[pos]! = (s ++ t)[pos]! from (arrGetElem!_append_left hposlt).symm]
              rw [hst0char]
            have hisdigit : isDigit (s[pos]'hposlt) = true := by
              rw [hs0]; rfl
            have hconsumes : pos + 1 ≤ (takeWhile isDigit s pos "").2 :=
              takeWhile_step_of hposlt hisdigit
            have hstop := htw isDigit pos (Nat.le_refl pos)
            exfalso
            omega
          · -- (s++t)[pos]! is not '0'; then neither is s[pos]!
            have hsp0 : (s[pos]! == '0') = false := by
              have hsagree : s[pos]! = (s ++ t)[pos]! :=
                (arrGetElem!_append_left hposlt).symm
              rw [hsagree]
              exact Bool.not_eq_true _ |>.mp hst0
            rw [hsp0, Bool.true_and, Bool.false_and]
      | false =>
          simp
  -- the octal prefix condition agrees (same shape as hex, with 'o')
  have hcondo : (decide (pos + 1 < (s ++ t).size) && (s ++ t)[pos]! == '0' && (s ++ t)[pos + 1]! == 'o')
      = (decide (pos + 1 < s.size) && s[pos]! == '0' && s[pos + 1]! == 'o') := by
    rw [arrGetElem!_append_left (by omega : pos < s.size)]
    by_cases h1 : pos + 1 < s.size
    · rw [arrGetElem!_append_left h1]
      have hsz : decide (pos + 1 < (s ++ t).size) = decide (pos + 1 < s.size) := by
        rw [Array.size_append]
        by_cases h2 : pos + 1 < s.size
        · have : pos + 1 < s.size + t.size := by omega
          simp [h2, this]
        · have h3 : ¬ pos + 1 < s.size + t.size := by omega
          simp [h2, h3]
      rw [hsz]
    · have hsfalse : (decide (pos + 1 < s.size) && s[pos]! == '0' && s[pos + 1]! == 'o') = false := by
        have hd : decide (pos + 1 < s.size) = false := by
          rw [decide_eq_false (by omega : ¬ pos + 1 < s.size)]
        rw [hd]
        rfl
      rw [hsfalse]
      cases hsd : decide (pos + 1 < (s ++ t).size) with
      | true =>
          by_cases hst0 : (s ++ t)[pos]! == '0'
          · have hst0char : (s ++ t)[pos]! = '0' := by
              apply eq_of_beq
              exact hst0
            have hs0 : (s[pos]'hposlt) = '0' := by
              rw [show s[pos]'hposlt = s[pos]! from (arrGetElem_bang_eq hposlt).symm]
              rw [show s[pos]! = (s ++ t)[pos]! from (arrGetElem!_append_left hposlt).symm]
              rw [hst0char]
            have hisdigit : isDigit (s[pos]'hposlt) = true := by
              rw [hs0]; rfl
            have hconsumes : pos + 1 ≤ (takeWhile isDigit s pos "").2 :=
              takeWhile_step_of hposlt hisdigit
            have hstop := htw isDigit pos (Nat.le_refl pos)
            exfalso
            omega
          · have hsp0 : (s[pos]! == '0') = false := by
              have hsagree : s[pos]! = (s ++ t)[pos]! :=
                (arrGetElem!_append_left hposlt).symm
              rw [hsagree]
              exact Bool.not_eq_true _ |>.mp hst0
            rw [hsp0, Bool.true_and, Bool.false_and]
      | false =>
          simp
  -- main body
  rw [lexUnsigned, lexUnsigned, hcondx]
  split
  · rename_i hx
    have htwx : takeWhile isHexDigit (s ++ t) (pos + 2) ""
        = takeWhile isHexDigit s (pos + 2) "" :=
      takeWhile_append_left (htw isHexDigit (pos + 2) (by omega))
    rw [htwx]
  · rename_i hx
    rw [hcondo]
    split
    · rename_i ho
      have htwo : takeWhile isOctDigit (s ++ t) (pos + 2) ""
          = takeWhile isOctDigit s (pos + 2) "" :=
        takeWhile_append_left (htw isOctDigit (pos + 2) (by omega))
      rw [htwo]
    · rename_i ho
      have htwd : takeWhile isDigit (s ++ t) pos ""
          = takeWhile isDigit s pos "" :=
        takeWhile_append_left (htw isDigit pos (by omega))
      rw [htwd]

/-- `lexInt` agrees on the appended array under the same boundary
    conditions (the leading `-` check reads at `pos` only). -/
theorem lexInt_append_left {s t : Array Char} {pos : Nat}
    (htw : ∀ (p : Char → Bool) (q : Nat), pos ≤ q →
      (takeWhile p s q "").2 < s.size) :
    lexInt (s ++ t) pos = lexInt s pos := by
  have hposlt : pos < s.size :=
    Nat.lt_of_le_of_lt (takeWhile_ge isDigit s pos "")
      (htw isDigit pos (Nat.le_refl pos))
  have hcond : (pos < (s ++ t).size && (s ++ t)[pos]! == '-')
      = (pos < s.size && s[pos]! == '-') := by
    rw [arrGetElem!_append_left hposlt]
    have hdec : decide (pos < (s ++ t).size) = decide (pos < s.size) := by
      rw [Array.size_append]
      have h1 : pos < s.size := hposlt
      have this2 : pos < s.size + t.size := by omega
      simp [h1, this2]
    rw [hdec]
  rw [lexInt, lexInt, hcond]
  by_cases hneg : pos < s.size && s[pos]! == '-'
  · rw [if_pos hneg, if_pos hneg]
    -- the recursive lexUnsigned at pos+1: shift the hypotheses
    have htw' : ∀ (p : Char → Bool) (q : Nat), pos + 1 ≤ q →
        (takeWhile p s q "").2 < s.size := by
      intro p q hq1
      exact htw p q (by omega)
    rw [lexUnsigned_append_left htw']
  · rw [if_neg hneg, if_neg hneg]
    rw [lexUnsigned_append_left htw]

/-- `lexToken` agrees on the appended array when the token starting at
    `pos` lies entirely inside `s`: no string literal starts in `s`
    from `pos` on, every scan stops inside `s`, and there is room for
    two-character lookahead in `s`. -/
theorem lexToken_append_left {s t : Array Char} {pos : Nat}
    (hpos : pos < s.size)
    (hpos2 : pos + 2 < s.size)
    (hnostr : ∀ (q : Nat), pos ≤ q → q < s.size → s[q]! ≠ '"')
    (htw : ∀ (p : Char → Bool) (q : Nat) (acc : String), pos ≤ q →
      (takeWhile p s q acc).2 < s.size) :
    lexToken (s ++ t) pos (by rw [Array.size_append]; omega)
      = lexToken s pos hpos := by
  have hlt : pos < (s ++ t).size := by rw [Array.size_append]; omega
  have heq : (s ++ t)[pos]'hlt = s[pos]'hpos := arrGetElem_append_left hpos
  -- dispatch on the shared first character via the goal's match
  rw [lexToken, lexToken]
  simp only [heq]
  -- per-branch handling
  all_goals simp_all
  all_goals (try split)
  all_goals (try simp_all)
  all_goals (try omega)
  all_goals (try rfl)
  -- the ':' branch: the lookahead conditions agree (chars in s)
  case h_10 =>
    rename_i _ heqc
    have heq1 : (s ++ t)[pos + 1]! = s[pos + 1]! :=
      arrGetElem!_append_left (t := t) (by omega : pos + 1 < s.size)
    by_cases hc : pos + 1 < s.size ∧ s[pos + 1]! = ':'
    · rw [if_pos (by
          refine ⟨by omega, ?_⟩
          rw [heq1]
          exact hc.2), if_pos hc]
    · rw [if_neg (by
          intro h2
          rw [heq1] at h2
          apply hc
          exact ⟨by omega, h2.2⟩), if_neg hc]
  case h_11 =>
    rename_i _ heqc
    have heq1 : (s ++ t)[pos + 1]! = s[pos + 1]! :=
      arrGetElem!_append_left (t := t) (by omega : pos + 1 < s.size)
    by_cases hc : pos + 1 < s.size ∧ s[pos + 1]! = '.'
    · rw [if_pos (by
          refine ⟨by omega, ?_⟩
          rw [heq1]
          exact hc.2), if_pos hc]
    · rw [if_neg (by
          intro h2
          rw [heq1] at h2
          apply hc
          exact ⟨by omega, h2.2⟩), if_neg hc]
  -- the identifier/digit default branch (h_13)
  case h_13 =>
    -- the conditions (isAlpha s[pos] || s[pos] == '_') etc. are the
    -- same on both sides (already s-form after simp only [heq])
    by_cases halpha : isAlpha s[pos] = true ∨ s[pos] = '_'
    · -- the identifier scan agrees; reduce both ifs and rewrite the scans
      have hscan : takeWhile isIdentChar (s ++ t) (pos + 1)
          (String.singleton s[pos])
          = takeWhile isIdentChar s (pos + 1) (String.singleton s[pos]) :=
        takeWhile_append_left (htw isIdentChar (pos + 1) _ (by omega))
      simp only [if_pos halpha, hscan]
    · rw [if_neg halpha, if_neg halpha]
      by_cases hdigit : isDigit s[pos] = true ∨ s[pos] = '-'
      · rw [if_pos hdigit, if_pos hdigit]
        have hilex : lexInt (s ++ t) pos = lexInt s pos :=
          lexInt_append_left (fun p q hq => htw p q "" hq)
        split
        · rename_i tL pL hiL
          have hR : lexInt s pos = .ok (tL, pL) := by
            rw [← hilex]; exact hiL
          split
          · rename_i tR pR hiR
            rw [hR] at hiR
            injection hiR with htp
            cases htp
            rfl
          · -- s errored but s++t ok: contradiction via hR
            rename_i eR hiR
            rw [hR] at hiR
            exact absurd hiR (by simp)
        · rename_i eL hiL
          have hR : lexInt s pos = .error eL := by
            rw [← hilex]; exact hiL
          split
          · -- s ok but s++t errored: contradiction
            rename_i tR pR hiR
            rw [hR] at hiR
            exact absurd hiR (by simp)
          · rename_i eR hiR
            rw [hR] at hiR
            injection hiR with hee
            subst hee
            rfl
      · rw [if_neg hdigit, if_neg hdigit]


theorem arrGetElem_append_right' {s t : Array Char} {k : Nat}
    (h : k < t.size) :
    (s ++ t)[s.size + k]'(by rw [Array.size_append]; omega) = t[k]'h := by
  have hlt : s.size + k < (s ++ t).size := by rw [Array.size_append]; omega
  have h1 := Array.getElem_append_right (xs := s) (ys := t)
    (i := s.size + k) (h := hlt) (hle := by omega)
  rw [show (t[k]'h) = t[s.size + k - s.size]'(by
      show s.size + k - s.size < t.size
      omega) from by
    congr 1
    omega]
  exact h1

theorem arrGetElem!_append_right' {s t : Array Char} {k : Nat}
    (hle : k < t.size) :
    (s ++ t)[s.size + k]! = t[k]! := by
  have hlt : s.size + k < (s ++ t).size := by rw [Array.size_append]; omega
  rw [arrGetElem!_of_lt (a := (s ++ t)) hlt, arrGetElem!_of_lt (a := t) hle]
  exact arrGetElem_append_right' hle

/-- `takeWhile` past the join is the tail's scan, with the stop
    position offset by `s.size` (the string result agrees). -/
theorem takeWhile_append_right {p : Char → Bool} {s t : Array Char} {k : Nat}
    {acc : String} :
    takeWhile p (s ++ t) (s.size + k) acc
      = ((takeWhile p t k acc).1, s.size + (takeWhile p t k acc).2) := by
  have key : ∀ (q : Nat) (acc : String), k ≤ q →
      takeWhile p (s ++ t) (s.size + q) acc
        = ((takeWhile p t q acc).1, s.size + (takeWhile p t q acc).2) := by
    intro q acc
    induction q, acc using takeWhile.induct (p := p) (s := t) with
    | case1 q acc h c hp ih =>
        intro _
        have hlt : s.size + q < (s ++ t).size := by rw [Array.size_append]; omega
        rw [takeWhile.eq_def, takeWhile.eq_def]
        rw [dif_pos hlt, dif_pos h]
        rw [show (s ++ t)[s.size + q]'hlt = t[q]'h from arrGetElem_append_right' h]
        rw [if_pos hp, if_pos hp]
        have hih := ih (by omega)
        rw [show s.size + q + 1 = s.size + (q + 1) from by omega]
        exact hih
    | case2 q acc h c hp =>
        intro _
        have hlt : s.size + q < (s ++ t).size := by rw [Array.size_append]; omega
        rw [takeWhile.eq_def, takeWhile.eq_def]
        rw [dif_pos hlt, dif_pos h]
        rw [show (s ++ t)[s.size + q]'hlt = t[q]'h from arrGetElem_append_right' h]
        rw [if_neg hp, if_neg hp]
    | case3 q acc h =>
        intro _
        rw [takeWhile.eq_def, takeWhile.eq_def]
        rw [dif_neg (by rw [Array.size_append]; omega), dif_neg h]
  exact key k acc (Nat.le_refl k)


/-- `lexUnsigned` past the join is the tail's scan with the end
    position offset — the character-window agreement (the reads at
    `s.size + k` and `s.size + k + 1` agree with `t`'s while inside
    `t`, and the three prefix conditions agree), then the digit
    scans transport by `takeWhile_append_right`. -/
theorem lexUnsigned_append_right_ok {s t : Array Char} {k : Nat}
    (hpos : k < t.size)
    {n : Int} {p : Nat}
    (hok : lexUnsigned t k = .ok (n, p)) :
    lexUnsigned (s ++ t) (s.size + k) = .ok (n, p + s.size) := by
  have hread0 : (s ++ t)[s.size + k]! = t[k]! := by
    have hlt : s.size + k < (s ++ t).size := by rw [Array.size_append]; omega
    rw [show (s ++ t)[s.size + k]! = (if h : s.size + k < (s ++ t).size
      then (s ++ t)[s.size + k] else default) from rfl, dif_pos hlt]
    rw [show t[k]! = (if h : k < t.size then t[k] else default) from rfl]
    rw [dif_pos hpos]
    exact arrGetElem_append_right' hpos
  have hcondx : (decide (s.size + k + 1 < (s ++ t).size) && (s ++ t)[s.size + k]! == '0'
      && (s ++ t)[s.size + k + 1]! == 'x')
      = (decide (k + 1 < t.size) && t[k]! == '0' && t[k + 1]! == 'x') := by
    rw [hread0]
    by_cases h1 : k + 1 < t.size
    · have hlt1 : s.size + k + 1 < (s ++ t).size := by
        rw [Array.size_append]; omega
      have hread1 : (s ++ t)[s.size + k + 1]! = t[k + 1]! :=
        arrGetElem!_append_right' h1
      rw [hread1]
      rw [decide_eq_true hlt1, decide_eq_true h1]
    · rw [decide_eq_false (by omega : ¬ k + 1 < t.size)]
      rw [Array.size_append]
      rw [decide_eq_false (by omega : ¬ s.size + k + 1 < s.size + t.size)]
      simp
  have hcondo : (decide (s.size + k + 1 < (s ++ t).size) && (s ++ t)[s.size + k]! == '0'
      && (s ++ t)[s.size + k + 1]! == 'o')
      = (decide (k + 1 < t.size) && t[k]! == '0' && t[k + 1]! == 'o') := by
    rw [hread0]
    by_cases h1 : k + 1 < t.size
    · have hlt1 : s.size + k + 1 < (s ++ t).size := by
        rw [Array.size_append]; omega
      have hread1 : (s ++ t)[s.size + k + 1]! = t[k + 1]! :=
        arrGetElem!_append_right' h1
      rw [hread1]
      rw [decide_eq_true hlt1, decide_eq_true h1]
    · rw [decide_eq_false (by omega : ¬ k + 1 < t.size)]
      rw [Array.size_append]
      rw [decide_eq_false (by omega : ¬ s.size + k + 1 < s.size + t.size)]
      simp
  rw [lexUnsigned.eq_def (s := s ++ t) (pos := s.size + k)]
  rw [lexUnsigned.eq_def (s := t) (pos := k)] at hok
  rw [hcondx, hcondo]
  -- case on the three prefix conditions explicitly; hok (t-side,
  -- same conditions after the rewrite) resolves in tandem
  by_cases hx : (decide (k + 1 < t.size) && t[k]! == '0' && t[k + 1]! == 'x') = true
  · rw [if_pos hx]
    rw [if_pos hx] at hok
    -- hex: the scan past the join is the offset scan
    have hscan : takeWhile isHexDigit (s ++ t) (s.size + k + 2) ""
        = ((takeWhile isHexDigit t (k + 2) "").1,
           s.size + (takeWhile isHexDigit t (k + 2) "").2) :=
      takeWhile_append_right (p := isHexDigit) (s := s) (t := t)
        (k := k + 2) (acc := "")
    rw [hscan]
    simp only []
    by_cases hempty : (takeWhile isHexDigit t (k + 2) "").1.isEmpty = true
    · rw [if_pos hempty]
      rw [if_pos hempty] at hok
      exact absurd hok (by simp)
    · rw [if_neg hempty]
      rw [if_neg hempty] at hok
      -- extract n and p from hok's ok-pair:
      obtain ⟨hn, hp2⟩ := Prod.mk.inj (Except.ok.inj hok)
      subst hn
      subst hp2
      rw [show s.size + (takeWhile isHexDigit t (k + 2) "").2
        = (takeWhile isHexDigit t (k + 2) "").2 + s.size from by omega]
  · rw [if_neg hx]
    rw [if_neg hx] at hok
    by_cases ho : (decide (k + 1 < t.size) && t[k]! == '0' && t[k + 1]! == 'o') = true
    · rw [if_pos ho]
      rw [if_pos ho] at hok
      have hscan : takeWhile isOctDigit (s ++ t) (s.size + k + 2) ""
          = ((takeWhile isOctDigit t (k + 2) "").1,
             s.size + (takeWhile isOctDigit t (k + 2) "").2) :=
        takeWhile_append_right (p := isOctDigit) (s := s) (t := t)
          (k := k + 2) (acc := "")
      rw [hscan]
      simp only []
      by_cases hempty : (takeWhile isOctDigit t (k + 2) "").1.isEmpty = true
      · rw [if_pos hempty]
        rw [if_pos hempty] at hok
        exact absurd hok (by simp)
      · rw [if_neg hempty]
        rw [if_neg hempty] at hok
        obtain ⟨hn, hp2⟩ := Prod.mk.inj (Except.ok.inj hok)
        subst hn
        subst hp2
        rw [show s.size + (takeWhile isOctDigit t (k + 2) "").2
          = (takeWhile isOctDigit t (k + 2) "").2 + s.size from by omega]
    · rw [if_neg ho]
      rw [if_neg ho] at hok
      have hscan : takeWhile isDigit (s ++ t) (s.size + k) ""
          = ((takeWhile isDigit t k "").1,
             s.size + (takeWhile isDigit t k "").2) :=
        takeWhile_append_right (p := isDigit) (s := s) (t := t)
          (k := k) (acc := "")
      rw [hscan]
      simp only []
      by_cases hempty : (takeWhile isDigit t k "").1.isEmpty = true
      · rw [if_pos hempty]
        rw [if_pos hempty] at hok
        exact absurd hok (by simp)
      · rw [if_neg hempty]
        rw [if_neg hempty] at hok
        obtain ⟨hn, hp2⟩ := Prod.mk.inj (Except.ok.inj hok)
        subst hn
        subst hp2
        rw [show s.size + (takeWhile isDigit t k "").2
          = (takeWhile isDigit t k "").2 + s.size from by omega]


/-- `lexInt` past the join is the tail's scan with the end
    position offset — SUCCESS-transport form. -/
theorem lexInt_append_right_ok {s t : Array Char} {k : Nat}
    (hpos : k < t.size)
    (htw : ∀ (p : Char → Bool) (q : Nat), k ≤ q →
      (takeWhile p t q "").2 < t.size)
    {tok : Token} {p : Nat} {_hp : k < p}
    (hok : lexInt t k = .ok (tok, p)) :
    lexInt (s ++ t) (s.size + k) = .ok (tok, p + s.size) := by
  -- the leading `-` check agrees (char reads in t), then the
  -- unsigned part transports by the window lemma
  rw [lexInt.eq_def (s := t) (pos := k)] at hok
  rw [lexInt.eq_def (s := s ++ t) (pos := s.size + k)]
  have hread0 : (s ++ t)[s.size + k]! = t[k]! :=
    arrGetElem!_append_right' hpos
  by_cases hneg : (decide (k < t.size) && t[k]! == '-') = true
  · -- t-side takes the '-' branch; the s++t side must too
    have hlt : s.size + k < (s ++ t).size := by
      rw [Array.size_append]; omega
    have hnegrw : (decide (s.size + k < (s ++ t).size)
        && (s ++ t)[s.size + k]! == '-') = true := by
      rw [hread0, decide_eq_true hlt]
      have : decide (k < t.size) = true := decide_eq_true hpos
      rw [this] at hneg
      exact hneg
    rw [if_pos hnegrw]
    rw [if_pos hneg] at hok
    split at hok
    · -- t-side ok: transport the unsigned part from k+1
      rename_i n p1 hu
      -- k+1 < t.size: the '-' at k is followed by the unsigned
      -- start inside t. The scan premise htw bounds every scan
      -- stop inside t; in particular the unsigned's digit scan
      -- from ≥ k+1 stops inside t, which forces k+1 < t.size:
      -- the stop position is ≥ the start (takeWhile_ge), and if
      -- k+1 ≥ t.size the scan from k+1 stops AT k+1 ≥ t.size
      -- (past-the-end dif_neg), contradicting the < t.size stop.
      have hlt1 : k + 1 < t.size := by
        have hstop := htw isDigit (k + 2) (by omega)
        rw [takeWhile.eq_def (s := t) (pos := k + 2) (acc := "")] at hstop
        by_cases hge : k + 1 < t.size
        · exact hge
        · rw [dif_neg (by omega : ¬ k + 2 < t.size)] at hstop
          simp only at hstop
          omega
      have hu' : lexUnsigned (s ++ t) (s.size + (k + 1))
          = .ok (n, p1 + s.size) :=
        lexUnsigned_append_right_ok (s := s) (t := t)
          (k := k + 1) hlt1 hu
      -- extract the t-side result and rewrite the goal's match
      have hpair := Prod.mk.inj (Except.ok.inj hok)
      obtain ⟨htok, hpp⟩ := hpair
      subst htok
      have hpp' : p = p1 := by omega
      subst hpp'
      rw [show s.size + (k + 1) = s.size + k + 1 from by omega] at hu'
      rw [hu']
    · exact absurd hok (by simp)
  · rw [if_neg (by
      intro hc
      rw [hread0] at hc
      rw [decide_eq_true (by rw [Array.size_append]; omega : s.size + k < (s ++ t).size)] at hc
      have hdec : decide (k < t.size) = true := decide_eq_true hpos
      rw [hdec] at hneg
      exact absurd hc hneg)]
    rw [if_neg hneg] at hok
    split at hok
    · rename_i n p1 hu
      have hu' : lexUnsigned (s ++ t) (s.size + k)
          = .ok (n, p1 + s.size) :=
        lexUnsigned_append_right_ok (s := s) (t := t) (k := k) hpos hu
      have hpair := Prod.mk.inj (Except.ok.inj hok)
      obtain ⟨htok, hpp⟩ := hpair
      subst htok
      have hpp' : p = p1 := by omega
      subst hpp'
      rw [hu']
    · exact absurd hok (by simp)


theorem lexToken_append_right_ok {s t : Array Char} {k : Nat}
    {tok : Token} {p : Nat} {hp : k < p} (hpos : k < t.size)
    (htw : ∀ (p : Char → Bool) (q : Nat), k ≤ q →
      (takeWhile p t q "").2 < t.size)
    (hnostr : t[k]'hpos ≠ '"')
    (hok : lexToken t k hpos = .ok (tok, ⟨p, hp⟩)) :
    lexToken (s ++ t) (s.size + k) (by rw [Array.size_append]; omega)
        = .ok (tok, ⟨s.size + p, by omega⟩) := by
  have hlt : s.size + k < (s ++ t).size := by rw [Array.size_append]; omega
  have heq : (s ++ t)[s.size + k]'hlt = t[k]'hpos :=
    arrGetElem_append_right' hpos
  -- transport the RHS through the char equality: case on t[k]'hpos
  -- is over 14 chars — instead use the general match transport:
  -- generalize the char and the hypothesis hok
  rw [lexToken.eq_def (s := t) (pos := k) (h := hpos)] at hok
  simp only [] at hok
  split at hok
  case h_1 heqc =>
    have hpair := Except.ok.inj hok
    obtain ⟨htok, hpp⟩ := Prod.mk.inj hpair
    subst htok
    have hk1 : p = k + 1 := by injection hpp with hpv; omega
    subst hk1
    rw [lexToken.eq_def (s := s ++ t) (pos := s.size + k) (h := hlt)]
    simp only [heq, heqc]
    rfl
  case h_2 heqc =>
    have hpair := Except.ok.inj hok
    obtain ⟨htok, hpp⟩ := Prod.mk.inj hpair
    subst htok
    have hk1 : p = k + 1 := by injection hpp with hpv; omega
    subst hk1
    rw [lexToken.eq_def (s := s ++ t) (pos := s.size + k) (h := hlt)]
    simp only [heq, heqc]
    rfl
  case h_3 heqc =>
    have hpair := Except.ok.inj hok
    obtain ⟨htok, hpp⟩ := Prod.mk.inj hpair
    subst htok
    have hk1 : p = k + 1 := by injection hpp with hpv; omega
    subst hk1
    rw [lexToken.eq_def (s := s ++ t) (pos := s.size + k) (h := hlt)]
    simp only [heq, heqc]
    rfl
  case h_4 heqc =>
    have hpair := Except.ok.inj hok
    obtain ⟨htok, hpp⟩ := Prod.mk.inj hpair
    subst htok
    have hk1 : p = k + 1 := by injection hpp with hpv; omega
    subst hk1
    rw [lexToken.eq_def (s := s ++ t) (pos := s.size + k) (h := hlt)]
    simp only [heq, heqc]
    rfl
  case h_5 heqc =>
    have hpair := Except.ok.inj hok
    obtain ⟨htok, hpp⟩ := Prod.mk.inj hpair
    subst htok
    have hk1 : p = k + 1 := by injection hpp with hpv; omega
    subst hk1
    rw [lexToken.eq_def (s := s ++ t) (pos := s.size + k) (h := hlt)]
    simp only [heq, heqc]
    rfl
  case h_6 heqc =>
    have hpair := Except.ok.inj hok
    obtain ⟨htok, hpp⟩ := Prod.mk.inj hpair
    subst htok
    have hk1 : p = k + 1 := by injection hpp with hpv; omega
    subst hk1
    rw [lexToken.eq_def (s := s ++ t) (pos := s.size + k) (h := hlt)]
    simp only [heq, heqc]
    rfl
  case h_7 heqc =>
    have hpair := Except.ok.inj hok
    obtain ⟨htok, hpp⟩ := Prod.mk.inj hpair
    subst htok
    have hk1 : p = k + 1 := by injection hpp with hpv; omega
    subst hk1
    rw [lexToken.eq_def (s := s ++ t) (pos := s.size + k) (h := hlt)]
    simp only [heq, heqc]
    rfl
  case h_8 heqc =>
    have hpair := Except.ok.inj hok
    obtain ⟨htok, hpp⟩ := Prod.mk.inj hpair
    subst htok
    have hk1 : p = k + 1 := by injection hpp with hpv; omega
    subst hk1
    rw [lexToken.eq_def (s := s ++ t) (pos := s.size + k) (h := hlt)]
    simp only [heq, heqc]
    rfl
  case h_9 heqc =>
    have hpair := Except.ok.inj hok
    obtain ⟨htok, hpp⟩ := Prod.mk.inj hpair
    subst htok
    have hk1 : p = k + 1 := by injection hpp with hpv; omega
    subst hk1
    rw [lexToken.eq_def (s := s ++ t) (pos := s.size + k) (h := hlt)]
    simp only [heq, heqc]
    rfl
  -- h_10 (':'): the lookahead conditions agree
  case h_10 heqc =>
    -- the lookahead position must be inside t (hok's if is .ok, so
    -- the t-side condition decided one way or the other with k+1
    -- reads); first reduce hok's if
    by_cases hcond : (decide (k + 1 < t.size) && t[k + 1]! == ':') = true
    · -- the t-side takes colonColon: the s++t side does too (the
      -- lookahead chars agree when k+1 < t.size)
      have hlt1 : k + 1 < t.size := by
        -- hcond's first conjunct is true
        have hdec := Bool.and_eq_true_iff.mp hcond
        have : decide (k + 1 < t.size) = true := hdec.1
        exact of_decide_eq_true this
      have hlk : (s ++ t)[s.size + k + 1]! = t[k + 1]! :=
        arrGetElem!_append_right' hlt1
      have hk2 : p = k + 2 := by
        rw [if_pos hcond] at hok
        have hpair := Except.ok.inj hok
        obtain ⟨htok, hpp⟩ := Prod.mk.inj hpair
        subst htok
        injection hpp with hpv
        omega
      subst hk2
      rw [lexToken.eq_def (s := s ++ t) (pos := s.size + k) (h := hlt)]
      simp only [heq, heqc]
      rw [show (s ++ t)[s.size + k + 1]! = t[k + 1]! from hlk]
      -- the size decide is true (k+1 < t.size gives s.size+k+1 <
      -- (s++t).size); the char part of hcond then matches
      have hdect := decide_eq_true (show s.size + k + 1 < (s ++ t).size from by
        rw [Array.size_append]; omega)
      rw [hdect]
      have hcond2 : (t[k + 1]! == ':') = true :=
        (Bool.and_eq_true_iff.mp hcond).2
      rw [hcond2]
      simp only [Bool.true_and, reduceIte, Except.pure]
      -- hok's colonColon case forces tok = .colonColon (hpair was
      -- derived above in hk2's proof; redo it here for tok)
      have htokcc : tok = Token.colonColon := by
        rw [if_pos hcond] at hok
        have hpair := Except.ok.inj hok
        exact (Prod.mk.inj hpair).1.symm
      rw [htokcc]
      rfl
    · rw [if_neg hcond] at hok
      have hpair := Except.ok.inj hok
      obtain ⟨htok, hpp⟩ := Prod.mk.inj hpair
      subst htok
      have hk1 : p = k + 1 := by injection hpp with hpv; omega
      subst hk1
      rw [lexToken.eq_def (s := s ++ t) (pos := s.size + k) (h := hlt)]
      simp only [heq, heqc]
      -- the s++t-side condition must be false: if its size-decide
      -- were true, then k+1 < t.size (sizes), the reads agree, and
      -- the conditions would be equal — contradicting hcond
      -- the s++t-side SIZE decide: (s.size + k + 1 <
      -- (s++t).size) iff (k+1 < t.size); hcond (the t-side
      -- condition is false) forces k+1 ≥ t.size... NO: hcond being
      -- the NEGATION of (decide && read) with decide-t TRUE forces
      -- only the read false. The size decide is separately true
      -- exactly when k+1 < t.size. Case on it:
      by_cases hlt1 : k + 1 < t.size
      · -- size decide true; the reads agree, so the s++t-side
        -- whole condition is (true && read) = read = false — the
        -- if selects the else: colon at k+1 — matching hok
        have hlk : (s ++ t)[s.size + k + 1]! = t[k + 1]! :=
          arrGetElem!_append_right' hlt1
        have hdect : decide (k + 1 < t.size) = true :=
          decide_eq_true hlt1
        have hcondf : (t[k + 1]! == ':') = false := by
          have hpair := Bool.and_eq_false_iff.mp (by
            cases hh : (decide (k + 1 < t.size) && t[k + 1]! == ':') with
            | true => exact absurd hh hcond
            | false => rfl)
          rw [hdect] at hpair
          exact hpair.resolve_left (by simp)
        rw [hlk, hcondf, Bool.and_false, if_neg (by simp)]
        rfl
      · rw [decide_eq_false (by
          rw [Array.size_append]
          omega)]
        rfl
  -- h_11 ('.'): hok is .ok, so the t-side condition must be true
  -- (the false branch throws), and the reads agree
  case h_11 heqc =>
    have hlt1 : k + 1 < t.size := by
      -- if k+1 ≥ t.size the t-side condition is false (decide false)
      -- and lexToken t throws — contradicting hok
      by_cases hc : k + 1 < t.size
      · exact hc
      · exfalso
        have hsd : decide (k + 1 < t.size) = false :=
          decide_eq_false (by omega)
        -- hok is already the if-form; the condition is
        -- (false && ...) = false, so hok is throw = Except.ok —
        -- contradiction
        rw [hsd, Bool.false_and, if_neg (by simp)] at hok
        exact absurd hok (by simp)
    have hlk : (s ++ t)[s.size + k + 1]! = t[k + 1]! :=
      arrGetElem!_append_right' hlt1
    have hdect : decide (k + 1 < t.size) = true :=
      decide_eq_true hlt1
    -- the read must be '.' (else the t side throws)
    have hcond : (decide (k + 1 < t.size) && t[k + 1]! == '.') = true := by
      cases hh : (decide (k + 1 < t.size) && t[k + 1]! == '.') with
      | true => rfl
      | false =>
          exfalso
          -- the condition is false, so lexToken's if selects the
          -- throw branch: hok becomes an error — contradiction
          have hcondneg : ¬ ((decide (k + 1 < t.size) && t[k + 1]! == '.') = true) := by
            rw [hh]; simp
          rw [if_neg hcondneg] at hok
          exact absurd hok (by simp)
    -- the s++t side: same reads, same condition — dotDot, offset
    have hlk : (s ++ t)[s.size + k + 1]! = t[k + 1]! :=
      arrGetElem!_append_right' hlt1
    have hk2 : p = k + 2 := by
      rw [if_pos hcond] at hok
      have hpair := Except.ok.inj hok
      obtain ⟨htok, hpp⟩ := Prod.mk.inj hpair
      subst htok
      injection hpp with hpv
      omega
    subst hk2
    have htokdd : tok = Token.dotDot := by
      rw [if_pos hcond] at hok
      have hpair := Except.ok.inj hok
      exact (Prod.mk.inj hpair).1.symm
    rw [htokdd]
    rw [lexToken.eq_def (s := s ++ t) (pos := s.size + k) (h := hlt)]
    simp only [heq, heqc]
    rw [decide_eq_true (by rw [Array.size_append]; omega), hlk]
    have hread : (t[k + 1]! == '.') = true :=
      (Bool.and_eq_true_iff.mp hcond).2
    rw [hread]
    rfl

  -- h_12 ('"'): excluded
  case h_12 heqc =>
    -- hnostr : t[k]'hpos ≠ '"'; heqc says the char IS '"'
    exact absurd (show t[k]'hpos = '"' from by rw [heqc]) hnostr
  -- h_13: ident/int
  case h_13 heqc =>
    -- the default branch: identifier or integer
    -- first: the char classes agree between the two sides (the char
    -- is shared), so both sides take the same sub-branch
    by_cases halpha : (isAlpha t[k] || t[k] == '_') = true
    · -- the identifier branch: the scans agree via the offset law
      rw [lexToken.eq_def (s := s ++ t) (pos := s.size + k) (h := hlt)]
      simp only [heq, heqc]
      rw [if_pos halpha]
      -- the s++t-side scan is the t-side scan (the offset law at
      -- the associated position, with the shared accumulator char)
      -- extract hok's t-side result: split the keywordToken match
      -- inside hok, then use the .ok extraction per branch
      rw [if_pos halpha] at hok
      cases hhk : keywordToken
          (takeWhile isIdentChar t (k + 1) (String.singleton t[k])).1 with
      | some tok2 =>
          -- hok's match selects the `some` arm (hhk); reduce it
          rw [hhk] at hok
          have htok : tok = tok2 := by
            have hpair := Except.ok.inj hok
            exact (Prod.mk.inj hpair).1.symm
          subst htok
          -- the s++t-side scan law (the position offset)
          have h := takeWhile_append_right (p := isIdentChar)
            (s := s) (t := t) (k := k + 1) (acc := String.singleton t[k])
          have hpos : s.size + (k + 1) = s.size + k + 1 := by omega
          rw [hpos] at h
          -- p from hok
          have hpp : p = (takeWhile isIdentChar t (k + 1)
              (String.singleton t[k])).2 := by
            have hpair := Except.ok.inj hok
            obtain ⟨_, hp2⟩ := Prod.mk.inj hpair
            injection hp2 with hpv
            omega
          subst hpp
          simp only [h]
          rw [hhk]
          rfl
      | none =>
          rw [hhk] at hok
          -- the reserved-contains check must be false (hok is .ok)
          by_cases hres : reservedNonFzn.contains
              (takeWhile isIdentChar t (k + 1) (String.singleton t[k])).1 = true
          · rw [if_pos hres] at hok
            exact absurd hok (by simp)
          · rw [if_neg hres] at hok
            -- the ident token; extract and transport
            have hpair := Except.ok.inj hok
            obtain ⟨htok, hpp⟩ := Prod.mk.inj hpair
            subst htok
            -- the scan offset law: replace the s++t-side scan by the
            -- t-side one (the goal is already the unfolded match)
            have h := takeWhile_append_right (p := isIdentChar)
              (s := s) (t := t) (k := k + 1) (acc := String.singleton t[k])
            have hpos : s.size + (k + 1) = s.size + k + 1 := by omega
            rw [hpos] at h
            -- rewrite the scan pair; simp handles the dependent
            -- .snd projection (the subtype property shifts by the
            -- offset, which the goal type already expects)
            simp only [h]
            rw [if_neg hres]
            -- hpp identifies p with the t-side scan position; use
            -- simp to also reduce the keywordToken match and the
            -- position arithmetic
            have hpp2 : p = (takeWhile isIdentChar t (k + 1)
                (String.singleton t[k])).2 := by
              injection hpp with hpv
              omega
            simp only [hpp2]
            rw [hhk]
            rfl
    · rw [lexToken.eq_def (s := s ++ t) (pos := s.size + k) (h := hlt)]
      simp only [heq, heqc]
      rw [if_neg halpha]
      by_cases hdigit : (isDigit t[k] || t[k] == '-') = true
      · rw [if_pos hdigit]
        -- the integer branch: the token/position transport
        -- (hok already unfolded; the s++t side's lexInt agrees by
        -- the same character-window argument)
        rw [if_neg halpha] at hok
        rw [if_pos hdigit] at hok
        -- reduce hok's dependent match on lexInt t k by splitting
        split at hok
        next tok2 p2 hli =>
          -- hli : lexInt t k = .ok (tok2, p2); hok gives tok/p
          have hpair := Except.ok.inj hok
          obtain ⟨htok, hpp⟩ := Prod.mk.inj hpair
          have htok2 : tok = tok2 := htok.symm
          have hpp2 : p = p2 := by
            injection hpp with hpv
            omega
          subst htok2
          subst hpp2
          -- the goal's match on lexInt (s++t) (s.size+k): the
          -- s++t-side lexInt succeeds with the same token and the
          -- offset position; split the goal's match
          split
          · -- s++t side ok: same token; the position is the t-side
            -- end plus s.size (the character window agrees)
            next tok3 p3 hli' =>
              -- the s++t side's lexInt is the offset of the t
              -- side's (lexInt_append_right); with hli (the t
              -- side's result) the positions satisfy
              -- p3 = p + s.size and tok3 = tok
              have hoffset := lexInt_append_right_ok (s := s) (t := t)
                (k := k) hpos htw hli
                (_hp := lexInt_gt (s := t) (pos := k) (t := tok) (p := p) hli)
              -- identify tok3/p3 with tok/(p+s.size) via hli' +
              -- hoffset, then close by proof irrelevance
              have hident : Except.ok (tok3, p3)
                  = Except.ok (tok, p + s.size) :=
                hli'.symm.trans hoffset
              obtain ⟨rfl, hpp3⟩ := (Prod.mk.inj (Except.ok.inj hident))
              have hpp3eq : p3 = s.size + p := by omega
              subst hpp3eq
              rfl
          · -- s++t side error — impossible: the same characters
            -- succeed on the t side; the offset law gives
            -- lexInt (s++t) .. = .map .. (lexInt t k), and hli
            -- says the t side succeeded
            rename_i e hlierr
            have hoffset := lexInt_append_right_ok (s := s) (t := t)
              (k := k) hpos htw hli
              (_hp := lexInt_gt (s := t) (pos := k) (t := tok) (p := p) hli)
            rw [hoffset] at hlierr
            exact absurd hlierr (by simp)
        · rename_i e hli
          exact absurd hok (by simp)
      · rw [if_neg hdigit]
        -- both sides throw; hok is .ok — contradiction
        exfalso
        rw [if_neg halpha, if_neg hdigit] at hok
        exact absurd hok (by simp)


/-- `skipToNewline` past the join is the tail's scan, offset. -/
theorem skipToNewline_append_right {s t : Array Char} {k : Nat} :
    skipToNewline (s ++ t) (s.size + k)
      = s.size + skipToNewline t k := by
  induction k using skipToNewline.induct (s := t) with
  | case1 k h hn =>
      have hlt : s.size + k < (s ++ t).size := by
        rw [Array.size_append]; omega
      rw [skipToNewline.eq_def (s := s ++ t) (pos := s.size + k)]
      rw [dif_pos hlt]
      rw [show (s ++ t)[s.size + k]'hlt = t[k]'h from arrGetElem_append_right' h]
      rw [if_pos hn]
      rw [skipToNewline.eq_def (s := t) (pos := k)]
      rw [dif_pos h, if_pos hn]
      omega
  | case2 k h hn ih =>
      have hlt : s.size + k < (s ++ t).size := by
        rw [Array.size_append]; omega
      rw [skipToNewline.eq_def (s := s ++ t) (pos := s.size + k)]
      rw [dif_pos hlt]
      rw [show (s ++ t)[s.size + k]'hlt = t[k]'h from arrGetElem_append_right' h]
      rw [if_neg hn]
      rw [skipToNewline.eq_def (s := t) (pos := k)]
      rw [dif_pos h, if_neg hn]
      rw [show s.size + k + 1 = s.size + (k + 1) from by omega]
      rw [ih]
  | case3 k h =>
      rw [skipToNewline.eq_def (s := s ++ t) (pos := s.size + k)]
      rw [dif_neg (by rw [Array.size_append]; omega)]
      rw [skipToNewline.eq_def (s := t) (pos := k)]
      rw [dif_neg h]

/-- `skipTrivia` past the join is the tail's skip, offset. -/
theorem skipTrivia_append_right {s t : Array Char} {k : Nat} :
    skipTrivia (s ++ t) (s.size + k) = s.size + skipTrivia t k := by
  induction k using skipTrivia.induct (s := t) with
  | case1 k h c hw ih =>
      have hlt : s.size + k < (s ++ t).size := by
        rw [Array.size_append]; omega
      rw [skipTrivia.eq_def (s := s ++ t) (pos := s.size + k)]
      rw [dif_pos hlt]
      rw [show (s ++ t)[s.size + k]'hlt = t[k]'h from arrGetElem_append_right' h]
      rw [if_pos hw]
      rw [skipTrivia.eq_def (s := t) (pos := k)]
      rw [dif_pos h, if_pos hw]
      rw [show skipTrivia (s ++ t) (s.size + k + 1)
          = skipTrivia (s ++ t) (s.size + (k + 1)) from by
        rw [show s.size + (k + 1) = s.size + k + 1 from by omega]]
      rw [ih]
  | case2 k h c hw hc ih =>
      have hlt : s.size + k < (s ++ t).size := by
        rw [Array.size_append]; omega
      rw [skipTrivia.eq_def (s := s ++ t) (pos := s.size + k)]
      rw [dif_pos hlt]
      rw [show (s ++ t)[s.size + k]'hlt = t[k]'h from arrGetElem_append_right' h]
      rw [if_neg hw, if_pos hc]
      rw [show skipToNewline (s ++ t) (s.size + k + 1)
          = s.size + skipToNewline t (k + 1) from by
        have := skipToNewline_append_right (s := s) (t := t) (k := k + 1)
        exact this]
      rw [skipTrivia.eq_def (s := t) (pos := k)]
      rw [dif_pos h, if_neg hw, if_pos hc]
      rw [show skipTrivia (s ++ t) (s.size + skipToNewline t (k + 1))
          = s.size + skipTrivia t (skipToNewline t (k + 1)) from by
        have h1 := ih
        rw [show skipToNewline t (k + 1) = skipToNewline t (k + 1) from rfl] at h1
        exact h1]
  | case3 k h c hw hc =>
      have hlt : s.size + k < (s ++ t).size := by
        rw [Array.size_append]; omega
      rw [skipTrivia.eq_def (s := s ++ t) (pos := s.size + k)]
      rw [dif_pos hlt]
      rw [show (s ++ t)[s.size + k]'hlt = t[k]'h from arrGetElem_append_right' h]
      rw [if_neg hw, if_neg hc]
      rw [skipTrivia.eq_def (s := t) (pos := k)]
      rw [dif_pos h, if_neg hw, if_neg hc]
  | case4 k h =>
      rw [skipTrivia.eq_def (s := s ++ t) (pos := s.size + k)]
      rw [dif_neg (by rw [Array.size_append]; omega)]
      rw [skipTrivia.eq_def (s := t) (pos := k)]
      rw [dif_neg h]


/-- The tokenizer walk past the join is the tail's walk, under the
    walk-level premise that (a) every scan from every position the
    walk visits stops inside `t` (`htw`), and (b) the tail's lexing
    never errors from `k` (`hnoerr` — needed because the lexer's
    error MESSAGES embed the absolute position, so error results
    genuinely differ between `s ++ t` and `t`). -/
theorem tokenizeAux_append_right_ok {s t : Array Char}
    (htw : ∀ (p : Char → Bool) (q : Nat),
      (takeWhile p t q "").2 < t.size)
    (hnoerr : ∀ (k : Nat) (h : k < t.size),
      (lexToken t k h).isOk = true)
    (hnostr : ∀ (k : Nat) (h : k < t.size), t[k]'h ≠ '"') :
    ∀ (k : Nat) (acc : Array Token),
      tokenizeAux (s ++ t) (s.size + k) acc
        = tokenizeAux t k acc := by
  intro k acc
  induction k, acc using tokenizeAux.induct (s := t) with
  | case1 k acc hsk hpos ih =>
      -- the trivia skip at the offset
      have hskip : skipTrivia (s ++ t) (s.size + k)
          = s.size + skipTrivia t k :=
        skipTrivia_append_right
      -- both sides unfold with aligned trivia skips
      rw [tokenizeAux.eq_def (s := s ++ t) (pos := s.size + k)]
      rw [tokenizeAux.eq_def (s := t) (pos := k)]
      -- the goal: two do-blocks with the shared structure. Both
      -- trivia skips are s.size + q vs q; both bounds agree; the
      -- token agrees by lexToken_append_right_ok (needs the
      -- success hypothesis). Split the ifs.
      -- rewrite the s++t side's trivia skip to the offset form
      simp only [] at *
      -- substitute the skip
      rw [hskip]
      -- both bounds: (s.size + skipTrivia t k < s.size + t.size) iff
      -- (skipTrivia t k < t.size)
      have hbound : s.size + hsk < (s ++ t).size := by
        rw [Array.size_append]
        omega
      rw [dif_pos hbound, dif_pos hpos]
      -- the token at the offset agrees (success-transport)
      have hsklt : hsk < t.size := hpos
      cases htok : lexToken t hsk hsklt with
      | ok tp =>
          obtain ⟨tok, p', hp'⟩ := tp
          have hoffset : lexToken (s ++ t) (s.size + hsk) hbound
              = .ok (tok, ⟨s.size + p', by omega⟩) :=
            lexToken_append_right_ok (s := s) (t := t) (k := hsk)
              hsklt (fun p q _ => htw p q) (hnostr hsk hsklt) htok
          rw [hoffset]
          -- hsk < p' from the token's structure: lexToken's tokens
          -- all end strictly after the start. Derive by casing the
          -- lexToken definition on the t side (htok).
          have hgtp : hsk < p' := by
            have hdef := htok
            rw [lexToken.eq_def (s := t) (pos := hsk) (h := hsklt)] at hdef
            simp only [] at hdef
            -- split the whole match/lexUnsigned structure at once:
            -- every branch puts the end position > hsk. Reduce by
            -- `split at hdef` repeatedly and use omega on the
            -- resulting position equations.
            repeat' (first | split at hdef | skip)
            all_goals
              first
              | (injection hdef with hpair; obtain ⟨_, hpos'⟩ :=
                  Prod.mk.inj hpair; injection hpos' with hv; omega)
              | omega
          exact ih tok p' hgtp
      | error e =>
          -- the error case is impossible: hnoerr says the t-side
          -- lexToken at any in-bounds position succeeds
          exfalso
          have hsome := hnoerr hsk hsklt
          rw [htok] at hsome
          exact Bool.noConfusion hsome
  | case2 k acc hsk hpos =>
      have hskip : skipTrivia (s ++ t) (s.size + k)
          = s.size + skipTrivia t k :=
        skipTrivia_append_right
      rw [tokenizeAux.eq_def (s := s ++ t) (pos := s.size + k)]
      rw [tokenizeAux.eq_def (s := t) (pos := k)]
      simp only [] at *
      rw [hskip]
      -- both sides' trivia runs are past the end: pure acc
      have hbound : ¬ (s.size + hsk < (s ++ t).size) := by
        rw [Array.size_append]
        omega
      rw [dif_neg hbound, dif_neg hpos]


/-- The stop char of a skip that stops inside the array is not
    whitespace (the skip only stops at a significant char). -/
theorem skipTrivia_stop_notws' {arr : Array Char} {k : Nat}
    (hlt : skipTrivia arr k < arr.size) :
    ¬ (isWhitespace (arr[skipTrivia arr k]!) = true) := by
  -- the stop's char class, by functional induction over the
  -- bang read (no dependent-transport issues)
  have key : ∀ (q : Nat) (hstop : skipTrivia arr q < arr.size),
      ¬ (isWhitespace (arr[skipTrivia arr q]!) = true) := by
    intro q
    induction q using skipTrivia.induct (s := arr) with
    | case1 q h c hw ih =>
        intro hstop
        have hstep : skipTrivia arr q = skipTrivia arr (q + 1) := by
          rw [skipTrivia.eq_def (s := arr) (pos := q)]
          rw [dif_pos h, if_pos hw]
        rw [hstep]
        exact ih (by rw [← hstep]; exact hstop)
    | case2 q h c hw hc ih =>
        intro hstop
        have hstep : skipTrivia arr q
            = skipTrivia arr (skipToNewline arr (q + 1)) := by
          rw [skipTrivia.eq_def (s := arr) (pos := q)]
          rw [dif_pos h, if_neg hw, if_pos hc]
        rw [hstep]
        exact ih (by rw [← hstep]; exact hstop)
    | case3 q h c hw hc =>
        intro hstop
        have hstop2 : skipTrivia arr q = q := by
          rw [skipTrivia.eq_def (s := arr) (pos := q)]
          rw [dif_pos h, if_neg hw, if_neg hc]
        -- the char read at the stop is c (the case's let), and
        -- c is not whitespace by hw
        intro hws
        rw [hstop2] at hws
        -- the case's let c is definitionally arr[q]'h; bridge
        -- via the prim-read:
        have hc2 : (arr[q]'h) = c := rfl
        rw [show (arr[q]!) = (arr[q]'h) from arrGetElem!_of_lt h] at hws
        rw [hc2] at hws
        exact hw hws
    | case4 q h =>
        intro hstop
        rw [skipTrivia.eq_def (s := arr) (pos := q)] at hstop
        rw [dif_neg h] at hstop
        exact absurd hstop (by omega)
  exact key k hlt

theorem takeWhile_stop_acc (p : Char → Bool) (s : Array Char) :
    ∀ (q : Nat) (acc1 : String), ∀ (acc2 : String),
      (takeWhile p s q acc1).2 = (takeWhile p s q acc2).2 := by
  intro q acc1
  induction q, acc1 using takeWhile.induct (p := p) (s := s) with
  | case1 q acc h c hp ih =>
      intro acc2
      rw [takeWhile.eq_def (acc := acc), takeWhile.eq_def (acc := acc2)]
      rw [dif_pos h, dif_pos h]
      rw [if_pos hp, if_pos hp]
      exact ih (String.push acc2 c)
  | case2 q acc h c hp =>
      intro acc2
      rw [takeWhile.eq_def (acc := acc), takeWhile.eq_def (acc := acc2)]
      rw [dif_pos h, dif_pos h]
      rw [if_neg hp, if_neg hp]
  | case3 q acc h =>
      intro acc2
      rw [takeWhile.eq_def (acc := acc), takeWhile.eq_def (acc := acc2)]
      rw [dif_neg h, dif_neg h]

/-- Variant of `lexToken_append_left` where the two-character
    lookahead room premise (`pos + 2 < s.size`) is replaced by:
    whenever the lookahead index is past `s`, the joined array's
    character there is neither `:` nor `.` (so the two-char tokens
    cannot fire on the joined side; the newline separator and any
    token-start satisfy this). -/
theorem lexToken_append_left' {s t : Array Char} {pos : Nat}
    (hpos : pos < s.size)
    (hlook : ∀ (_hn : s.size ≤ pos + 1) (_h2 : pos + 1 < s.size + t.size),
      (s ++ t)[pos + 1]'(by rw [Array.size_append]; omega) ≠ ':'
      ∧ (s ++ t)[pos + 1]'(by rw [Array.size_append]; omega) ≠ '.')
    (hnostr : ∀ (q : Nat), pos ≤ q → q < s.size → s[q]! ≠ '"')
    (htw : ∀ (p : Char → Bool) (q : Nat) (acc : String), pos ≤ q →
      (takeWhile p s q acc).2 < s.size) :
    lexToken (s ++ t) pos (by rw [Array.size_append]; omega)
      = lexToken s pos hpos := by
  have hlt : pos < (s ++ t).size := by rw [Array.size_append]; omega
  have heq : (s ++ t)[pos]'hlt = s[pos]'hpos := arrGetElem_append_left hpos
  rw [lexToken, lexToken]
  simp only [heq]
  all_goals simp_all
  all_goals (try split)
  all_goals (try simp_all)
  all_goals (try omega)
  all_goals (try rfl)
  -- the ':' branch: the lookahead conditions agree
  case h_10 =>
    rename_i _ heqc
    by_cases hroom : pos + 1 < s.size
    · have heq1 : (s ++ t)[pos + 1]! = s[pos + 1]! :=
        arrGetElem!_append_left (t := t) hroom
      by_cases hc : pos + 1 < s.size ∧ s[pos + 1]! = ':'
      · rw [if_pos (by
            refine ⟨by omega, ?_⟩
            rw [heq1]
            exact hc.2), if_pos hc]
      · rw [if_neg (by
            intro h2
            rw [heq1] at h2
            apply hc
            exact ⟨by omega, h2.2⟩), if_neg hc]
    · -- past s: the joined char at pos+1 is not ':' (hlook), so
      -- both sides' conditions are false
      have hsfalse : ¬ (pos + 1 < s.size ∧ s[pos + 1]! = ':') :=
        fun h => hroom h.1
      rw [if_neg hsfalse]
      rw [if_neg (by
        intro hc2
        obtain ⟨hbound2, hcolon⟩ := hc2
        obtain ⟨hnc, _⟩ := hlook (by omega) hbound2
        -- the goal's char (reduced to the t-read) equals the
        -- joined read at pos+1: convert hnc's form
        apply hnc
        -- hcolon : (s++t)[pos+1]! = ':' — the goal wants the
        -- t-read form; convert the joined bang-read to the t-read
        have hread : (s ++ t)[s.size + (pos + 1 - s.size)]!
            = t[pos + 1 - s.size]! :=
          arrGetElem!_append_right' (s := s) (t := t) (k := pos + 1 - s.size)
            (by omega : pos + 1 - s.size < t.size)
        rw [show s.size + (pos + 1 - s.size) = pos + 1 from by omega] at hread
        rw [hread] at hcolon
        have hlt2 : pos + 1 - s.size < t.size := by omega
        rw [arrGetElem!_of_lt (a := t) (i := pos + 1 - s.size) hlt2] at hcolon
        exact hcolon)]

  case h_11 =>
    rename_i _ heqc
    by_cases hroom : pos + 1 < s.size
    · have heq1 : (s ++ t)[pos + 1]! = s[pos + 1]! :=
        arrGetElem!_append_left (t := t) hroom
      by_cases hc : pos + 1 < s.size ∧ s[pos + 1]! = '.'
      · rw [if_pos (by
            refine ⟨by omega, ?_⟩
            rw [heq1]
            exact hc.2), if_pos hc]
      · rw [if_neg (by
            intro h2
            rw [heq1] at h2
            apply hc
            exact ⟨by omega, h2.2⟩), if_neg hc]
    · have hsfalse : ¬ (pos + 1 < s.size ∧ s[pos + 1]! = '.') :=
        fun h => hroom h.1
      rw [if_neg hsfalse]
      rw [if_neg (by
        intro hc2
        obtain ⟨hbound2, hdot⟩ := hc2
        obtain ⟨_, hnd⟩ := hlook (by omega) hbound2
        apply hnd
        have hread : (s ++ t)[s.size + (pos + 1 - s.size)]!
            = t[pos + 1 - s.size]! :=
          arrGetElem!_append_right' (s := s) (t := t) (k := pos + 1 - s.size)
            (by omega : pos + 1 - s.size < t.size)
        rw [show s.size + (pos + 1 - s.size) = pos + 1 from by omega] at hread
        rw [hread] at hdot
        have hlt2 : pos + 1 - s.size < t.size := by omega
        rw [arrGetElem!_of_lt (a := t) (i := pos + 1 - s.size) hlt2] at hdot
        exact hdot)]

  case h_13 =>
    -- the conditions on both sides are already aligned (s-form);
    -- rewrite the scan first (it appears in both sides' matches)
    have hscan : takeWhile isIdentChar (s ++ t) (pos + 1)
        (String.singleton s[pos])
        = takeWhile isIdentChar s (pos + 1) (String.singleton s[pos]) :=
      takeWhile_append_left (htw isIdentChar (pos + 1) _ (by omega))
    simp only [hscan]
    by_cases halpha : isAlpha s[pos] = true ∨ s[pos] = '_'
    · rw [if_pos halpha, if_pos halpha]
    · rw [if_neg halpha, if_neg halpha]
      by_cases hdigit : isDigit s[pos] = true ∨ s[pos] = '-'
      · rw [if_pos hdigit, if_pos hdigit]
        have hilex : lexInt (s ++ t) pos = lexInt s pos :=
          lexInt_append_left (fun p q hq => htw p q "" hq)
        split
        · rename_i tL pL hiL
          have hR : lexInt s pos = .ok (tL, pL) := by
            rw [← hilex]; exact hiL
          split
          · rename_i tR pR hiR
            rw [hR] at hiR
            injection hiR with htp
            cases htp
            rfl
          · rename_i eR hiR
            rw [hR] at hiR
            exact absurd hiR (by simp)
        · rename_i eL hiL
          have hR : lexInt s pos = .error eL := by
            rw [← hilex]; exact hiL
          split
          · rename_i tR pR hiR
            rw [hR] at hiR
            exact absurd hiR (by simp)
          · rename_i eR hiR
            rw [hR] at hiR
            injection hiR with hee
            subst hee
            rfl
      · rw [if_neg hdigit, if_neg hdigit]

theorem takeWhile_stop_le' (p : Char → Bool) (arr : Array Char) :
    ∀ (q : Nat) (acc : String), q ≤ arr.size →
      (takeWhile p arr q acc).2 ≤ arr.size := by
  intro q acc
  induction q, acc using takeWhile.induct (p := p) (s := arr) with
  | case1 q acc h c hp ih =>
      intro hqle
      rw [takeWhile.eq_def (s := arr) (pos := q) (acc := acc)]
      rw [dif_pos h, if_pos hp]
      exact ih (by omega)
  | case2 q acc h c hp =>
      intro _
      rw [takeWhile.eq_def (s := arr) (pos := q) (acc := acc)]
      rw [dif_pos h, if_neg hp]
      show (acc, q).snd ≤ arr.size
      simp only []
      omega
  | case3 q acc h =>
      intro hqle
      rw [takeWhile.eq_def (s := arr) (pos := q) (acc := acc)]
      rw [dif_neg h]
      show (acc, q).snd ≤ arr.size
      simp only []
      exact hqle

theorem lexString_le (arr : Array Char) :
    ∀ (pos : Nat) (acc : String), pos ≤ arr.size →
    ∀ (w : String) (p : Nat), lexString arr pos acc = .ok (w, p) →
      p ≤ arr.size := by
  intro pos acc
  induction pos, acc using lexString.induct (s := arr) with
  | case1 pos acc h c hq =>
    intro hle w p hr
    rw [lexString.eq_def] at hr
    simp only [h, dif_pos] at hr
    change (if (c == '"') = true then Except.ok (acc, pos + 1)
      else _) = Except.ok (w, p) at hr
    rw [if_pos hq] at hr
    simp only [Except.ok.injEq, Prod.mk.injEq] at hr
    obtain ⟨_, rfl⟩ := hr
    omega
  | case2 pos acc h _c hnq hbs hroom _e _d ih1 =>
    intro hle w p hr
    rw [lexString.eq_def] at hr
    simp only [h, dif_pos] at hr
    have hc : _c = arr[pos] := rfl
    rw [hc] at hnq hbs
    rw [if_neg hnq, if_pos hbs, if_pos hroom] at hr
    exact ih1 (by omega) w p hr
  | case3 pos acc h _c hnq hbs hnoroom =>
    intro hle w p hr
    rw [lexString.eq_def] at hr
    simp only [h, dif_pos] at hr
    have hc : _c = arr[pos] := rfl
    rw [hc] at hnq hbs
    rw [if_neg hnq, if_pos hbs, if_neg hnoroom] at hr
    contradiction
  | case4 pos acc h c hq hbs hn =>
    intro hle w p hr
    rw [lexString.eq_def] at hr
    simp only [h, dif_pos] at hr
    change (if (c == '"') = true then Except.ok (acc, pos + 1)
      else if (c == '\\') = true then _
      else if (c == '\n') = true then _
      else _) = Except.ok (w, p) at hr
    rw [if_neg hq, if_neg hbs, if_pos hn] at hr
    contradiction
  | case5 pos acc h c hq hbs hn ih =>
    intro hle w p hr
    rw [lexString.eq_def] at hr
    simp only [h, dif_pos] at hr
    change (if (c == '"') = true then Except.ok (acc, pos + 1)
      else if (c == '\\') = true then _
      else if (c == '\n') = true then _
      else _) = Except.ok (w, p) at hr
    rw [if_neg hq, if_neg hbs, if_neg hn] at hr
    exact ih (by omega) w p hr
  | case6 pos acc h =>
    intro hle w p hr
    rw [lexString.eq_def] at hr
    simp only [dif_neg h] at hr
    contradiction

theorem lexUnsigned_le (arr : Array Char) (pos : Nat) (hle : pos ≤ arr.size)
    (n : Int) (p : Nat) (hok : lexUnsigned arr pos = .ok (n, p)) :
    p ≤ arr.size := by
  rw [lexUnsigned.eq_def (s := arr) (pos := pos)] at hok
  split at hok
  · rename_i hcondx
    -- hex: the prefix gives pos+1 < size
    have hroom : pos + 1 < arr.size := by
      have h1 : (decide (pos + 1 < arr.size)) = true := by
        cases hlt : decide (pos + 1 < arr.size) with
        | true => rfl
        | false =>
            rw [hlt] at hcondx
            simp at hcondx
      exact of_decide_eq_true h1
    split at hok
    · exact absurd hok (by simp)
    · rename_i hdig
      injection hok with hpair
      obtain ⟨_, hpos'⟩ := Prod.mk.inj hpair
      have := takeWhile_stop_le' isHexDigit arr (pos + 2) "" (by omega)
      omega
  · rename_i hno
    split at hok
    · rename_i hcondo
      -- oct
      have hroom : pos + 1 < arr.size := by
        have h1 : (decide (pos + 1 < arr.size)) = true := by
          cases hlt : decide (pos + 1 < arr.size) with
          | true => rfl
          | false =>
              rw [hlt] at hcondo
              simp at hcondo
        exact of_decide_eq_true h1
      split at hok
      · exact absurd hok (by simp)
      · rename_i hdig
        injection hok with hpair
        obtain ⟨_, hpos'⟩ := Prod.mk.inj hpair
        have := takeWhile_stop_le' isOctDigit arr (pos + 2) "" (by omega)
        omega
    · -- decimal
      rename_i hno2
      split at hok
      · exact absurd hok (by simp)
      · rename_i hdig
        injection hok with hpair
        obtain ⟨_, hpos'⟩ := Prod.mk.inj hpair
        have := takeWhile_stop_le' isDigit arr pos "" hle
        omega

theorem lexInt_le (arr : Array Char) (pos : Nat) (hle : pos ≤ arr.size)
    (tok : Token) (p : Nat) (hok : lexInt arr pos = .ok (tok, p)) :
    p ≤ arr.size := by
  rw [lexInt.eq_def (s := arr) (pos := pos)] at hok
  by_cases hminus : (decide (pos < arr.size) && arr[pos]! == '-') = true
  · rw [if_pos hminus] at hok
    split at hok
    · rename_i n pe hu
      have hcond := Bool.and_eq_true_iff.mp hminus
      have hroom : pos < arr.size := of_decide_eq_true hcond.1
      injection hok with hpair
      obtain ⟨_, hpos'⟩ := Prod.mk.inj hpair
      have := lexUnsigned_le arr (pos + 1) (by omega) n pe hu
      omega
    · exact absurd hok (by simp)
  · rw [if_neg hminus] at hok
    split at hok
    · rename_i n pe hu
      injection hok with hpair
      obtain ⟨_, hpos'⟩ := Prod.mk.inj hpair
      have := lexUnsigned_le arr pos hle n pe hu
      omega
    · exact absurd hok (by simp)

theorem skipTrivia_ws_agree' (arr : Array Char)
    (k k' : Nat) (hkk : k ≤ k') (hk'le : k' ≤ arr.size)
    (hws : ∀ (m : Nat), k ≤ m → m < k' →
      (hm : m < arr.size) → isWhitespace ((arr[m]'hm)) = true)
    (_hnopct : ∀ (q : Nat) (hq : q < arr.size), k ≤ q → q < k' →
      ((arr[q]'hq)) ≠ '%') :
    skipTrivia arr k = skipTrivia arr k' := by
  have key : ∀ (j : Nat), k ≤ j → j < k' →
      skipTrivia arr j = skipTrivia arr (j + 1) := by
    intro j hjle hjlt
    have hjsize : j < arr.size := by omega
    rw [skipTrivia.eq_def (s := arr) (pos := j)]
    rw [dif_pos hjsize]
    have hwsj : isWhitespace ((arr[j]'hjsize)) = true := hws j hjle hjlt hjsize
    rw [if_pos hwsj]
  have chain : ∀ (d : Nat), d ≤ k' - k →
      skipTrivia arr k = skipTrivia arr (k + d) := by
    intro d
    induction d with
    | zero => intro _; rfl
    | succ d' ih =>
        intro hdle
        rw [ih (by omega)]
        have h1 : skipTrivia arr (k + d') = skipTrivia arr (k + d' + 1) := by
          apply key (k + d')
          · omega
          · omega
        rw [h1, Nat.add_assoc]
  have hd : k + (k' - k) = k' := by omega
  rw [chain (k' - k) (Nat.le_refl _), hd]


theorem skipTrivia_path (arr : Array Char)
    (hnopct : ∀ (q : Nat) (h : q < arr.size), (arr[q]'h) ≠ '%') :
    ∀ (k m : Nat), k ≤ m → m < skipTrivia arr k → ∀ (hms : m < arr.size),
      isWhitespace (arr[m]'hms) = true := by
  intro k
  induction k using skipTrivia.induct (s := arr) with
  | case1 k h c hw ih =>
      intro m hkm hmlt hmsize
      by_cases hmeq : m = k
      · have h1 : ((arr[m]'hmsize)) = arr[m]! :=
          (arrGetElem!_of_lt hmsize).symm
        have h2 : ((arr[k]'h)) = arr[k]! :=
          (arrGetElem!_of_lt h).symm
        rw [h1, show arr[m]! = arr[k]! from by rw [hmeq], ← h2]
        exact hw
      · have hstep : skipTrivia arr k = skipTrivia arr (k + 1) := by
          rw [skipTrivia.eq_def (s := arr) (pos := k)]
          rw [dif_pos h, if_pos hw]
        rw [hstep] at hmlt
        exact ih m (by omega) hmlt hmsize
  | case2 k h c hw hc ih =>
      exfalso
      apply hnopct k h
      have hcc : c = '%' := eq_of_beq hc
      rw [show (arr[k]'h) = c from rfl, hcc]
  | case3 k h c hw hc =>
      intro m hkm hmlt hmsize
      have hstop : skipTrivia arr k = k := by
        rw [skipTrivia.eq_def (s := arr) (pos := k)]
        rw [dif_pos h, if_neg hw, if_neg hc]
      rw [hstop] at hmlt
      omega
  | case4 k h =>
      intro m hkm hmlt hmsize
      have hstop : skipTrivia arr k = k := by
        rw [skipTrivia.eq_def (s := arr) (pos := k)]
        rw [dif_neg h]
      rw [hstop] at hmlt
      omega

theorem skip_exit_join {s u : Array Char}
    (hnopct : ∀ (q : Nat) (h : q < s.size), s[q]'h ≠ '%')
    (husize : 0 < u.size)
    (huhead : (s ++ u)[s.size]'(by
      rw [Array.size_append]
      omega) = '\n')
    (hle : p ≤ s.size)
    (hexit : s.size ≤ skipTrivia s p) :
    skipTrivia (s ++ u) p = skipTrivia (s ++ u) s.size := by
  -- the joined skip from p agrees with the s-skip up to the
  -- boundary (skipTrivia_append_left needs the stop inside —
  -- NOT available). Instead: BOTH joined skips stop at the
  -- first significant position past the separator. Since
  -- [p, s.size) is whitespace in s (the s-skip's path), those
  -- chars are also whitespace in the joined array (reads
  -- agree), and the separator is whitespace — so by
  -- skipTrivia_ws_agree on the joined array over [p, s.size+1)
  -- ... s.size+1 > the run's end. The run [p, s.size] all
  -- whitespace in the joined: skip (s++u) p = skip (s++u)
  -- (s.size + 1)? NO — the ws_agree gives skip p = skip (j) for
  -- j = the run end. The run is [p, s.size] (inclusive of the
  -- separator); so skip (s++u) p = skip (s++u) (s.size + 1).
  -- But we want = skip (s++u) s.size — NOT equal in general
  -- (the separator at s.size is whitespace so the skip from
  -- s.size ALSO skips it: skip (s++u) s.size = skip (s++u)
  -- (s.size + 1) — by ws_agree on [s.size, s.size+1)! So both
  -- equal skip (s++u) (s.size + 1). Chain:
  have hwsp : ∀ (m : Nat), p ≤ m → m < s.size →
      (hm : m < (s ++ u).size) → isWhitespace ((s ++ u)[m]'hm) = true := by
    intro m hmle hmlt hmsize
    -- the char is s's char (in-bounds read agreement) and it
    -- is whitespace by the s-skip's path:
    have hmsread : (s ++ u)[m]'hmsize = s[m]'(by omega) :=
      arrGetElem_append_left (by omega : m < s.size)
    rw [hmsread]
    exact skipTrivia_path s hnopct p m hmle (by omega) (by omega)
  have hwssep : ∀ (m : Nat), s.size ≤ m → m < s.size + 1 →
      (hm : m < (s ++ u).size) → isWhitespace ((s ++ u)[m]'hm) = true := by
    intro m hmle hmge hm
    have hmss : m = s.size := by omega
    -- the dependent-read transport (m = s.size):
    have h1 : ((s ++ u)[m]'hm) = (s ++ u)[m]! :=
      (arrGetElem!_of_lt hm).symm
    rw [h1, hmss]
    have h2 : (s ++ u)[s.size]! = ((s ++ u)[s.size]'(by
      rw [Array.size_append]; omega)) := arrGetElem!_of_lt (by
      rw [Array.size_append]; omega)
    rw [h2, huhead]
    rfl
  -- the joined run [p, s.size+1) is all whitespace:
  have hwsall : ∀ (m : Nat), p ≤ m → m < s.size + 1 →
      (hm : m < (s ++ u).size) → isWhitespace ((s ++ u)[m]'hm) = true := by
    intro m hmle hmge hmsize
    by_cases hmlt : m < s.size
    · exact hwsp m hmle hmlt hmsize
    · exact hwssep m (by omega) hmge hmsize
  -- both skips equal the skip from s.size + 1:
  have hsizebound : s.size + 1 <= (s ++ u).size := by
    have hu1 : 1 <= u.size := husize
    have hsz : (s ++ u).size = s.size + u.size := by
      rw [Array.size_append]
    omega
  have hsizebound2 : p <= s.size + 1 := by omega
  -- the joined-run no-% premise: any in-bounds % char on the
  -- both skips equal the skip from s.size + 1:
  have hsizebound : s.size + 1 ≤ (s ++ u).size := by
    have hu1 : 1 ≤ u.size := husize
    have hsz : (s ++ u).size = s.size + u.size := by
      rw [Array.size_append]
    omega
  have hsizebound2 : p ≤ s.size + 1 := by omega
  -- the run premise for ws_agree: within [p, s.size+1) the
  -- joined array is whitespace (hwsall), hence not '%':
  have hrunnopct : ∀ (q : Nat) (hq : q < (s ++ u).size),
      p ≤ q → q < s.size + 1 → ((s ++ u)[q]'hq) ≠ '%' := by
    intro q hq hq1 hq2
    have hwsq := hwsall q hq1 hq2 hq
    intro hpct
    rw [hpct] at hwsq
    exact absurd hwsq (by
      intro hc
      exact absurd (eq_of_beq hc).symm (by decide))
  -- ws_agree (with the run-restricted premise):
  rw [skipTrivia_ws_agree' (s ++ u)
    p (s.size + 1) hsizebound2 hsizebound hwsall hrunnopct]
  rw [skipTrivia_ws_agree' (s ++ u)
    s.size (s.size + 1) (Nat.le_succ s.size) hsizebound
    (fun m hm1 hm2 hmsize => hwsall m (by omega) (by omega) hmsize)
    (fun q hq hq1 hq2 => hrunnopct q hq (by omega) hq2)]

theorem lexToken_le {arr : Array Char} {pos : Nat} (h : pos < arr.size)
    {tok : Token} {p : Nat} (hp : pos < p)
    (hok : lexToken arr pos h = .ok (tok, ⟨p, hp⟩)) :
    p ≤ arr.size := by
  rw [lexToken.eq_def] at hok
  simp only [] at hok
  -- the ':' arm (h_10):
  split at hok
  case h_10 heq =>
    by_cases hcond : (decide (pos + 1 < arr.size) && arr[pos + 1]! == ':') = true
    · rw [if_pos hcond] at hok
      injection hok with hpair
      obtain ⟨_, hpos'⟩ := Prod.mk.inj hpair
      injection hpos' with hv
      -- pos+1 < size gives pos+2 ≤ size:
      have hroom : pos + 1 < arr.size :=
        of_decide_eq_true (Bool.and_eq_true_iff.mp hcond).1
      omega
    · rw [if_neg hcond] at hok
      injection hok with hpair
      obtain ⟨_, hpos'⟩ := Prod.mk.inj hpair
      injection hpos' with hv
      omega
  case h_11 heq =>
    by_cases hcond : (decide (pos + 1 < arr.size) && arr[pos + 1]! == '.') = true
    · rw [if_pos hcond] at hok
      injection hok with hpair
      obtain ⟨_, hpos'⟩ := Prod.mk.inj hpair
      injection hpos' with hv
      have hroom : pos + 1 < arr.size :=
        of_decide_eq_true (Bool.and_eq_true_iff.mp hcond).1
      omega
    · rw [if_neg hcond] at hok
      exact absurd hok (by simp)
  case h_12 heq =>
    -- the string arm: the end is lexString's ok end
    split at hok
    · rename_i str pe hs
      have hsub : pe ≤ arr.size :=
        lexString_le arr (pos + 1) "" (by omega) str pe hs
      -- hok : ok (stringLit str, ⟨pe, _⟩) = ok (tok, ⟨p, hp⟩)
      injection hok with hpair
      obtain ⟨_, hpos'⟩ := Prod.mk.inj hpair
      injection hpos' with hv
      omega
    · exact absurd hok (by simp)
  all_goals
    first
    | (injection hok with hpair; obtain ⟨_, hpos'⟩ := Prod.mk.inj hpair;
        injection hpos' with hv; omega)
    | skip
  case h_13 heq =>
    -- the catch-all arm: ident or int
    by_cases halpha : (isAlpha arr[pos] || arr[pos] == '_') = true
    · rw [if_pos halpha] at hok
      -- the keywordToken match + reserved check:
      split at hok
      · rename_i t hr
        injection hok with hpair
        obtain ⟨_, hpos'⟩ := Prod.mk.inj hpair
        injection hpos' with hv
        have := takeWhile_stop_le' isIdentChar arr (pos + 1)
          (String.singleton arr[pos]) (by omega)
        omega
      · rename_i hr
        split at hok
        · exact absurd hok (by simp)
        · rename_i hr2
          injection hok with hpair
          obtain ⟨_, hpos'⟩ := Prod.mk.inj hpair
          injection hpos' with hv
          have := takeWhile_stop_le' isIdentChar arr (pos + 1)
            (String.singleton arr[pos]) (by omega)
          omega
    · rw [if_neg halpha] at hok
      by_cases hdigit : (isDigit arr[pos] || arr[pos] == '-') = true
      · rw [if_pos hdigit] at hok
        split at hok
        · rename_i t pe hi
          have hle : pos ≤ arr.size := Nat.le_of_lt h
          have := lexInt_le arr pos hle t pe hi
          injection hok with hpair
          obtain ⟨_, hpos'⟩ := Prod.mk.inj hpair
          injection hpos' with hv
          omega
        · exact absurd hok (by simp)
      · rw [if_neg hdigit] at hok
        exact absurd hok (by simp)

theorem tokenizeAux_exit_tail {s u : Array Char} (acc : Array Token)
    (hnopct : ∀ (q : Nat) (h : q < s.size), (s[q]'h) ≠ '%')
    (husize : 0 < u.size)
    (huhead : (s ++ u)[s.size]'(by
      rw [Array.size_append]
      omega) = '\n')
    (hle : p ≤ s.size)
    (hexit : s.size ≤ skipTrivia s p) :
    tokenizeAux (s ++ u) p acc = tokenizeAux (s ++ u) s.size acc := by
  -- the joined skips agree (skip_exit_join); the walks from
  -- agreeing-skip positions agree:
  have hskip : skipTrivia (s ++ u) p = skipTrivia (s ++ u) s.size :=
    skip_exit_join hnopct husize huhead hle hexit
  -- the walks: unfold both; the LHS's skip is hskip; the RHS's
  -- is the same; both walks identical after the alignment:
  rw [tokenizeAux.eq_def (s := s ++ u) (pos := p),
    tokenizeAux.eq_def (s := s ++ u) (pos := s.size)]
  simp only []
  conv =>
    lhs
    rw [hskip]

theorem tokenizeAux_skip_eq (arr : Array Char) :
    ∀ (k k' : Nat) (acc : Array Token),
      skipTrivia arr k = skipTrivia arr k' →
      tokenizeAux arr k acc = tokenizeAux arr k' acc := by
  intro k k' acc hskip
  rw [tokenizeAux.eq_def (s := arr) (pos := k)]
  rw [tokenizeAux.eq_def (s := arr) (pos := k')]
  simp only []
  conv =>
    lhs
    rw [hskip]

theorem split_helper {s u : Array Char}
    (husize : 0 < u.size)
    (huhead : (s ++ u)[s.size]'(by
      rw [Array.size_append]
      omega) = '\n')
    (hnopct : ∀ (q : Nat) (h : q < s.size), s[q]'h ≠ '%')
    (hunif : ∀ (k : Nat) (_h : k < s.size) (_h2 : s.size ≤ k + 1)
        (h3 : k + 1 < (s ++ u).size),
      (s ++ u)[k + 1]'h3 ≠ ':' ∧ (s ++ u)[k + 1]'h3 ≠ '.')
    (htw : ∀ (p : Char → Bool) (q : Nat) (acc : String),
      (takeWhile p s q acc).2 < s.size)
    (hnoerr : ∀ (k : Nat) (h : k < s.size),
      (lexToken s k h).isOk = true)
    (hnostr : ∀ (k : Nat) (h : k < s.size), s[k]'h ≠ '"') :
    ∀ (k : Nat) (acc : Array Token), skipTrivia s k < s.size →
      tokenizeAux (s ++ u) k acc
        = (tokenizeAux s k acc).bind (fun acc' =>
            tokenizeAux (s ++ u) s.size acc') := by
  intro k acc
  induction k, acc using tokenizeAux.induct (s := s) with
  | case1 k acc hsk hpos ih =>
      intro _
      have hskip : skipTrivia (s ++ u) k = skipTrivia s k :=
        skipTrivia_append_left (fun q _ hq => hnopct q hq) hpos
      rw [tokenizeAux.eq_def (s := s ++ u) (pos := k)]
      rw [tokenizeAux.eq_def (s := s) (pos := k)]
      simp only [] at *
      rw [hskip]
      have hbound : hsk < (s ++ u).size := by
        rw [Array.size_append]; omega
      rw [dif_pos hbound, dif_pos hpos]
      -- the token agreement:
      have htok2 : lexToken (s ++ u) hsk hbound = lexToken s hsk hpos := by
        apply lexToken_append_left' hpos
        · intro hn h2
          have h3 : hsk + 1 < (s ++ u).size := by
            rw [Array.size_append]
            exact h2
          exact hunif hsk hpos hn h3
        · intro q hq hq2
          rw [arrGetElem!_of_lt hq2]
          exact hnostr q hq2
        · intro p q acc hq
          rw [takeWhile_stop_acc p s q acc ""]
          exact htw p q ""
      rw [htok2]
      cases ht : lexToken s hsk hpos with
      | ok tp =>
          obtain ⟨tok, p', hp'⟩ := tp
          -- the token end stays in bounds:
          have hple : p' ≤ s.size := lexToken_le hpos (by omega) ht
          by_cases hexit : skipTrivia s p' < s.size
          · -- the walk continues in s: the IH at p'
            exact ih tok p' hp' hexit
          · -- the s-walk EXITS at p': the s-side returns
            -- acc.push tok; the joined side from p' must equal
            -- the joined walk from s.size with acc.push tok.
            -- reduce the s-side walk (the exit):
            have hex : tokenizeAux s p' (acc.push tok)
                = Except.ok (acc.push tok) := by
              rw [tokenizeAux.eq_def (s := s) (pos := p')
                (acc := acc.push tok)]
              rw [dif_neg (by omega : ¬ skipTrivia s p' < s.size)]
              rfl
            -- the joined walk from p' (whitespace tail + the
            -- separator) equals the joined walk from s.size:
            have htail : tokenizeAux (s ++ u) p' (acc.push tok)
                = tokenizeAux (s ++ u) s.size (acc.push tok) :=
              tokenizeAux_exit_tail (acc.push tok) hnopct
                husize
                huhead
                hple (by omega)
            -- assemble: the joined walk = the tail walk; the
            -- s-side exited:
            calc tokenizeAux (s ++ u) p' (acc.push tok)
                = tokenizeAux (s ++ u) s.size (acc.push tok) := htail
              _ = (Except.ok (acc.push tok)).bind
                  (fun acc' => tokenizeAux (s ++ u) s.size acc') := by rfl
              _ = (tokenizeAux s p' (acc.push tok)).bind
                  (fun acc' => tokenizeAux (s ++ u) s.size acc') := by
                  rw [hex]
      | error e =>
          exfalso
          have hthis := hnoerr hsk hpos
          rw [ht] at hthis
          exact Bool.noConfusion hthis
  | case2 k acc hsk hpos =>
      intro hstop
      exact absurd hstop hpos

/-- The skip is a fixpoint: skipping from the stop gives the
    same stop (the stop is significant or past the end). -/
theorem skipTrivia_fixpoint (arr : Array Char) (k : Nat) :
    skipTrivia arr (skipTrivia arr k) = skipTrivia arr k := by
  have key : ∀ (q : Nat), skipTrivia arr (skipTrivia arr q) = skipTrivia arr q := by
    intro q
    induction q using skipTrivia.induct (s := arr) with
    | case1 q h c hw ih =>
        -- the skip steps to q+1 (whitespace); IH at q+1
        have hstep : skipTrivia arr q = skipTrivia arr (q + 1) := by
          rw [skipTrivia.eq_def (s := arr) (pos := q)]
          rw [dif_pos h, if_pos hw]
        rw [hstep]
        exact ih
    | case2 q h c hw hc ih =>
        -- the % branch: hnopct excludes it in our uses, but the
        -- fixpoint holds generally: the skip jumps to the
        -- post-comment position J; the skip from J = J iff J is
        -- significant or past end. Since skip arr q = skip arr J
        -- by the step, IH at J:
        have hstep : skipTrivia arr q
            = skipTrivia arr (skipToNewline arr (q + 1)) := by
          rw [skipTrivia.eq_def (s := arr) (pos := q)]
          rw [dif_pos h, if_neg hw, if_pos hc]
        rw [hstep]
        exact ih
    | case3 q h c hw hc =>
        -- the stop is q itself (significant char); skipping from
        -- q: q is significant → stops at q again
        have hstop : skipTrivia arr q = q := by
          rw [skipTrivia.eq_def (s := arr) (pos := q)]
          rw [dif_pos h, if_neg hw, if_neg hc]
        rw [hstop]
        rw [skipTrivia.eq_def (s := arr) (pos := q)]
        rw [dif_pos h, if_neg hw, if_neg hc]
    | case4 q h =>
        -- past the end: the skip is q; skipping from q (≥ size)
        -- returns q
        have hstop : skipTrivia arr q = q := by
          rw [skipTrivia.eq_def (s := arr) (pos := q)]
          rw [dif_neg h]
        rw [hstop]
        rw [skipTrivia.eq_def (s := arr) (pos := q)]
        rw [dif_neg h]
  exact key k

theorem nl_head (t : Array Char) :
    (#[('\n' : Char)] ++ t)[0]! = '\n' := by
  have hlt : 0 < (#[('\n' : Char)] ++ t).size := by
    rw [Array.size_append, show (#[('\n' : Char)]).size = 1 by decide]
    omega
  rw [arrGetElem!_of_lt hlt]
  rw [Array.getElem_append_left (show 0 < (#[('\n' : Char)]).size by decide)]
  rfl

/-- **The lexer cons law** (full premise form). -/

theorem tokenizeAux_acc_append (arr : Array Char) :
    ∀ (n : Nat) (k : Nat), arr.size - k ≤ n →
    ∀ (pre acc : Array Token),
      tokenizeAux arr k (pre ++ acc)
        = (tokenizeAux arr k acc).map (fun r => pre ++ r) := by
  intro n
  induction n with
  | zero =>
      -- arr.size - k = 0: k ≥ size; the walk exits immediately
      intro k hk pre acc
      rw [tokenizeAux.eq_def (s := arr) (pos := k) (acc := pre ++ acc)]
      rw [tokenizeAux.eq_def (s := arr) (pos := k) (acc := acc)]
      simp only []
      have hkge : arr.size ≤ k := by omega
      have hskipge : arr.size ≤ skipTrivia arr k :=
        Nat.le_trans hkge (skipTrivia_ge arr k)
      rw [dif_neg (Nat.not_lt.mpr hskipge),
        dif_neg (Nat.not_lt.mpr hskipge)]
      -- map (pre ++) (pure acc) = pure (pre ++ acc):
      rfl
  | succ n' ih =>
      intro k hk pre acc
      by_cases hlt : skipTrivia arr k < arr.size
      · rw [tokenizeAux.eq_def (s := arr) (pos := k) (acc := pre ++ acc)]
        rw [tokenizeAux.eq_def (s := arr) (pos := k) (acc := acc)]
        simp only []
        rw [dif_pos hlt, dif_pos hlt]
        cases ht : lexToken arr (skipTrivia arr k) hlt with
        | ok tp =>
            obtain ⟨tok, p', hp'⟩ := tp
            have hgoal : tokenizeAux arr p' ((pre ++ acc).push tok)
                = (tokenizeAux arr p' (acc.push tok)).map
                    (fun r => pre ++ r) := by
              rw [show ((pre ++ acc).push tok) = pre ++ (acc.push tok) from by
                rw [Array.push_append]]
              -- the measure decreases: arr.size - p' = n' (since
              -- skip < p' ≤ size... p' could be = size: then the
              -- measure is 0 ≤ n'):
              have hmeas : arr.size - p' ≤ n' := by
                have hge : k ≤ skipTrivia arr k := skipTrivia_ge arr k
                omega
              -- apply the ih (at the measure n') with the
              -- min-trick: if p' = size the measure is 0 —
              -- use Nat.le to case... The ih is ONLY for
              -- arr.size - p' = n'. For p' < size it equals n';
              -- for p' = size it's 0. Handle both:
              by_cases hp'size : p' < arr.size
              · have hmeq : arr.size - p' ≤ n' := by
                  have hge : k ≤ skipTrivia arr k := skipTrivia_ge arr k
                  omega
                rw [ih p' hmeq pre (acc.push tok)]
              · -- p' ≥ size: the walk exits; both sides pure:
                rw [tokenizeAux.eq_def (s := arr) (pos := p')
                  (acc := pre ++ (acc.push tok))]
                rw [tokenizeAux.eq_def (s := arr) (pos := p')
                  (acc := acc.push tok)]
                simp only []
                have hpge : arr.size ≤ p' := by omega
                have hskipge2 : arr.size ≤ skipTrivia arr p' :=
                  Nat.le_trans hpge (skipTrivia_ge arr p')
                rw [dif_neg (Nat.not_lt.mpr hskipge2),
                  dif_neg (Nat.not_lt.mpr hskipge2)]
                rfl
            exact hgoal
        | error e =>
            rfl
      · rw [tokenizeAux.eq_def (s := arr) (pos := k) (acc := pre ++ acc)]
        rw [tokenizeAux.eq_def (s := arr) (pos := k) (acc := acc)]
        simp only []
        rw [dif_neg hlt, dif_neg hlt]
        rfl



theorem walk_nl_eq_walk_t (t : Array Char)
    (htw : ∀ (p : Char → Bool) (q : Nat),
      (takeWhile p t q "").2 < t.size)
    (hnoerr : ∀ (k : Nat) (h : k < t.size),
      (lexToken t k h).isOk = true)
    (hnostr : ∀ (k : Nat) (h : k < t.size), (t[k]'h) ≠ '"') :
    ∀ (acc : Array Token),
      tokenizeAux (#[('\n' : Char)] ++ t) 0 acc
        = tokenizeAux t 0 acc := by
  intro acc
  have hskip01 : skipTrivia (#[('\n' : Char)] ++ t) 0
      = skipTrivia (#[('\n' : Char)] ++ t) (#[('\n' : Char)].size + 0) := by
    have hlt : 0 < (#[('\n' : Char)] ++ t).size := by
      rw [Array.size_append, show (#[('\n' : Char)]).size = 1 by decide]
      omega
    rw [skipTrivia.eq_def (s := #[('\n' : Char)] ++ t) (pos := 0)]
    rw [dif_pos hlt]
    rw [show ((#[('\n' : Char)] ++ t)[0]'hlt) = '\n' from by
      have h1 : ((#[('\n' : Char)] ++ t)[0]'hlt)
          = (#[('\n' : Char)] ++ t)[0]! :=
        (arrGetElem!_of_lt hlt).symm
      rw [h1]
      exact nl_head t]
    rw [if_pos (by rfl : (isWhitespace '\n') = true)]
    rw [show (0 : Nat) + 1 = #[('\n' : Char)].size + 0 from by
      show 0 + 1 = 1 + 0
      rfl]
  have hskip1 : skipTrivia (#[('\n' : Char)] ++ t) (#[('\n' : Char)].size + 0)
      = #[('\n' : Char)].size + skipTrivia t 0 :=
    skipTrivia_append_right (s := #[('\n' : Char)]) (t := t) (k := 0)
  -- the walks: unfold both, align the skips; the LHS walk from
  -- nl.size + skip t 0 = the t walk from skip t 0 (right law);
  -- the t walk from skip t 0 = the t walk from 0 (skip_eq with
  -- the skip fixpoint skip t (skip t 0) = skip t 0):
  have hfix : skipTrivia t (skipTrivia t 0) = skipTrivia t 0 :=
    skipTrivia_fixpoint t 0
  have hright := tokenizeAux_append_right_ok
    (s := #[('\n' : Char)]) (t := t) htw hnoerr hnostr
    (skipTrivia t 0) acc
  -- hright : walk (nl ++ t) (nl.size + skip t 0) acc = walk t
  -- (skip t 0) acc
  -- apply hright FIRST (rewrite the walk at the offset), then
  -- align the skip in the result:
  rw [tokenizeAux_skip_eq (#[('\n' : Char)] ++ t) 0
        (#[('\n' : Char)].size + 0) acc hskip01]
  -- now the walk from nl.size + 0; rewrite the position to
  -- nl.size + skip t 0 (the skip fixpoint alignment in the
  -- joined array: skip (nl++t) (nl.size+0) = nl.size + skip t 0
  -- — both are the SAME value by hskip1, so the walks agree):
  have hskipfix : skipTrivia (#[('\n' : Char)] ++ t)
      (#[('\n' : Char)].size + skipTrivia t 0)
      = #[('\n' : Char)].size + skipTrivia t 0 := by
    rw [show skipTrivia (#[('\n' : Char)] ++ t)
        (#[('\n' : Char)].size + skipTrivia t 0)
      = #[('\n' : Char)].size + skipTrivia t (skipTrivia t 0) from
      skipTrivia_append_right (s := #[('\n' : Char)]) (t := t)
        (k := skipTrivia t 0)]
    rw [hfix]
  rw [tokenizeAux_skip_eq (#[('\n' : Char)] ++ t)
        (#[('\n' : Char)].size + 0)
        (#[('\n' : Char)].size + skipTrivia t 0) acc
        (show skipTrivia (#[('\n' : Char)] ++ t) (#[('\n' : Char)].size + 0)
          = skipTrivia (#[('\n' : Char)] ++ t)
              (#[('\n' : Char)].size + skipTrivia t 0) from by
          rw [hskip1, hskipfix])]
  rw [hright]
  rw [tokenizeAux_skip_eq t (skipTrivia t 0) 0 acc hfix]

theorem tokenize_cons_newline_full {s t : Array Char} {toks : Array Token}
    (hsok : tokenizeAux s 0 #[] = .ok toks)
    (hnopct : ∀ (q : Nat) (h : q < s.size), (s[q]'h) ≠ '%')
    (htws : ∀ (p : Char → Bool) (q : Nat) (acc : String),
      (takeWhile p s q acc).2 < s.size)
    (hnoerrs : ∀ (k : Nat) (h : k < s.size),
      (lexToken s k h).isOk = true)
    (hnostrs : ∀ (k : Nat) (h : k < s.size), (s[k]'h) ≠ '"')
    (htwt : ∀ (p : Char → Bool) (q : Nat),
      (takeWhile p t q "").2 < t.size)
    (hnoerrt : ∀ (k : Nat) (h : k < t.size),
      (lexToken t k h).isOk = true)
    (hnostrt : ∀ (k : Nat) (h : k < t.size), (t[k]'h) ≠ '"')
    -- the (nl ++ t)-side premises (the joined tail):
    (htwnl : ∀ (p : Char → Bool) (q : Nat),
      (takeWhile p (#[('\n' : Char)] ++ t) q "").2
        < (#[('\n' : Char)] ++ t).size)
    (hnoerrnl : ∀ (k : Nat) (h : k < (#[('\n' : Char)] ++ t).size),
      (lexToken (#[('\n' : Char)] ++ t) k h).isOk = true)
    (hnostrnl : ∀ (k : Nat) (h : k < (#[('\n' : Char)] ++ t).size),
      ((#[('\n' : Char)] ++ t)[k]'h) ≠ '"') :
    tokenizeAux (s ++ #[('\n' : Char)] ++ t) 0 #[]
      = (tokenizeAux t 0 #[]).map
        (fun acc => toks ++ acc) := by
  -- the associativity: s ++ nl ++ t = s ++ (nl ++ t):
  rw [show s ++ #[('\n' : Char)] ++ t
      = s ++ (#[('\n' : Char)] ++ t) from by
      rw [Array.append_assoc]]
  -- STEP 1: the exit-start dichotomy: if skip s 0 < s.size the
  -- split applies; else the s-walk is empty (toks from the exit
  -- at 0) and the joined walk = the (nl ++ t) walk from 0:
  by_cases hstart : skipTrivia s 0 < s.size
  · -- the split from 0:
    have husize : 0 < (#[('\n' : Char)] ++ t).size := by
      rw [Array.size_append, show (#[('\n' : Char)]).size = 1 by decide]
      omega
    have huhead : (s ++ (#[('\n' : Char)] ++ t))[s.size]'(by
        rw [Array.size_append, Array.size_append,
          show (#[('\n' : Char)]).size = 1 by decide]
        omega) = '\n' := by
      -- the char at s.size is the head of (nl ++ t):
      have hread : (s ++ (#[('\n' : Char)] ++ t))[s.size]'(by
          rw [Array.size_append, Array.size_append,
            show (#[('\n' : Char)]).size = 1 by decide]
          omega)
          = (#[('\n' : Char)] ++ t)[0]'(by
            rw [Array.size_append, show (#[('\n' : Char)]).size = 1 by decide]
            omega) :=
        arrGetElem_append_right' (s := s) (t := #[('\n' : Char)] ++ t)
          (show 0 < (#[('\n' : Char)] ++ t).size from by
            rw [Array.size_append, show (#[('\n' : Char)]).size = 1 by decide]
            omega)
      rw [hread]
      rw [Array.getElem_append_left (show 0 < (#[('\n' : Char)]).size by decide)]
      rfl
    have hsplit := split_helper husize huhead hnopct
      (fun k h h2 h3 => by
        -- the lookahead premise: past s in the joined, the char
        -- at k+1: k+1 = s.size (the separator) or in t. For the
        -- separator it's '\n' (≠ ':' '.'). For t's chars: a ':'
        -- at t[0] would make the t-walk's first token ':...' —
        -- the t-premises (hnoerrt ok) allow any token; the
        -- lookahead premise is about the S-side tokens'
        -- two-char lookahead crossing the boundary — only when
        -- k+1 = s.size (the separator, handled) since the s-side
        -- tokens end before. For k+1 > s.size: the s-token at k
        -- can't exist (k < s.size). So all cases reduce to the
        -- separator or vacuous:
        by_cases hkeq : k + 1 = s.size
        · -- the separator position: the char at k+1 = s.size
          -- is the separator ('\n' ≠ ':' '.'):
          have hread : ((s ++ (#[('\n' : Char)] ++ t))[k + 1]'h3) = '\n' := by
            have hlt : (k + 1) - s.size < (#[('\n' : Char)] ++ t).size := by
              rw [Array.size_append, show (#[('\n' : Char)]).size = 1 by decide]
              omega
            rw [show ((s ++ (#[('\n' : Char)] ++ t))[k + 1]'h3)
              = ((s ++ (#[('\n' : Char)] ++ t))[k + 1]!) from
              (arrGetElem!_of_lt h3).symm]
            have hap := arrGetElem!_append_right' (s := s)
              (t := #[('\n' : Char)] ++ t) (k := (k + 1) - s.size) hlt
            rw [show s.size + ((k + 1) - s.size) = k + 1 from by omega] at hap
            rw [hap]
            rw [show (k + 1) - s.size = 0 from by omega]
            rw [nl_head t]
          rw [hread]
          exact ⟨by intro hc; exact absurd hc (by decide),
            by intro hc; exact absurd hc (by decide)⟩
        · -- k+1 > s.size (past the separator): the s-token at k
          -- would consume past the separator — but the s-side
          -- lexToken at k (in s) doesn't read past s... the
          -- hunif premise covers the JOINED reads: the char at
          -- k+1 in the joined array is a t char. The s-token's
          -- two-char lookahead only happens for ':'/'.' heads —
          -- then the s-walk's token could try to read past s
          -- into the joined. This is the entry-line structure:
          -- a ':' token at the END of s (k+1 = s.size) is the
          -- separator case (handled); k+1 > s.size means k ≥
          -- s.size — but k < s.size. So this case is vacuous
          -- when k+1 ≤ s.size; and k+1 = s.size handled. But
          -- k+1 > s.size with k < s.size means s.size < k+1 ≤
          -- s.size — contradiction:
          exfalso
          omega)
      htws hnoerrs hnostrs 0 #[] hstart
    rw [hsplit, hsok]
    -- STEP 2: the walk from s.size in s ++ (nl ++ t) = the walk
    -- in (nl ++ t) from 0 (the right law at the s boundary):
    -- the (nl++t)-side premises: scans in (nl++t) stop inside
    -- (nl++t); lexing (nl++t) never errors; no strings. The
    -- scans from q ≥ 1 are t's scans (offset); from q = 0 the
    -- '\n' is not a scan char (ident/digit scans stop
    -- immediately on non-matching)... the scan from 0 in
    -- (nl++t): the '\n' fails every predicate → stop 0 < size.
    -- For q ≥ 1: the scan from q = 1 + j equals t's scan from j
    -- (offset) — bounded by htwt.
    -- STEP 2: the walk from s.size in s ++ (nl ++ t) = the walk
    -- in (nl ++ t) from 0 (the right law at the s boundary):
    have htail : (acc' : Array Token) →
        tokenizeAux (s ++ (#[('\n' : Char)] ++ t)) s.size acc'
          = tokenizeAux (#[('\n' : Char)] ++ t) 0 acc' := by
      intro acc'
      exact tokenizeAux_append_right_ok
        (s := s) (t := #[('\n' : Char)] ++ t)
        htwnl hnoerrnl hnostrnl 0 acc'
    -- STEP 3: rewrite the bind body:
    rw [show ((Except.ok toks).bind fun acc' =>
        tokenizeAux (s ++ (#[('\n' : Char)] ++ t)) s.size acc')
        = tokenizeAux (#[('\n' : Char)] ++ t) 0 toks from
        htail toks]
    -- the walk in nl ++ t from 0 = the walk in t from 0 (the
    -- separator is trivia):
    rw [walk_nl_eq_walk_t t htwt hnoerrt hnostrt toks]
    -- the acc homomorphism completes the map form:
    exact tokenizeAux_acc_append t t.size 0
        (show t.size - 0 ≤ t.size by omega) toks #[]
  · -- the exit at 0: the s-walk from 0 exits immediately (the
    -- skip is past the end), so hsok gives toks = #[] (the walk
    -- returns the accumulator):
    have htoks : toks = #[] := by
      rw [tokenizeAux.eq_def (s := s) (pos := 0) (acc := #[])] at hsok
      simp only [] at hsok
      rw [dif_neg hstart] at hsok
      injection hsok with hpair
      cases hpair
      rfl
    subst htoks
    -- the joined walk from 0: the skip in the joined array
    -- skips s's trivia + the separator, landing at the (nl ++ t)
    -- part; by the exit-tail walk (from 0 with the s-skip past
    -- the end): the joined walk = the walk from s.size = the
    -- (nl ++ t) walk from 0 = the t walk from 0 (with [] ++):
    rw [tokenizeAux_exit_tail (acc := #[]) hnopct
      (husize := by
        rw [Array.size_append, show (#[('\n' : Char)]).size = 1 by decide]
        omega)
      (huhead := by
        have hlt : 0 < (#[('\n' : Char)] ++ t).size := by
          rw [Array.size_append, show (#[('\n' : Char)]).size = 1 by decide]
          omega
        have hlt2 : s.size < (s ++ (#[('\n' : Char)] ++ t)).size := by
          rw [Array.size_append]
          rw [Array.size_append]
          rw [show (#[('\n' : Char)]).size = 1 by decide]
          omega
        rw [show ((s ++ (#[('\n' : Char)] ++ t))[s.size]'hlt2)
          = (s ++ (#[('\n' : Char)] ++ t))[s.size]! from
          (arrGetElem!_of_lt hlt2).symm]
        have hap := arrGetElem!_append_right' (s := s)
          (t := #[('\n' : Char)] ++ t) (k := 0) hlt
        rw [show s.size + 0 = s.size from rfl] at hap
        rw [hap]
        exact nl_head t)
      (hle := Nat.zero_le s.size)
      (hexit := Nat.le_of_not_lt (by
        intro hcon
        exact absurd hcon hstart))]
    have hright0 := tokenizeAux_append_right_ok
      (s := s) (t := #[('\n' : Char)] ++ t)
      htwnl hnoerrnl hnostrnl 0 #[]
    rw [show tokenizeAux (s ++ (#[('\n' : Char)] ++ t)) s.size #[]
        = tokenizeAux (#[('\n' : Char)] ++ t) 0 #[] from by
        have h := hright0
        rw [show s.size + 0 = s.size from rfl] at h
        exact h]
    rw [walk_nl_eq_walk_t t htwt hnoerrt hnostrt #[]]
    -- map (fun acc => #[] ++ acc) x = x:
    rw [show (fun (acc : Array Token) => #[] ++ acc) = id from by
      funext acc
      rw [Array.empty_append]
      rfl]
    rw [Except.map_id]
    rfl



/-! ## The identifier half of the lexer round-trip

`tokenize name = .ok #[.ident name]` for a lexable name: the head
is an identifier start (alpha or `_`), every char is an identifier
char, and the name is neither a keyword nor reserved.  Built on
the list/array bridges (`list_toArray_size`, `cons_toArray_read`,
`takeWhile_cons_shift` via `List.toArray_cons` +
`takeWhile_append_right`, `takeWhile_list_all` — the induction
over `takeWhile isIdentChar`), the char-class exclusions
(`isAlpha_not_ws`/`isAlpha_not_pct`), `skipTrivia_ident_head`,
and `lexToken_ident`. -/

theorem list_toArray_size (l : List Char) : l.toArray.size = l.length := rfl

/-- The head read of a cons-list's backing array is the head char. -/
theorem cons_toArray_read (c : Char) (cs : List Char) :
    ((c :: cs : List Char).toArray)[0]'(by
      rw [list_toArray_size]
      simp) = c := by
  rw [List.getElem_toArray (xs := c :: cs) (i := 0) (by
    rw [list_toArray_size]
    simp)]
  simp

/-! ## The list-level all-scan -/

/-- The shifted scan on a cons-list's array is the tail's scan
    with the result offset by 1 (via `List.toArray_cons` and
    `takeWhile_append_right`). -/
theorem takeWhile_cons_shift (p : Char → Bool) (c : Char) (cs : List Char)
    (q : Nat) (acc : String) :
    takeWhile p ((c :: cs : List Char).toArray) (1 + q) acc
      = ((takeWhile p cs.toArray q acc).1, 1 + (takeWhile p cs.toArray q acc).2) := by
  rw [List.toArray_cons]
  exact takeWhile_append_right (p := p) (s := #[c]) (t := cs.toArray)
    (k := q) (acc := acc)

/-- Over a list whose every char satisfies `p`, the scan from any
    position takes all remaining chars. -/
theorem takeWhile_list_all {p : Char → Bool} {l : List Char}
    (hchars : ∀ c ∈ l, p c = true) :
    ∀ (k : Nat) (acc : String), k ≤ l.length →
      takeWhile p l.toArray k acc =
        (acc ++ String.ofList (l.drop k), l.length) := by
  induction l with
  | nil =>
      intro k acc hk
      rw [takeWhile.eq_def]
      rw [dif_neg (by
        show ¬ k < ([] : List Char).toArray.size
        rw [list_toArray_size]
        simp)]
      have hk0 : k = 0 := Nat.le_zero.mp hk
      subst hk0
      show (acc, 0) = (acc ++ String.ofList ([] : List Char), 0)
      rw [String.ofList_nil, String.append_empty]
  | cons c cs ih =>
      intro k acc hk
      have hcc : p c = true := hchars c (by constructor)
      have hcs : ∀ x ∈ cs, p x = true := by
        intro x hx
        exact hchars x (List.mem_cons_of_mem _ hx)
      cases k with
      | zero =>
          rw [takeWhile.eq_def]
          rw [dif_pos (by
            show 0 < ((c :: cs : List Char).toArray).size
            rw [list_toArray_size]
            simp)]
          rw [cons_toArray_read c cs, if_pos hcc, String.push_eq_append]
          rw [show (0 : Nat) + 1 = 1 + 0 from rfl]
          rw [takeWhile_cons_shift p c cs 0 (acc ++ String.singleton c)]
          have hrec := ih hcs 0 (acc ++ String.singleton c) (Nat.zero_le _)
          rw [hrec]
          rw [show (c :: cs).drop 0 = c :: cs from rfl]
          rw [String.ofList_cons, String.append_assoc]
          show ((acc ++ (String.singleton c ++ String.ofList cs), cs.length).1,
            1 + (acc ++ (String.singleton c ++ String.ofList cs), cs.length).2)
            = (acc ++ (String.singleton c ++ String.ofList cs), (c :: cs).length)
          simp
          omega
      | succ k' =>
          rw [show (k' + 1 : Nat) = 1 + k' from Nat.add_comm k' 1,
            show (c :: cs : List Char).drop (1 + k') = cs.drop k' from by
              rw [show (1 + k' : Nat) = k' + 1 from (Nat.add_comm k' 1).symm,
                List.drop_succ_cons]]
          rw [takeWhile_cons_shift p c cs k' acc]
          have hrec := ih hcs k' acc (by
            have : (c :: cs).length = cs.length + 1 := by simp
            omega)
          rw [hrec]
          show ((acc ++ String.ofList (List.drop k' cs), cs.length).1,
            1 + (acc ++ String.ofList (List.drop k' cs), cs.length).2)
            = (acc ++ String.ofList (List.drop k' cs), (c :: cs).length)
          simp
          omega

/-! ## The identifier half of the lexer round-trip -/

/-- The array behind `ofList l` (the tokenize input conversion). -/
theorem internal_toArray_ofList (l : List Char) :
    (String.Internal.toArray (String.ofList l)) = l.toArray := by
  apply Array.toList_inj.mp
  rw [show (String.Internal.toArray (String.ofList l)).toList
    = (String.ofList l).toList from rfl]
  rw [String.toList_ofList]

/-- An alpha character is not whitespace. -/
private theorem isAlpha_not_ws {c : Char} (ha : isAlpha c = true) :
    isWhitespace c = false := by
  unfold isAlpha at ha
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at ha
  have hnot : ∀ (d : Char), (d == ' ' ∨ d == '\t' ∨ d == '\n' ∨ d == '\r') → c ≠ d := by
    intro d hd hcd
    subst hcd
    rcases hd with he | he | he | he
    all_goals have he2 := eq_of_beq he
    all_goals subst he2
    all_goals rcases ha with ⟨h1, h2⟩ | ⟨h1, h2⟩
    all_goals exact absurd h1 (by decide)
  cases h1 : (c == ' ') with
  | true => exact (hnot c (by simp [h1]) rfl).elim
  | false =>
    cases h2 : (c == '\t') with
    | true => exact (hnot c (by simp [h2]) rfl).elim
    | false =>
      cases h3 : (c == '\n') with
      | true => exact (hnot c (by simp [h3]) rfl).elim
      | false =>
        cases h4 : (c == '\r') with
        | true => exact (hnot c (by simp [h4]) rfl).elim
        | false =>
          unfold isWhitespace
          rw [h1, h2, h3, h4]
          rfl

/-- An alpha character is not `%`. -/
private theorem isAlpha_not_pct {c : Char} (ha : isAlpha c = true) :
    (c == '%') = false := by
  have hA : ('A' ≤ c ∧ c ≤ 'Z') ∨ ('a' ≤ c ∧ c ≤ 'z') := by
    unfold isAlpha at ha
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at ha
    exact ha
  cases hcc : (c == '%') with
  | true =>
      have : c = '%' := eq_of_beq hcc
      subst this
      rcases hA with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp at h1 h2
  | false => rfl

/-- A lexable identifier head (alpha or `_`) is not whitespace
    and not `%`. -/
private theorem head_not_trivia {c : Char} (h : isAlpha c = true ∨ c = '_') :
    isWhitespace c = false ∧ (c == '%') = false := by
  rcases h with ha | rfl
  · exact ⟨isAlpha_not_ws ha, isAlpha_not_pct ha⟩
  · exact ⟨by rfl, by rfl⟩

/-- `lexToken` on a cons-array whose head is an identifier start
    and whose chars are all ident chars produces the identifier
    token spanning the whole name. -/
theorem lexToken_ident {c : Char} {cs : List Char}
    (hstart : isAlpha c = true ∨ c = '_')
    (hchars : ∀ x ∈ (c :: cs : List Char), isIdentChar x = true)
    (hkw : keywordToken (String.ofList (c :: cs)) = none)
    (hres : reservedNonFzn.contains (String.ofList (c :: cs)) = false) :
    lexToken ((c :: cs : List Char).toArray) 0 (by
      show 0 < ((c :: cs : List Char).toArray).size
      rw [list_toArray_size]; simp)
      = .ok (.ident (String.ofList (c :: cs)),
          ⟨(c :: cs).length, by
            show 0 < ((c :: cs : List Char).toArray).size
            rw [list_toArray_size]; simp⟩) := by
  have hc : isIdentChar c = true := hchars c (by constructor)
  have hsize0 : 0 < ((c :: cs : List Char).toArray).size := by
    rw [list_toArray_size]; simp
  rw [lexToken]
  simp only [cons_toArray_read c cs]
  -- case the match on c: the 12 punct arms contradict hstart
  -- (c is alpha or '_', never a punct char); the catch-all arm is
  -- the identifier branch
  split
  case h_1 => exact absurd hstart (by
    intro hc'; rcases hc' with h1 | h2
    · exact absurd h1 (by decide)
    · exact absurd h2 (by decide))
  case h_2 => exact absurd hstart (by
    intro hc'; rcases hc' with h1 | h2
    · exact absurd h1 (by decide)
    · exact absurd h2 (by decide))
  case h_3 => exact absurd hstart (by
    intro hc'; rcases hc' with h1 | h2
    · exact absurd h1 (by decide)
    · exact absurd h2 (by decide))
  case h_4 => exact absurd hstart (by
    intro hc'; rcases hc' with h1 | h2
    · exact absurd h1 (by decide)
    · exact absurd h2 (by decide))
  case h_5 => exact absurd hstart (by
    intro hc'; rcases hc' with h1 | h2
    · exact absurd h1 (by decide)
    · exact absurd h2 (by decide))
  case h_6 => exact absurd hstart (by
    intro hc'; rcases hc' with h1 | h2
    · exact absurd h1 (by decide)
    · exact absurd h2 (by decide))
  case h_7 => exact absurd hstart (by
    intro hc'; rcases hc' with h1 | h2
    · exact absurd h1 (by decide)
    · exact absurd h2 (by decide))
  case h_8 => exact absurd hstart (by
    intro hc'; rcases hc' with h1 | h2
    · exact absurd h1 (by decide)
    · exact absurd h2 (by decide))
  case h_9 => exact absurd hstart (by
    intro hc'; rcases hc' with h1 | h2
    · exact absurd h1 (by decide)
    · exact absurd h2 (by decide))
  case h_10 => exact absurd hstart (by
    intro hc'; rcases hc' with h1 | h2
    · exact absurd h1 (by decide)
    · exact absurd h2 (by decide))
  case h_11 => exact absurd hstart (by
    intro hc'; rcases hc' with h1 | h2
    · exact absurd h1 (by decide)
    · exact absurd h2 (by decide))
  case h_12 => exact absurd hstart (by
    intro hc'; rcases hc' with h1 | h2
    · exact absurd h1 (by decide)
    · exact absurd h2 (by decide))
  -- the catch-all arm: the identifier branch
  case h_13 =>
    -- the alpha/underscore dispatch condition is true by hstart:
    have halpha : (isAlpha c || c == '_') = true := by
      rcases hstart with ha | rfl
      · simp [ha]
      · simp
    rw [if_pos halpha]
    -- the takeWhile scan takes the whole rest of the name:
    have hscan := takeWhile_list_all
      (p := isIdentChar) (l := c :: cs) hchars (0 + 1)
      (String.singleton c) (by
        show 0 + 1 ≤ (c :: cs).length
        simp)
    -- the assembled string form of the scan result:
    have hassem : (takeWhile isIdentChar ((c :: cs : List Char).toArray)
        (0 + 1) (String.singleton c)).1
        = String.ofList (c :: cs) := by
      rw [hscan]
      rw [show ((c :: cs : List Char).drop (0 + 1)) = cs from rfl]
      rw [show (String.singleton c ++ String.ofList cs)
        = String.ofList (c :: cs) from by rw [String.ofList_cons]]
    have hposs : (takeWhile isIdentChar ((c :: cs : List Char).toArray)
        (0 + 1) (String.singleton c)).2
        = (c :: cs).length := by
      rw [hscan]
    -- reduce the projections FIRST (non-dependent positions):
    rw [show (takeWhile isIdentChar ((c :: cs : List Char).toArray)
        (0 + 1) (String.singleton c)).1
        = String.ofList (c :: cs) from by
      rw [hscan, show ((c :: cs : List Char).drop (0 + 1)) = cs from rfl,
        show (String.singleton c ++ String.ofList cs)
          = String.ofList (c :: cs) from by rw [String.ofList_cons]]]
    -- the position: hscan's .2; rewrite under the subtype via the
    -- position fact (the anonymous constructor's proof argument is
    -- proof-irrelevant, so `show` the goal in pair form):
    have hpos : (takeWhile isIdentChar ((c :: cs : List Char).toArray)
        (0 + 1) (String.singleton c)).2
        = (c :: cs).length := by rw [hscan]
    -- the keywordToken match reduces by hkw (cases on the option):
    rw [hkw] at *
    -- the reserved check reduces by hres:
    cases hres' : reservedNonFzn.contains (String.ofList (c :: cs)) with
    | true =>
        rw [hres'] at hres
        exact Bool.noConfusion hres
    | false =>
        rw [if_neg (by simp)]
        -- the match on `none` reduces definitionally to the
        -- ident pair with the scan position:
        show Except.ok ((Token.ident (String.ofList (c :: cs)),
          (Subtype.mk ((takeWhile isIdentChar
            ((c :: cs : List Char).toArray) (0 + 1)
            (String.singleton c)).2) (by
              have hge := takeWhile_ge isIdentChar
                ((c :: cs : List Char).toArray) (0 + 1)
                (String.singleton c)
              rw [hpos] at hge
              omega) :
            { q : Nat // 0 < q })) :
          Token × { q : Nat // 0 < q })
          = Except.ok ((Token.ident (String.ofList (c :: cs)),
            (Subtype.mk (c :: cs).length (by simp) :
              { q : Nat // 0 < q })) :
            Token × { q : Nat // 0 < q })
        -- the two subtype values are equal (same value; the
        -- proofs are irrelevant):
        have hval : ((takeWhile isIdentChar
          ((c :: cs : List Char).toArray) (0 + 1)
          (String.singleton c)).2) = (c :: cs).length := hpos
        have hsub : (Subtype.mk ((takeWhile isIdentChar
          ((c :: cs : List Char).toArray) (0 + 1)
          (String.singleton c)).2) (by
            have hge := takeWhile_ge isIdentChar
              ((c :: cs : List Char).toArray) (0 + 1)
              (String.singleton c)
            rw [hval] at hge
            omega) :
          { q : Nat // 0 < q })
          = (Subtype.mk (c :: cs).length (by simp) :
            { q : Nat // 0 < q }) := by
          apply Subtype.ext
          exact hval
        rw [hsub]

/-- A digit char is neither alpha nor `_` (the digit/`-` lexer
    dispatch exclusions). -/
theorem isDigit_not_underscore {c : Char} (h : isDigit c = true) :
    (c == '_') = false := by
  unfold isDigit at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hge, hle⟩ := h
  by_cases hc : c = '_'
  · subst hc
    exact absurd (hle : ('_' : Char) ≤ '9') (by decide)
  · show (c == '_') = false
    by_cases hbeq : (c == '_') = true
    · exact absurd (by simpa using hbeq) hc
    · exact Bool.not_eq_true _ |>.mp (by simpa using hbeq)

theorem isDigit_not_alpha {c : Char} (h : isDigit c = true) :
    isAlpha c = false := by
  have hbounds : ('0' : Char).toNat ≤ c.toNat ∧ c.toNat ≤ ('9' : Char).toNat := by
    unfold isDigit at h
    simp only [decide_eq_true_eq, Bool.and_eq_true] at h
    exact h
  -- isAlpha unfolds to Bool ||; its two disjuncts are false by
  -- the bounds. Drive by cases on each comparison:
  unfold isAlpha
  -- the val comparisons with the bridge:
  have h48 : ('0' : Char).toNat = 48 := rfl
  have h57 : ('9' : Char).toNat = 57 := rfl
  have h65 : ('A' : Char).toNat = 65 := rfl
  have h97 : ('a' : Char).toNat = 97 := rfl
  have hAn : ¬ ('A' : Char).val ≤ c.val := by
    rw [UInt32.le_iff_toNat_le,
      show ('A' : Char).val.toNat = ('A' : Char).toNat from rfl,
      show c.val.toNat = c.toNat from rfl]
    omega
  have han : ¬ ('a' : Char).val ≤ c.val := by
    rw [UInt32.le_iff_toNat_le,
      show ('a' : Char).val.toNat = ('a' : Char).toNat from rfl,
      show c.val.toNat = c.toNat from rfl]
    omega
  -- the first disjunct: decide ('A' ≤ c) && decide (c ≤ 'Z'):
  have hd1 : (decide ('A' ≤ c) && decide (c ≤ 'Z')) = false := by
    by_cases hle : ('A' : Char).val ≤ c.val
    · exact absurd hle hAn
    · rw [show decide ('A' ≤ c) = false from by
        rw [show decide ('A' ≤ c) = decide ('A'.val ≤ c.val) from rfl]
        rw [decide_eq_false hle]]
      simp
  have hd2 : (decide ('a' ≤ c) && decide (c ≤ 'z')) = false := by
    by_cases hle : ('a' : Char).val ≤ c.val
    · exact absurd hle han
    · rw [show decide ('a' ≤ c) = false from by
        rw [show decide ('a' ≤ c) = decide ('a'.val ≤ c.val) from rfl]
        rw [decide_eq_false hle]]
      simp
  rw [hd1, hd2]
  rfl

/-- The `lexToken` result at a digit head of an all-digit array: the
    digit/`-` dispatch fires, `lexInt` takes the decimal arm (no
    `-`, `0x`, `0o`), and the scan runs to the end of the array. -/
theorem lexToken_digits {s : Array Char}
    (hall : ∀ k : Nat, k < s.size → isDigit s[k]! = true)
    (h0 : 0 < s.size) :
    lexToken s 0 h0
      = .ok (.intLit ((parseDecNat (takeWhile isDigit s 0 "").1 : Int)),
          ⟨s.size, h0⟩) := by
  rw [lexToken]
  -- the proof-carrying read agrees with the bang read:
  have hlt0 : 0 < s.size := h0
  have hread : s[0]'hlt0 = s[0]! := by
    rw [Array.getElem_eq_getD, Array.getElem!_eq_getD]
  simp only [hread]
  -- case the match on s[0]!: it is a digit (not a punct, not a
  -- string quote), so the catch-all arm fires; the alpha/underscore
  -- dispatch fails and the digit/`-` dispatch succeeds:
  split
  · rename_i h1
    -- h1 : s[0]! = '(': contradicts isDigit:
    exfalso
    have := hall 0 h0
    rw [h1] at this
    exact absurd this (by decide)
  · rename_i h1
    exfalso
    have := hall 0 h0
    rw [h1] at this
    exact absurd this (by decide)
  · rename_i h1
    exfalso
    have := hall 0 h0
    rw [h1] at this
    exact absurd this (by decide)
  · rename_i h1
    exfalso
    have := hall 0 h0
    rw [h1] at this
    exact absurd this (by decide)
  · rename_i h1
    exfalso
    have := hall 0 h0
    rw [h1] at this
    exact absurd this (by decide)
  · rename_i h1
    exfalso
    have := hall 0 h0
    rw [h1] at this
    exact absurd this (by decide)
  · rename_i h1
    exfalso
    have := hall 0 h0
    rw [h1] at this
    exact absurd this (by decide)
  · rename_i h1
    exfalso
    have := hall 0 h0
    rw [h1] at this
    exact absurd this (by decide)
  · rename_i h1
    exfalso
    have := hall 0 h0
    rw [h1] at this
    exact absurd this (by decide)
  · rename_i h1
    exfalso
    have := hall 0 h0
    rw [h1] at this
    -- ':'-arm
    exact absurd this (by decide)
  · rename_i h1
    exfalso
    have := hall 0 h0
    rw [h1] at this
    -- '.'-arm
    exact absurd this (by decide)
  · rename_i h1
    exfalso
    have := hall 0 h0
    rw [h1] at this
    -- '"'-arm
    exact absurd this (by decide)
  -- the catch-all arm: digit/`-` dispatch
  case h_13 =>
    -- the alpha/underscore dispatch fails (a digit is neither):
    have halpha : (isAlpha s[0]! || s[0]! == '_') = false := by
      rw [Bool.or_eq_false_iff]
      exact ⟨isDigit_not_alpha (hall 0 h0),
        isDigit_not_underscore (hall 0 h0)⟩
    have halpha' : ¬ ((isAlpha s[0]! || s[0]! == '_') = true) := by
      rw [halpha]; exact fun hc => Bool.noConfusion hc
    rw [if_neg halpha']
    -- the digit/`-` dispatch is true by hall:
    rw [if_pos (show (isDigit s[0]! || s[0]! == '-') = true from by
      simp [hall 0 h0])]
    -- lexInt at 0: the leading-'-' guard fails (digit head), then
    -- lexUnsigned takes the decimal arm:
    have hli : lexInt s 0
        = .ok ((.intLit ((parseDecNat (takeWhile isDigit s 0 "").1 : Int)),
            s.size) : Token × Nat) := by
      rw [lexInt_nonneg_head (s := s) (pos := 0) h0 (hall 0 h0),
        lexUnsigned_decimal (s := s) (pos := 0) h0 (hall 0 h0) hall,
        takeWhile_digits_end hall]
      rfl
    -- the equation-bearing match on the (now concrete) lexInt value:
    -- only the ok case is possible (hli); its bound token/pos are
    -- the concrete pair, by injection on the two equations:
    split
    · rename_i t p hi
      have hboth : (Except.ok (t, p) :
          Except String (Token × Nat))
          = Except.ok ((.intLit ((parseDecNat (takeWhile isDigit s 0 "").1 : Int)),
              s.size) : Token × Nat) := by
        rw [← hi]; exact hli
      obtain ⟨ht, hp⟩ := Prod.mk.inj (Except.ok.inj hboth)
      subst ht; subst hp
      rfl
    · rename_i e hi
      rw [hli] at hi
      exact absurd hi (by simp)

/-- `skipTrivia` on an identifier head returns the position (the
    head is neither whitespace nor `%`). -/
theorem skipTrivia_ident_head {c : Char} {cs : List Char}
    (hstart : isAlpha c = true ∨ c = '_') :
    skipTrivia ((c :: cs : List Char).toArray) 0 = 0 := by
  have hsize0 : 0 < ((c :: cs : List Char).toArray).size := by
    rw [list_toArray_size]; simp
  rw [skipTrivia.eq_def]
  rw [dif_pos hsize0]
  rw [cons_toArray_read c cs]
  rcases hstart with ha | rfl
  · have hw : isWhitespace c = false := isAlpha_not_ws ha
    have hp : (c == '%') = false := isAlpha_not_pct ha
    rw [if_neg (by simp [hw]), if_neg (by simp [hp])]
  · rw [if_neg (by
        intro hw
        unfold isWhitespace at hw
        simp only [Bool.or_eq_true, beq_iff_eq] at hw
        rcases hw with h | h | h | h <;> simp at h),
      if_neg (by
        intro hp
        have : ('_' : Char) = '%' := eq_of_beq hp
        simp at this)]

/-- The head-read fact at the generalized proof (transport helper). -/
theorem cons_toArray_read' (c : Char) (cs : List Char)
    (h : 0 < ((c :: cs : List Char).toArray).size) :
    ((c :: cs : List Char).toArray)[0]'h = c := by
  rw [show ((c :: cs : List Char).toArray)[0]'h =
    (((c :: cs : List Char).toArray).getD 0 default) from rfl]
  rw [Array.getD, dif_pos h]
  exact cons_toArray_read c cs

/-- **The identifier half of the lexer round-trip**: tokenizing a
    name whose head is an identifier start (alpha or `_`), whose
    chars are all identifier chars, and which is neither a keyword
    nor reserved, yields exactly one identifier token. -/
theorem tokenize_ident {l : List Char}
    (hne : l ≠ [])
    (hfirst : ∀ c ∈ l, isAlpha c = true ∨ c = '_')
    (hchars : ∀ c ∈ l, isIdentChar c = true)
    (hkw : keywordToken (String.ofList l) = none)
    (hres : reservedNonFzn.contains (String.ofList l) = false) :
    tokenize (String.ofList l) = .ok #[.ident (String.ofList l)] := by
  obtain ⟨c, cs, rfl⟩ : ∃ c cs, l = c :: cs := by
    cases l with
    | nil => exact absurd rfl hne
    | cons c cs => exact ⟨c, cs, rfl⟩
  have hstart : isAlpha c = true ∨ c = '_' := hfirst c (by constructor)
  have hchars' : ∀ x ∈ (c :: cs : List Char), isIdentChar x = true :=
    fun x hx => hchars x hx
  have hsize : ((c :: cs : List Char).toArray).size
      = (c :: cs).length := rfl
  -- the walk: skipTrivia is 0, lexToken yields the ident spanning
  -- the whole name, so the walk recurses at name-length = size and
  -- stops with the single token:
  unfold tokenize
  rw [internal_toArray_ofList (c :: cs)]
  -- tokenizeAux from 0:
  have hskip : skipTrivia ((c :: cs : List Char).toArray) 0 = 0 :=
    skipTrivia_ident_head hstart
  have hlt : 0 < ((c :: cs : List Char).toArray).size := by
    rw [list_toArray_size]; simp
  rw [tokenizeAux.eq_def (s := (c :: cs : List Char).toArray)
    (pos := 0) (acc := #[])]
  -- zeta-reduce the let, then rewrite the skip and take the branch:
  simp only []
  conv =>
    lhs
    rw [hskip]
  rw [dif_pos hlt]
  -- the token fact (same shape as lexToken_ident):
  have htok := lexToken_ident (c := c) (cs := cs) hstart hchars' hkw hres
  rw [htok]
  -- reduce the monadic bind on the ok result:
  show tokenizeAux ((c :: cs : List Char).toArray)
    ((c :: cs).length) #[.ident (String.ofList (c :: cs))]
    = Except.ok #[.ident (String.ofList (c :: cs))]
  -- the recursive walk from name-length = size stops (past end):
  rw [show (c :: cs).length = ((c :: cs : List Char).toArray).size from
    hsize.symm]
  rw [tokenizeAux.eq_def (s := (c :: cs : List Char).toArray)
    (pos := ((c :: cs : List Char).toArray).size) (acc := #[.ident (String.ofList (c :: cs))])]
  -- the skip at size: past the end, skipTrivia returns the
  -- position itself (size):
  have hskipend : skipTrivia ((c :: cs : List Char).toArray)
      ((c :: cs : List Char).toArray).size
      = ((c :: cs : List Char).toArray).size := by
    rw [skipTrivia.eq_def]
    rw [dif_neg (Nat.lt_irrefl _)]
  simp only []
  conv =>
    lhs
    rw [hskipend]
  rw [dif_neg (Nat.lt_irrefl _)]
  -- the final acc: #[] ++ [ident] = #[ident] via Array.push on
  -- the empty start (already in acc position):
  rfl

/-! ## The value half of the lexer round-trip

`tokenize (emitScalar v)` yields exactly one literal token for the
Boolean forms (`tokenize_bool` via `tokenize_keyword`, the keyword
companion of `tokenize_ident`), plus the decimal-digit
characterization of `Nat.toDigits` (`toDigits_digit`,
`toDigits_isDigit`, `toDigits_nonempty`, `digitChar_isDigit`,
`isDigit_not_ws`/`isDigit_not_pct`/`isDigit_not_alpha`,
`takeWhile_digits_all`, `parseDecNat_ofDigits`) — the ingredients
for the integer half's master assembly. -/

theorem digitChar_isDigit (d : Nat) (hd : d < 10) :
    isDigit (Nat.digitChar d) = true := by
  have h1 : (Nat.digitChar d).toNat = '0'.toNat + d := by
    revert d
    decide +revert
  unfold isDigit
  have hboth : (decide ('0' ≤ Nat.digitChar d)
      && decide (Nat.digitChar d ≤ '9')) = true := by
    show (decide ('0'.toNat ≤ (Nat.digitChar d).toNat)
      && decide ((Nat.digitChar d).toNat ≤ '9'.toNat)) = true
    rw [h1]
    have h48049 : ('0' : Char).toNat = 48 := rfl
    have h5758 : ('9' : Char).toNat = 57 := rfl
    rw [h48049, h5758]
    have hle : decide ((48 : Nat) ≤ 48 + d) = true := by
      rw [decide_eq_true (by omega : (48 : Nat) ≤ 48 + d)]
    have hge : decide ((48 : Nat) + d ≤ 57) = true := by
      rw [decide_eq_true (by omega : (48 : Nat) + d ≤ 57)]
    rw [hle, hge]
    rfl
  rw [hboth]

theorem toDigits_digit (n : Nat) :
    ∀ (c : Char), c ∈ Nat.toDigits 10 n →
      ∃ (d : Nat), d < 10 ∧ c = Nat.digitChar d := by
  have key : ∀ (fuel n : Nat) (acc : List Char) (c : Char),
      c ∈ Nat.toDigitsCore 10 fuel n acc →
      (∃ (d : Nat), d < 10 ∧ c = Nat.digitChar d) ∨ c ∈ acc := by
    intro fuel
    induction fuel with
    | zero =>
        intro n acc c hc
        -- toDigitsCore 10 0 n acc = acc (no fuel): membership
        -- is in acc
        exact Or.inr hc
    | succ fuel' ih =>
        intro n acc c hc
        rw [Nat.toDigitsCore.eq_2] at hc
        by_cases hz : n / 10 = 0
        · rw [if_pos hz] at hc
          simp only [List.mem_cons] at hc
          rcases hc with hcc | hc2
          · exact Or.inl ⟨n % 10, Nat.mod_lt n (by decide), hcc⟩
          · exact Or.inr hc2
        · rw [if_neg hz] at hc
          -- membership in the recursive output: head or in acc
          -- (via the List.Mem cases on the cons-headed list after
          -- unfolding the inner core — the inner core's fuel is
          -- fuel', so its output IS the cons; use the IH's shape)
          -- the IH covers the recursive core with the extended acc:
          rcases ih (n / 10) ((n % 10).digitChar :: acc) c hc with h | h
          · exact Or.inl h
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
            rcases h with h1 | h2
            · exact Or.inl ⟨n % 10, Nat.mod_lt n (by decide), h1⟩
            · exact Or.inr h2
  intro c hc
  rw [show Nat.toDigits 10 n = Nat.toDigitsCore 10 (n + 1) n [] from rfl] at hc
  rcases key (n + 1) n [] c hc with h | h
  · exact h
  · cases h

/-- Every char of `Nat.toDigits 10 n` is a digit. -/

theorem toDigits_isDigit (n : Nat) :
    ∀ (c : Char), c ∈ Nat.toDigits 10 n → isDigit c = true := by
  intro c hc
  obtain ⟨d, hd, rfl⟩ := toDigits_digit n c hc
  exact digitChar_isDigit d hd

/-- The digits are nonempty. -/

theorem toDigits_nonempty (n : Nat) : Nat.toDigits 10 n ≠ [] := by
  intro hnil
  -- the value reconstruction: repr_val says the fold over the
  -- digits reconstructs n; an empty fold gives 0, forcing
  -- n = the fold-0 whose digits are ['0'] ≠ []:
  have hfold : (Nat.repr n).foldl (fun acc c => acc * 10 + toDigit c) 0 = n :=
    repr_val n
  rw [show Nat.repr n = String.ofList (Nat.toDigits 10 n) from rfl,
    hnil] at hfold
  -- hfold : foldl .. (ofList []) = n, i.e. 0 = n
  have hfold0 : String.foldl (fun acc c => acc * 10 + toDigit c) 0
      (String.ofList ([] : List Char)) = 0 := by
    rw [String.foldl_eq_foldl_toList]
    rw [show (String.ofList ([] : List Char)).toList = ([] : List Char) from rfl]
    rw [List.foldl_nil]
  rw [hfold0] at hfold
  -- hfold : 0 = n — so n's digits are 0's digits = ['0']:
  subst hfold
  exact absurd hnil (by rw [show Nat.toDigits 10 0 = ['0'] from rfl]; simp)

-- the scan over an all-digit list takes everything (via
-- takeWhile_list_all instantiated to isDigit):

theorem takeWhile_digits_all {l : List Char}
    (hdigits : ∀ c ∈ l, isDigit c = true) :
    takeWhile isDigit l.toArray 0 ""
      = (String.ofList l, l.length) :=
  takeWhile_list_all (p := isDigit) (l := l) hdigits 0 "" (Nat.zero_le _)

theorem isDigit_not_ws {c : Char} (h : isDigit c = true) :
    isWhitespace c = false := by
  have hbounds : ('0' : Char).toNat ≤ c.toNat ∧ c.toNat ≤ ('9' : Char).toNat := by
    unfold isDigit at h
    simp only [decide_eq_true_eq, Bool.and_eq_true] at h
    exact h
  cases hws : isWhitespace c with
  | true =>
      unfold isWhitespace at hws
      simp only [Bool.or_eq_true, beq_iff_eq] at hws
      rcases hws with ((he1 | he1) | he1) | he1
      · rw [he1] at hbounds
        have h32 : (' ' : Char).toNat = 32 := rfl
        have h48 : ('0' : Char).toNat = 48 := rfl
        omega
      · rw [he1] at hbounds
        have h9 : ('\t' : Char).toNat = 9 := rfl
        have h48 : ('0' : Char).toNat = 48 := rfl
        omega
      · rw [he1] at hbounds
        have h10 : ('\n' : Char).toNat = 10 := rfl
        have h48 : ('0' : Char).toNat = 48 := rfl
        omega
      · rw [he1] at hbounds
        have h13 : ('\r' : Char).toNat = 13 := rfl
        have h48 : ('0' : Char).toNat = 48 := rfl
        omega
  | false => rfl

theorem isDigit_not_pct {c : Char} (h : isDigit c = true) :
    (c == '%') = false := by
  have hbounds : ('0' : Char).toNat ≤ c.toNat ∧ c.toNat ≤ ('9' : Char).toNat := by
    unfold isDigit at h
    simp only [decide_eq_true_eq, Bool.and_eq_true] at h
    exact h
  cases hcc : (c == '%') with
  | true =>
      have hc2 : c = '%' := eq_of_beq hcc
      subst hc2
      unfold isDigit at h
      simp only [decide_eq_true_eq, Bool.and_eq_true] at h
      exact absurd h.1 (by decide)
  | false => rfl


theorem parseDecNat_ofDigits (n : Nat) :
    parseDecNat (String.ofList (Nat.toDigits 10 n)) = n := by
  show (String.ofList (Nat.toDigits 10 n)).foldl
      (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0 = n
  rw [String.foldl_eq_foldl_toList, String.toList_ofList]
  rw [show (fun (acc : Nat) c => acc * 10 + (c.toNat - '0'.toNat))
      = (fun acc c => acc * 10 + toDigit c) from by
    funext acc c
    rfl]
  have hrepr : Nat.repr n = String.ofList (Nat.toDigits 10 n) := rfl
  have h := repr_val n
  -- h : Nat.repr n's fold = n; Nat.repr n unfolds to ofList:
  rw [hrepr] at h
  rw [String.foldl_eq_foldl_toList, String.toList_ofList] at h
  exact h

theorem tokenize_keyword {l : List Char}
    (hne : l ≠ [])
    (hfirst : ∀ c ∈ l, isAlpha c = true ∨ c = '_')
    (hchars : ∀ c ∈ l, isIdentChar c = true)
    (hkw : keywordToken (String.ofList l) = some tok) :
    tokenize (String.ofList l) = .ok #[tok] := by
  obtain ⟨c, cs, rfl⟩ : ∃ c cs, l = c :: cs := by
    cases l with
    | nil => exact absurd rfl hne
    | cons c cs => exact ⟨c, cs, rfl⟩
  have hstart : isAlpha c = true ∨ c = '_' := hfirst c (by constructor)
  have hchars' : ∀ x ∈ (c :: cs : List Char), isIdentChar x = true :=
    fun x hx => hchars x hx
  have hsize : ((c :: cs : List Char).toArray).size
      = (c :: cs).length := rfl
  have hskip : skipTrivia ((c :: cs : List Char).toArray) 0 = 0 :=
    skipTrivia_ident_head hstart
  have hlt : 0 < ((c :: cs : List Char).toArray).size := by
    rw [list_toArray_size]; simp
  unfold tokenize
  rw [internal_toArray_ofList (c :: cs)]
  rw [tokenizeAux.eq_def (s := (c :: cs : List Char).toArray)
    (pos := 0) (acc := #[])]
  simp only []
  conv =>
    lhs
    rw [hskip]
  rw [dif_pos hlt]
  -- lexToken: mirror lexToken_ident but with hkw = some:
  -- the lexToken result, stated over an abstract position:
  have hlex : lexToken ((c :: cs : List Char).toArray) 0 (by
      show 0 < ((c :: cs : List Char).toArray).size
      rw [list_toArray_size]; simp)
      = .ok (tok, ⟨(c :: cs).length, by
        show 0 < ((c :: cs : List Char).toArray).size
        rw [list_toArray_size]; simp⟩) := by
    rw [lexToken]
    simp only [cons_toArray_read c cs]
    split
    case h_1 => exact absurd hstart (by
      intro hc'; rcases hc' with h1 | h2
      · exact absurd h1 (by decide)
      · exact absurd h2 (by decide))
    case h_2 => exact absurd hstart (by
      intro hc'; rcases hc' with h1 | h2
      · exact absurd h1 (by decide)
      · exact absurd h2 (by decide))
    case h_3 => exact absurd hstart (by
      intro hc'; rcases hc' with h1 | h2
      · exact absurd h1 (by decide)
      · exact absurd h2 (by decide))
    case h_4 => exact absurd hstart (by
      intro hc'; rcases hc' with h1 | h2
      · exact absurd h1 (by decide)
      · exact absurd h2 (by decide))
    case h_5 => exact absurd hstart (by
      intro hc'; rcases hc' with h1 | h2
      · exact absurd h1 (by decide)
      · exact absurd h2 (by decide))
    case h_6 => exact absurd hstart (by
      intro hc'; rcases hc' with h1 | h2
      · exact absurd h1 (by decide)
      · exact absurd h2 (by decide))
    case h_7 => exact absurd hstart (by
      intro hc'; rcases hc' with h1 | h2
      · exact absurd h1 (by decide)
      · exact absurd h2 (by decide))
    case h_8 => exact absurd hstart (by
      intro hc'; rcases hc' with h1 | h2
      · exact absurd h1 (by decide)
      · exact absurd h2 (by decide))
    case h_9 => exact absurd hstart (by
      intro hc'; rcases hc' with h1 | h2
      · exact absurd h1 (by decide)
      · exact absurd h2 (by decide))
    case h_10 => exact absurd hstart (by
      intro hc'; rcases hc' with h1 | h2
      · exact absurd h1 (by decide)
      · exact absurd h2 (by decide))
    case h_11 => exact absurd hstart (by
      intro hc'; rcases hc' with h1 | h2
      · exact absurd h1 (by decide)
      · exact absurd h2 (by decide))
    case h_12 => exact absurd hstart (by
      intro hc'; rcases hc' with h1 | h2
      · exact absurd h1 (by decide)
      · exact absurd h2 (by decide))
    case h_13 =>
      have halpha : (isAlpha c || c == '_') = true := by
        rcases hstart with ha | rfl
        · simp [ha]
        · simp
      rw [if_pos halpha]
      have hscan := takeWhile_list_all
        (p := isIdentChar) (l := c :: cs) hchars' (0 + 1)
        (String.singleton c) (by
          show 0 + 1 ≤ (c :: cs).length
          simp)
      rw [show (takeWhile isIdentChar ((c :: cs : List Char).toArray)
          (0 + 1) (String.singleton c)).1
          = String.ofList (c :: cs) from by
        rw [hscan, show ((c :: cs : List Char).drop (0 + 1)) = cs from rfl,
          show (String.singleton c ++ String.ofList cs)
            = String.ofList (c :: cs) from by rw [String.ofList_cons]]]
      -- the keyword match by hkw (rewrites the scrutinee); the
      -- position by hscan:
      rw [hkw]
      have hposs : (takeWhile isIdentChar ((c :: cs : List Char).toArray)
          (0 + 1) (String.singleton c)).2
          = (c :: cs).length := by rw [hscan]
      -- reduce the ok-pair with the position (proof-irrelevant):
      have hsub : (Subtype.mk ((takeWhile isIdentChar
            ((c :: cs : List Char).toArray) (0 + 1)
            (String.singleton c)).2) (by
              have hge := takeWhile_ge isIdentChar
                ((c :: cs : List Char).toArray) (0 + 1)
                (String.singleton c)
              rw [hposs] at hge
              omega) :
            { q : Nat // 0 < q })
          = (Subtype.mk (c :: cs).length (by
              show 0 < ((c :: cs : List Char).toArray).size
              rw [list_toArray_size]; simp) :
            { q : Nat // 0 < q }) := by
        apply Subtype.ext
        exact hposs
      rw [hsub]
      rfl
  -- the main walk: rewrite the lexToken by hlex via the
  -- match-cases (dependent): use rw [hlex] inside conv to dodge
  -- the motive:
  -- reduce via the bind-on-ok equation:
  have hbind : (do
      let __x ← ((.ok (tok, ⟨(c :: cs).length, by
        show 0 < ((c :: cs : List Char).toArray).size
        rw [list_toArray_size]; simp⟩) :
        Except String (Token × { q : Nat // 0 < q })))
      tokenizeAux ((c :: cs : List Char).toArray) __x.2.val
        (#[].push __x.1))
      = tokenizeAux ((c :: cs : List Char).toArray)
          ((c :: cs).length) #[tok] := by rfl
  conv =>
    lhs
    rw [hlex]
  rw [hbind]
  -- the recursive walk at length = size stops:
  rw [show (c :: cs).length = ((c :: cs : List Char).toArray).size from
    hsize.symm]
  rw [tokenizeAux.eq_def (s := (c :: cs : List Char).toArray)
    (pos := ((c :: cs : List Char).toArray).size) (acc := #[tok])]
  have hskipend : skipTrivia ((c :: cs : List Char).toArray)
      ((c :: cs : List Char).toArray).size
      = ((c :: cs : List Char).toArray).size := by
    rw [skipTrivia.eq_def]
    rw [dif_neg (Nat.lt_irrefl _)]
  simp only []
  conv =>
    lhs
    rw [hskipend]
  rw [dif_neg (Nat.lt_irrefl _)]
  rfl

/-- **The bool half of the value round-trip**: tokenizing the
    emitted form of a Boolean yields exactly one `boolLit`. -/

theorem tokenize_bool (b : Bool) :
    tokenize (emitScalar (.bool b)) = .ok #[.boolLit b] := by
  cases b with
  | true =>
      show tokenize "true" = .ok #[.boolLit true]
      have hkw : keywordToken (String.ofList ['t', 'r', 'u', 'e'])
          = some (.boolLit true) := rfl
      exact tokenize_keyword (l := ['t', 'r', 'u', 'e'])
        (hne := by simp)
        (hfirst := by decide) (hchars := by decide) hkw
  | false =>
      show tokenize "false" = .ok #[.boolLit false]
      have hkw : keywordToken (String.ofList ['f', 'a', 'l', 's', 'e'])
          = some (.boolLit false) := rfl
      exact tokenize_keyword (l := ['f', 'a', 'l', 's', 'e'])
        (hne := by simp)
        (hfirst := by decide) (hchars := by decide) hkw

/-- The walk past the end of the array stops with the accumulator
    (the skip is the position itself and the branch is not taken). -/
theorem tokenizeAux_stop {s : Array Char} {acc : Array Token} :
    tokenizeAux s s.size acc = Except.ok acc := by
  rw [tokenizeAux.eq_def (s := s) (pos := s.size) (acc := acc)]
  have hskip : skipTrivia s s.size = s.size := by
    rw [skipTrivia.eq_def]
    rw [dif_neg (Nat.lt_irrefl _)]
  simp only [hskip]
  rw [dif_neg (Nat.lt_irrefl _)]
  rfl

/-! ### The master assembly: the integer half of the round-trip

`emitInt`'s nonnegative form is `Nat.repr n` = the digit string
`Nat.toDigits 10 n`.  `tokenize_int_nonneg` pins the lexing of that
text: one `intLit n` token, spanning exactly the text.  The walk is
the `tokenize_ident` pattern with the digit branch in place of the
identifier branch; the value comes from `toDigitsCore_val` through
the `parseDecNat`-delta coincidence. -/

/-- **The integer half of the lexer round-trip** (nonnegative):
    tokenizing the printed form of a natural `n` — `Nat.repr n`, the
    digit string `Nat.toDigits 10 n` — yields exactly one `intLit n`
    token spanning the whole text. -/
theorem tokenize_int_nonneg (n : Nat) :
    tokenize (String.ofList (Nat.toDigits 10 n)) = .ok #[.intLit n] := by
  -- the digit-list facts:
  have hdigits : ∀ (c : Char), c ∈ Nat.toDigits 10 n → isDigit c = true :=
    toDigits_isDigit n
  have hne : Nat.toDigits 10 n ≠ [] := toDigits_nonempty n
  -- name the digit list:
  generalize hl : Nat.toDigits 10 n = l at hdigits hne ⊢
  -- the cons shape (the digits are nonempty):
  obtain ⟨c0, rest, rfl⟩ : ∃ c0 rest, l = c0 :: rest := by
    cases l with
    | nil => exact absurd rfl hne
    | cons c cs => exact ⟨c, cs, rfl⟩
  have hdigits' : ∀ x ∈ (c0 :: rest : List Char), isDigit x = true :=
    fun x hx => by
      have := hdigits x (hl ▸ hx)
      exact this
  -- the array facts:
  have hsize : ((c0 :: rest : List Char).toArray).size
      = (c0 :: rest).length := rfl
  have h0 : 0 < ((c0 :: rest : List Char).toArray).size := by
    rw [hsize]; simp
  have hall : ∀ k : Nat, k < ((c0 :: rest : List Char).toArray).size →
      isDigit ((c0 :: rest : List Char).toArray)[k]! = true := by
    intro k hk
    rw [list_toArray_size] at hk
    have hread : ((c0 :: rest : List Char).toArray)[k]!
        = (c0 :: rest)[k] := by
      have hget : ((c0 :: rest : List Char))[k]? = some ((c0 :: rest)[k]) := by
        simp [hk]
      simp [hk, List.getElem_toArray, hget]
    rw [hread]
    exact hdigits' _ (List.getElem_mem hk)
  -- the value fact: the text parses back to n:
  have hval : parseDecNat (String.ofList (c0 :: rest : List Char)) = n := by
    show (String.ofList (c0 :: rest : List Char)).foldl
      (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0 = n
    rw [String.foldl_eq_foldl_toList, String.toList_ofList]
    have h0' : (Nat.toDigits 10 n).foldl
        (fun acc c => acc * 10 + toDigit c) 0 = n :=
      toDigitsCore_val n (n + 1) (Nat.lt_succ_self n)
    rw [hl] at h0'
    exact h0'
  -- the token fact (lexToken_digits, with the scan's .1 the whole
  -- text and the value rewritten to n):
  have htok := lexToken_digits (s := ((c0 :: rest : List Char).toArray))
    hall h0
  rw [takeWhile_digits_end hall] at htok
  rw [show ((c0 :: rest : List Char).toArray).toList
      = (c0 :: rest : List Char) from rfl] at htok
  rw [hval] at htok
  -- the walk, exactly as tokenize_ident: unfold tokenize, the skip
  -- at 0 is 0 (a digit head is neither whitespace nor `%`), the
  -- lexToken result steps the walk to the size, and past the end
  -- the walk stops with the single token:
  have hws : isWhitespace ((c0 :: rest : List Char).toArray)[0]! = false :=
    isDigit_not_ws (hall 0 h0)
  have hpct : (((c0 :: rest : List Char).toArray)[0]! == '%') = false :=
    isDigit_not_pct (hall 0 h0)
  have hskip : skipTrivia ((c0 :: rest : List Char).toArray) 0 = 0 := by
    rw [skipTrivia.eq_def, dif_pos h0]
    -- the goal's `have c := s[0]` binds the (no-bang) read; both
    -- class facts hold for it as for the bang read (defeq):
    show (if isWhitespace ((c0 :: rest : List Char).toArray)[0] = true
        then skipTrivia ((c0 :: rest : List Char).toArray) (0 + 1)
        else if (((c0 :: rest : List Char).toArray)[0] == '%') = true
          then skipTrivia ((c0 :: rest : List Char).toArray)
              (skipToNewline ((c0 :: rest : List Char).toArray) (0 + 1))
          else 0) = 0
    rw [if_neg (by
        intro hcon
        rw [show ((c0 :: rest : List Char).toArray)[0]
            = ((c0 :: rest : List Char).toArray)[0]! from rfl] at hcon
        rw [hws] at hcon
        exact Bool.noConfusion hcon)]
    rw [if_neg (by
        intro hcon
        rw [show ((c0 :: rest : List Char).toArray)[0]
            = ((c0 :: rest : List Char).toArray)[0]! from rfl] at hcon
        rw [hpct] at hcon
        exact Bool.noConfusion hcon)]
  unfold tokenize
  rw [hl, internal_toArray_ofList (c0 :: rest)] at *
  rw [tokenizeAux.eq_def (s := ((c0 :: rest : List Char).toArray))
    (pos := 0) (acc := #[])]
  simp only []
  conv =>
    lhs
    rw [hskip]
  rw [dif_pos h0, htok]
  -- the bind on the ok result reduces to the walk with the pushed
  -- token; then the walk from the token end = size stops (past
  -- end) with the single token:
  have hbind : ∀ (x : Token × {q : Nat // 0 < q}),
      (Except.ok x : Except String (Token × {q : Nat // 0 < q})).bind
        (fun __x => tokenizeAux ((c0 :: rest : List Char).toArray) __x.2.1
          (#[].push __x.1))
      = tokenizeAux ((c0 :: rest : List Char).toArray) x.2.1
          #[x.1] := fun x => rfl
  -- the value: parseDecNat (the text) = n:
  rw [hval] at *
  -- past the end: the walk stops with the accumulator:
  exact tokenizeAux_stop

end LexerCons

end LeanFzn.Solver
