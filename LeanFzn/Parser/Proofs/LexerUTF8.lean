/-
Purpose: Constructive bridge between the standard UTF-8 decoder and the
independent encoding-based string meaning; no scanner is used in the statement.
Dependencies: Lexical's EncodesUTF8 and the standard library string/byte laws.
DAG: Independent lexical spec -> this bridge -> escape/string correctness.
-/
import LeanFzn.Parser.Lexical
import Init.Data.ByteArray.Lemmas
import Init.Data.String.Basic

namespace LeanFzn.Parser.Lexer
open LeanFzn.Parser.Lexical

theorem fromUTF8?_eq_some_iff (bytes : ByteArray) (value : String) :
    String.fromUTF8? bytes = some value ↔ value.toUTF8 = bytes := by
  unfold String.fromUTF8?
  split
  · rename_i h
    constructor
    · intro heq
      have hv : String.fromUTF8 bytes h = value := Option.some.inj heq
      rw [← hv]
      rfl
    · intro heq
      have hv : String.fromUTF8 bytes h = value := by
        apply String.toByteArray_inj.mp
        simpa [String.fromUTF8] using heq.symm
      exact congrArg some hv
  · rename_i h
    constructor
    · intro heq
      cases heq
    · intro heq
      apply False.elim
      apply h
      rw [← heq]
      exact value.isValidUTF8

theorem fromUTF8?_eq_some_iff_encodes (bytes : ByteArray) (value : String) :
    String.fromUTF8? bytes = some value ↔ EncodesUTF8 bytes.data.toList value := by
  rw [fromUTF8?_eq_some_iff]
  unfold EncodesUTF8
  constructor
  · intro h
    rw [h]
  · intro h
    exact ByteArray.ext (Array.toList_inj.mp h)

end LeanFzn.Parser.Lexer
