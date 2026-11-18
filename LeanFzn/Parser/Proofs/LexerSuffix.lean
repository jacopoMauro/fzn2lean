/-
# Character-suffix view of an `Array Char`

Purpose: present the unconsumed input of a positional scanner as a character
list, so that specifications phrased over `List Char` can be compared with the
array-based executable lexer.

`Suffix.toList s i` is the tail of `Array.toList` after stripping `i` leading
characters.  The lemmas below are deliberately elementary; nothing here
mentions a scanner function.
-/
import LeanFzn.Parser.Lexer

namespace LeanFzn.Parser.Lexer
namespace Suffix

/-- The character suffix of `s` starting at position `i`. -/
def toList (s : Array Char) (i : Nat) : List Char :=
  s.toList.drop i

theorem toList_def (s : Array Char) (i : Nat) : toList s i = s.toList.drop i := rfl

theorem length_toList (s : Array Char) : s.toList.length = s.size :=
  Array.length_toList (xs := s)

theorem toList_size (s : Array Char) (i : Nat) : (toList s i).length = s.size - i := by
  unfold toList
  rw [List.length_drop, Array.length_toList]

theorem toList_eq_nil_iff (s : Array Char) (i : Nat) : toList s i = [] ↔ s.size ≤ i := by
  unfold toList
  rw [List.drop_eq_nil_iff, Array.length_toList]

/-- A character at an in-range position is the head of the suffix. -/
theorem toList_getElem (s : Array Char) (i : Nat) (h : i < s.size) :
    toList s i = s[i] :: toList s (i + 1) := by
  unfold toList
  rw [List.drop_eq_getElem_cons (by simpa [Array.length_toList] using h)]
  rfl

theorem toList_take_append (s : Array Char) (i j : Nat) (h : i ≤ j) :
    toList s i = (toList s i).take (j - i) ++ toList s j := by
  unfold toList
  have h' := List.take_append_drop (j - i) (s.toList.drop i)
  rw [List.drop_drop] at h'
  rw [show i + (j - i) = j by omega] at h'
  exact h'.symm

/-- Invert a nonempty suffix, recovering its actual indexed head and tail. -/
theorem cons_inv {s : Array Char} {pos : Nat} {c : Char} {cs : List Char}
    (hs : toList s pos = c :: cs) :
    ∃ h : pos < s.size, s[pos] = c ∧ toList s (pos + 1) = cs := by
  have hi : pos < s.size := by
    have hn : toList s pos ≠ [] := by rw [hs]; simp
    have : ¬ s.size ≤ pos := fun h => hn ((toList_eq_nil_iff s pos).mpr h)
    omega
  refine ⟨hi, ?_⟩
  rw [toList_getElem s pos hi] at hs
  exact List.cons.inj hs

end Suffix
end LeanFzn.Parser.Lexer
