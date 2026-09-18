import LeanFzn
import solver.Emit
open LeanFzn.Lexer LeanFzn.Solver

-- 1/2: parseDecNat of a digit-text equals the toDigit fold (defeq):
example (l : List Char) :
    parseDecNat (String.ofList l)
      = l.foldl (fun acc c => acc * 10 + toDigit c) 0 := by
  show (String.ofList l).foldl
    (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0 = _
  rw [String.foldl_eq_foldl_toList, String.toList_ofList]
  rfl

-- 3: parseDecNat (String.ofList (Nat.toDigits 10 n)) = n:
example (n : Nat) : parseDecNat (String.ofList (Nat.toDigits 10 n)) = n := by
  show (String.ofList (Nat.toDigits 10 n)).foldl
    (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0 = n
  rw [String.foldl_eq_foldl_toList, String.toList_ofList]
  have h := toDigitsCore_val n (n + 1) (Nat.lt_succ_self n)
  rw [show Nat.toDigits 10 n = Nat.toDigitsCore 10 (n + 1) n [] from rfl]
  exact h
