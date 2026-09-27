import LeanFzn
open LeanFzn

example (a : List Value) (hpx : some a[0]! = some (Value.int 3)) : True := by
  cases hai : a[0]! with
  | int v =>
      have hiv : Value.int v = Value.int 3 := hpx
      trivial
  | other => trivial
