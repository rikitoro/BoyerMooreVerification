import Std.Tactic.Do

open Std.Do

namespace BoyerMoore

def majorityCandicdate {α : Type} [Inhabited α] [DecidableEq α]
  (votes : List α) : α := Id.run do
  let mut m : α := default
  let mut c : Nat := 0

  for v in votes do
    if c = 0 then
      m := v
      c := 1
    else if m = v then
      c := c + 1
    else
      c := c - 1

  return m


end BoyerMoore
