import Std

namespace BoyerMoore

def IsMajority {α : Type} [DecidableEq α]
  (a : α) (xs : List α) : Prop :=
  xs.length < 2 * xs.countP (· = a)

end BoyerMoore
