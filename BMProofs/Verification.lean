import BMModel.Algorithm
import BMModel.Specification

namespace BoyerMoore.Checked

theorem candidate_correct
  {α : Type} [Inhabited α] [DecidableEq α]
  (xs : List α) (a : α)
  (h : BoyerMoore.IsMajority a xs) :
  BoyerMoore.majorityCandidate xs = a := by
  sorry

end BoyerMoore.Checked
