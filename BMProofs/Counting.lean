import BMModel.Specification

namespace BoyerMoore.Checked

variable {α : Type} [DecidableEq α]

/-! # Counting lemmas
ループ不変条件の検証で必要となる
リスト中の要素の出現回数に関する補題
-/

/--
リスト末尾に `v` を追加したとき
要素 `a` の出現回数は `v = a` なら 1 増え
そうでなければ変化しない
-/
theorem countP_append_single
  (pref : List α) (a v : α) :
  (pref ++ [v]).countP (· = a) =
  pref.countP (· = a) + (if v = a then 1 else 0) := by
  grind

/--
リスト末尾に `v` を追加すると
`v` 自身の出現回数は 1 増える
-/
theorem countP_append_same
  (pref : List α) (v : α) :
  (pref ++ [v]).countP (· = v) = pref.countP (· = v) + 1 := by
  grind
/--
`v ≠ a` なら、リスト末尾に `v` を追加しても
`a` の出現回数は変化しない
-/
theorem countP_append_ne
  (pref : List α) (a v : α)
  (h : v ≠ a) :
  (pref ++ [v]).countP (· = a) =
  pref.countP (· = a) := by
  grind

end BoyerMoore.Checked
