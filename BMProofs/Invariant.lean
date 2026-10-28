import BMProofs.Counting

namespace BoyerMoore.Checked

variable {α : Type} [DecidableEq α]

/-! # Loop invariant
majorityCandidate のループ不変条件とその性質を定義する
-/

/--
処理済みリスト `pref` に対するループ不変条件
- `m` : 現在の候補
- `c` : 候補の残り票数

以下の 3 条件 :
1. `c` は候補 `m` の実際の出現回数以下
2. 候補 `m` の出現回数に対する上界
3. 候補 `m` 以外の要素の出現回数に対する上界
-/
def LoopInv (pref : List α) (m : α) (c : Nat) : Prop  :=
  c ≤ pref.countP (· = m) ∧
  2 * pref.countP (· = m) ≤ pref.length + c ∧
  ∀ a, a ≠ m → 2 * pref.countP (· = a) + c ≤ pref.length

/--
初期状態ではループ不変条件が成り立つ
-/
theorem LoopInv.init [Inhabited α] :
  LoopInv ([] : List α) (default : α) 0 := by
  simp [LoopInv]

/--
カウンタ `c = 0` のとき
処理済みリストには過半数要素が存在しない
-/
theorem LoopInv.zero
  {pref : List α} {m : α} {c : Nat}
  (hInv : LoopInv pref m c)
  (hc : c = 0) :
  ∀ a, 2 * pref.countP (· = a) ≤ pref.length := by
  intro a
  rcases hInv with ⟨_, hc, hother⟩
  by_cases h : a = m <;> simp_all

/--
ループ終了時に不変条件が成り立っていれば
真の過半数要素 `a` は現在の候補 `m` と一致する
-/
theorem LoopInv.result
  {pref : List α} {m : α} {c : Nat}
  (hInv : LoopInv pref m c)
  (a : α)
  (ha : BoyerMoore.IsMajority a pref) :
  m = a := by
  by_cases h : a = m
  · apply h.symm
  · have hother : 2 * pref.countP (· = a) + c ≤ pref.length := hInv.2.2 a h
    have hmajor : pref.length < 2 * pref.countP (· = a) := ha
    omega


end BoyerMoore.Checked
