import BMProofs.Invariant


namespace BoyerMoore.Checked

variable {α : Type} [DecidableEq α]

/-! # Preservation of loop invariant -/

/-- Case 1: `c = 0`
  カウンタが 0 の時、新しい入力 `v` を候補に設定し、カウンタを 1 にする
  `m := v`
  `c := 1`
-/
theorem LoopInv.step_zero
  (pref : List α) (m v : α) (c : Nat)
  (hInv : LoopInv pref m c)
  (hc : c = 0) :
  LoopInv (pref ++ [v]) v 1 := by
  have hall := LoopInv.zero hInv hc
  unfold LoopInv
  constructor
  · grind
  · constructor
    · have hv := hall v
      grind
    · intro a ha
      have hne : v ≠ a := by grind
      simp_all


/-- Case 2: `c ≠ 0` かつ `m = v`
  現在の候補と入力が等しい場合、候補を変更せずカウンタを 1 増やす
  `c := c + 1`
-/
theorem LoopInv.step_same
  (pref : List α) (m v : α) (c : Nat)
  (hInv : LoopInv pref m c)
  (_ : c ≠ 0) (hmv : m = v) :
  LoopInv (pref ++ [v]) m (c + 1) := by
  subst v
  rcases hInv with ⟨hcount, hm, hother⟩
  unfold LoopInv
  constructor
  · grind
  · constructor
    · grind
    · intro a ha
      have hne : m ≠ a := by grind
      have hle := hother a ha
      grind

/-- Case 3: `c ≠ 0` かつ `m ≠ v`
  現在の候補と入力が異なる場合、候補を変更せずカウンタを 1 減らす
  `c := c - 1`
-/
theorem LoopInv.step_diff
  (pref : List α) (m v : α) (c : Nat)
  (hInv : LoopInv pref m c)
  (hc : c ≠ 0) (hmv : m ≠ v) :
  LoopInv (pref ++ [v]) m (c - 1) := by
  rcases hInv with ⟨hcount, hm, hother⟩
  have hcpos : 0 < c := by grind
  have hvm : v ≠ m := by grind
  unfold LoopInv
  constructor
  · grind
  · constructor
    · grind
    · intro a ha
      by_cases hva : v = a
      · subst a
        have hvbound := hother v hvm
        grind
      · have habound := hother a ha
        grind


end BoyerMoore.Checked
