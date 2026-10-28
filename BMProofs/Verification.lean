import BMModel.Algorithm
import BMProofs.InvariantLemmas

import Std.WP
import Std.Tactic.Do

open Std.WP Lean.Order

set_option experimental.vcgen true

namespace BoyerMoore.Checked

/-! # Verification of Boyer-Moore majority vote
  `vcgen` を用いて命令型プログラム `BoyerMoore.majorityCandidate` を直接検証する

  ループ不変条件:
    `LoopInv`
  不変条件の初期化:
    `LoopInv.init`
  不変条件の保存:
    `LoopInv.step_zero`, `LoopInv.step_same`, `LoopInv.step_diff`
  終了時の正しさ:
    `LoopInv.result`
-/
theorem candidate_correct
  {α : Type} [Inhabited α] [DecidableEq α]
  (xs : List α) (a : α)
  (h : BoyerMoore.IsMajority a xs) :
  BoyerMoore.majorityCandidate xs = a := by
  generalize heq : BoyerMoore.majorityCandidate xs = r
  apply Id.of_run_eq_wp heq
  -- 検証条件の生成
  vcgen
  -- 不変条件を指定
  case inv1 =>
    exact fun pref _ state =>
      LoopInv pref state.fst state.snd
  all_goals sorry

end BoyerMoore.Checked
