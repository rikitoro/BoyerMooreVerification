# BoyerMooreVerification

Boyer-Moore majority vote algorithm の健全性についての Lean による検証


Boyer-Moore majority vote algorithm :
```lean
-- BMModel/Algorithm.lean

def BoyerMoore.majorityCandidate {α : Type} [Inhabited α] [DecidableEq α]
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
```

検証対象(課題) :
```lean
-- BMChallenge/Verification.lean

theorem candidate_correct
  {α : Type} [Inhabited α] [DecidableEq α]
  (xs : List α) (a : α)
  (h : BoyerMoore.IsMajority a xs) :
  BoyerMoore.majorityCandidate xs = a := by
  sorry
```
## comparator によるチェック方法

```
# モデル・課題をビルド
lake build SCPChallenge

# 課題と解答を比較
lake comparator

# 外部チェッカーも含めて検査
lake comparator --paranoid

# 証明ライブラリ全体を検証
lake check --paranoid
```

## References
1. えびまラボ, 候補者100億人の選挙で過半数得票者を見つける方法【ゆっくり解説】, YouTube, [Link](https://www.youtube.com/watch?v=DTWLKMwolAY) 
2. Boyer, R.S., Moore, J.S. (1991). MJRTY—A Fast Majority Vote Algorithm. In: Boyer, R.S. (eds) Automated Reasoning. Automated Reasoning Series, vol 1. Springer, Dordrecht. https://doi.org/10.1007/978-94-011-3488-0_5