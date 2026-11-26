import GoldbachBoundaries.Paper2.M3.Zeros

/-!
# Fill: `log_pi_bounds` (`1.144726 < log π < 1.144735`)

`exp(1.144726) = e · exp(0.144726)` and `exp(1.144735) = e · exp(0.144735)`. Mathlib's `Real.exp_one_gt_d9`,
`Real.exp_one_lt_d9` bound `e`, and `Real.exp_bound` (Taylor polynomial of degree 5 with remainder) bounds the second
factor. Then `exp(1.144726) < 3.1415806 < 3.141592 < π` and `π < 3.141593 < 3.1416088 < exp(1.144735)`
(`Real.pi_gt_d6`, `Real.pi_lt_d6`).
-/

namespace GoldbachBoundaries.Paper2.M3

/-- Taylor bracket for `exp x`, `|x| ≤ 1`, from `Real.exp_bound` with six terms. -/
private lemma exp_taylor6 {x : ℝ} (hx : |x| ≤ 1) :
    |Real.exp x - (1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + x ^ 5 / 120)| ≤
      |x| ^ 6 * (7 / (720 * 6)) := by
  have h := Real.exp_bound hx (n := 6) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [Nat.factorial] at h ⊢
  convert h using 2

/-- **`log π` to `5·10⁻⁶`** (real analysis). `log π > 1.144726`: `π > 3.141592` (`Real.pi_gt_d6`) and
`exp(1.144726) < 3.141592` (true: `exp(1.144726) = 3.1415805…`); `log π < 1.144735`: `π < 3.141593` and
`3.141593 < exp(1.144735)` (`= 3.1416088…`). The two `exp` bounds: Mathlib's `Real.exp_bound`/`Real.exp_approx`
machinery (as in `Real.exp_one_near_10`), or write `1.144726 = log 3 + x` style with `Real.abs_log_sub_add_sum_range_le`
(the series of `log(1 - y)`) for `log(3.141592/3)`, `log 3 = log 2 + log(3/2)`, as Mathlib does for
`Real.log_two_near_10`. Size: 150–300 lines. -/
theorem log_pi_bounds : (1.144726 : ℝ) < Real.log Real.pi ∧ Real.log Real.pi < 1.144735 := by
  have he1 := Real.exp_one_gt_d9
  have he2 := Real.exp_one_lt_d9
  have hp1 := Real.pi_gt_d6
  have hp2 := Real.pi_lt_d6
  constructor
  · rw [Real.lt_log_iff_exp_lt Real.pi_pos]
    have hsplit : Real.exp 1.144726 = Real.exp 1 * Real.exp 0.144726 := by
      rw [← Real.exp_add]; norm_num
    have ht := exp_taylor6 (x := 0.144726) (by rw [abs_of_pos (by norm_num)]; norm_num)
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 0.144726)] at ht
    have hub : Real.exp 0.144726 ≤ (1 + 0.144726 + 0.144726 ^ 2 / 2 + 0.144726 ^ 3 / 6 + 0.144726 ^ 4 / 24
        + 0.144726 ^ 5 / 120) + 0.144726 ^ 6 * (7 / (720 * 6)) := by
      linarith [le_abs_self (Real.exp 0.144726 - (1 + 0.144726 + 0.144726 ^ 2 / 2 + 0.144726 ^ 3 / 6
        + 0.144726 ^ 4 / 24 + 0.144726 ^ 5 / 120))]
    rw [hsplit]
    calc Real.exp 1 * Real.exp 0.144726
        ≤ 2.7182818286 * ((1 + 0.144726 + 0.144726 ^ 2 / 2 + 0.144726 ^ 3 / 6 + 0.144726 ^ 4 / 24
          + 0.144726 ^ 5 / 120) + 0.144726 ^ 6 * (7 / (720 * 6))) := by
          gcongr
      _ < 3.141592 := by norm_num
      _ < Real.pi := hp1
  · rw [Real.log_lt_iff_lt_exp Real.pi_pos]
    have hsplit : Real.exp 1.144735 = Real.exp 1 * Real.exp 0.144735 := by
      rw [← Real.exp_add]; norm_num
    have ht := exp_taylor6 (x := 0.144735) (by rw [abs_of_pos (by norm_num)]; norm_num)
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 0.144735)] at ht
    have hlb : (1 + 0.144735 + 0.144735 ^ 2 / 2 + 0.144735 ^ 3 / 6 + 0.144735 ^ 4 / 24
        + 0.144735 ^ 5 / 120) - 0.144735 ^ 6 * (7 / (720 * 6)) ≤ Real.exp 0.144735 := by
      linarith [neg_abs_le (Real.exp 0.144735 - (1 + 0.144735 + 0.144735 ^ 2 / 2 + 0.144735 ^ 3 / 6
        + 0.144735 ^ 4 / 24 + 0.144735 ^ 5 / 120))]
    rw [hsplit]
    calc Real.pi < 3.141593 := hp2
      _ < 2.7182818283 * ((1 + 0.144735 + 0.144735 ^ 2 / 2 + 0.144735 ^ 3 / 6 + 0.144735 ^ 4 / 24
          + 0.144735 ^ 5 / 120) - 0.144735 ^ 6 * (7 / (720 * 6))) := by norm_num
      _ ≤ Real.exp 1 * Real.exp 0.144735 := by gcongr

end GoldbachBoundaries.Paper2.M3
