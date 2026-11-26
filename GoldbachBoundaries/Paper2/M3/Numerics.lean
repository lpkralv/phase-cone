import GoldbachBoundaries.Paper2.M3.Zeros
import GoldbachBoundaries.Paper2.M3.Fill.eulerMascheroni_bounds
import GoldbachBoundaries.Paper2.M3.Fill.log_pi_bounds

/-!
# M3: the constant `16πeC₀²` of `nr:lem:A`

`C₀ = 1 + γ_E/2 - log(4π)/2 = 0.0230957…` and `16πeC₀² = 0.0728831…` (mpmath, 30 digits). The statement asks for
`0.0728 < 16πeC₀² < 0.0729`; the upper margin is `1.7·10⁻⁵`, which needs `C₀` to about `3·10⁻⁶`.

The numerical inputs are with `γ_E ∈ [0.577215, 0.577216]`, `log 2 ∈ (0.6931471803, 0.6931471808)`
(Mathlib's `Real.log_two_gt_d9`, `log_two_lt_d9`) and `log π ∈ (1.144726, 1.144735)` (true value `1.1447298858…`),
`C₀ ∈ (0.0230928, 0.0230978) ⊂ (0.02309, 0.023098)`; and with `π ∈ (3.141592, 3.141593)`, `e ∈ (2.7182818283,
2.7182818286)` (Mathlib's `d6`, `d9` bounds), `C₀ ∈ (0.02309, 0.023098)` gives `16πeC₀² ∈ (0.072847, 0.072898)`.
The lower bound `log π > 1.144726` is the tight one (margin `3.9·10⁻⁶`).

PNT+ proves `0.577215 ≤ γ_E ≤ 0.577216` (`EulerMascheroniBounds.lean`), but that file imports `IEANTN/LogTables`, which
imports LeanCert's `interval_decide` (whose certificate checks may use `native_decide`), and it is not built here; the
filler copies its argument instead (it needs only Mathlib's `log 2` bounds).
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M3

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-! ## Real lemmas -/

/-- `0.02309 < C₀ < 0.023098`. -/
theorem C0_bounds : (0.02309 : ℝ) < C0 ∧ C0 < 0.023098 := by
  obtain ⟨hγ1, hγ2⟩ := eulerMascheroni_bounds
  obtain ⟨hp1, hp2⟩ := log_pi_bounds
  have h2a := Real.log_two_gt_d9
  have h2b := Real.log_two_lt_d9
  have hlog : Real.log (4 * Real.pi) = 2 * Real.log 2 + Real.log Real.pi := by
    rw [Real.log_mul (by norm_num) Real.pi_ne_zero, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  unfold C0
  rw [hlog]
  constructor <;> linarith

/-- `0.0728 < 16πeC₀² < 0.0729`. -/
theorem const_bounds :
    0.0728 < 16 * Real.pi * Real.exp 1 * C0 ^ 2 ∧ 16 * Real.pi * Real.exp 1 * C0 ^ 2 < 0.0729 := by
  obtain ⟨hc1, hc2⟩ := C0_bounds
  have hp1 := Real.pi_gt_d6
  have hp2 := Real.pi_lt_d6
  have he1 := Real.exp_one_gt_d9
  have he2 := Real.exp_one_lt_d9
  have hc0 : (0 : ℝ) < C0 := by linarith
  constructor
  · calc (0.0728 : ℝ) < 16 * 3.141592 * 2.7182818283 * 0.02309 ^ 2 := by norm_num
      _ < 16 * Real.pi * Real.exp 1 * C0 ^ 2 := by gcongr
  · calc 16 * Real.pi * Real.exp 1 * C0 ^ 2 < 16 * 3.141593 * 2.7182818286 * 0.023098 ^ 2 := by gcongr
      _ < 0.0729 := by norm_num

end GoldbachBoundaries.Paper2.M3
