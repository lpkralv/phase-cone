import GoldbachBoundaries.Phi2.Fill.BCommon

/-! Filler B: `negLogDerivZeta_two_fifths` (`M2Explicit.lean`). The case `σ = 2/5` of `fillB_line_log_bound`
(RH: every zero is at distance `≥ 1/10` from the line; paper 2's `exists_sep_bound_nonneg` for `|y| ≥ 2`, continuity
on `|y| ≤ 2`). -/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics ComplexConjugate

namespace GoldbachBoundaries.Phi2Proof

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **`ψ` on the line `Re w = 2/5`** (RH, (Z2), (Z3)): no zero there, and `|ψ(2/5 + iy)| ≤ C log(|y| + 3)`.
Under RH every zero is at distance `≥ 1/10` from the line. The `ψ` part of `M5.Qleft_i`: `M5.exists_sep_bound_nonneg`
with `δ = 1/10` for `|y| ≥ 2`, and compactness (`M5.exists_bound_of_local`, `ζ(2/5 + iy) ≠ 0`) for `|y| ≤ 2`.
Size 60–120. -/
theorem negLogDerivZeta_two_fifths (hRH : RiemannHypothesis) (hZ2 : Z2) (hZ3 : Z3) :
    ∃ C : ℝ, ∀ y : ℝ, riemannZeta ((2 / 5 : ℝ) + y * I) ≠ 0 ∧
      ‖negLogDerivZeta ((2 / 5 : ℝ) + y * I)‖ ≤ C * Real.log (|y| + 3) := by
  obtain ⟨C, -, hC⟩ := fillB_line_log_bound hRH hZ2 hZ3 (σ := 2 / 5) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨C, hC⟩

end GoldbachBoundaries.Phi2Proof
