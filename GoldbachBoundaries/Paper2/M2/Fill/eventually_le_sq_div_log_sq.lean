import GoldbachBoundaries.Paper2.M2.Fill.BCommon

/-! Filler group B: `eventually_le_sq_div_log_sq` (`Single.lean`). The proof is `eventually_le_sq_div_log_sqB` in `Fill/BCommon.lean`. -/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M2

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- `X²/log² X → ∞`. Size: 30–60 lines. -/
theorem eventually_le_sq_div_log_sq {c : ℝ} (hc : 0 < c) (N : ℝ) :
    ∀ᶠ X in atTop, N ≤ c / 2 * X ^ 2 / Real.log X ^ 2 :=
  eventually_le_sq_div_log_sqB hc N

end GoldbachBoundaries.Paper2.M2
