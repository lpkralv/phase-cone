import GoldbachBoundaries.Phi2.Fill.ACommon

/-! Filler A: `norm_hL_le` (M1). Proof in `Phi2/Fill/ACommon.lean` (`FillA.continuousOn_hL'`, `norm_hL_le'`, ports of `TIdentity.continuousOn_hErr`, `norm_hErr_le`). -/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics

namespace GoldbachBoundaries.Phi2Proof

open GoldbachBoundaries

/-- **`hL(t) = O(t^{-b})`** (RH), `1/2 < b < 1`, all `t > 0`, and `hL` is continuous on `(0, ∞)`.
Uses: `FL_eq_verticalIntegral'`, `verticalIntegral'_kernelL_shift`, `TIdentity.norm_verticalIntegral'_kernelQ_le` (G8e),
`TIdentity.integrable_Gamma_mul_Qcont_of_RH` (G8c) with `ψ`. Size 80–150. -/
theorem norm_hL_le (hRH : RiemannHypothesis) {b : ℝ} (hb : 1 / 2 < b) (hb1 : b < 1) :
    ContinuousOn hL (Ioi 0) ∧ ∃ C : ℝ, ∀ t : ℝ, 0 < t → |hL t| ≤ C * t ^ (-b) :=
  ⟨FillA.continuousOn_hL', FillA.norm_hL_le' hRH hb hb1⟩

end GoldbachBoundaries.Phi2Proof
