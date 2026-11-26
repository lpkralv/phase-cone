import GoldbachBoundaries.Phi2.Fill.ACommon

/-! Filler A: `differentiable_e1L_E2L` (M1). Proof in `Phi2/Fill/ACommon.lean` (`FillA.differentiable_e1L'`, `differentiable_E2L'`, ports of `TIdentity.differentiable_e1`, `differentiable_E2`). -/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics

namespace GoldbachBoundaries.Phi2Proof

open GoldbachBoundaries

/-- `e₁` and `E₂` are entire. Uses: `TIdentity.differentiable_e1`, `differentiable_E2` (verbatim with `FL_basic`).
Size 30–60. -/
theorem differentiable_e1L_E2L : Differentiable ℂ e1L ∧ Differentiable ℂ E2L :=
  ⟨FillA.differentiable_e1L', FillA.differentiable_E2L'⟩

end GoldbachBoundaries.Phi2Proof
