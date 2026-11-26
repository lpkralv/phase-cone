import GoldbachBoundaries.Phi2.Fill.ACommon

/-! Filler A: `FL_basic` (M1). Proof in `Phi2/Fill/ACommon.lean` (a port of `TIdentity.Fw_continuousOn_and_le_exp`, `Fw_nonneg`). -/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics

namespace GoldbachBoundaries.Phi2Proof

open GoldbachBoundaries

/-- `FL` is continuous on `(0, ∞)` and `FL t ≤ C e^{-t}` for `t ≥ 1`; `0 ≤ FL t`.
Uses: `TIdentity.Fw_continuousOn_and_le_exp` (G9a), `TIdentity.Fw_nonneg`. Size 60–120. -/
theorem FL_basic :
    ContinuousOn FL (Ioi 0) ∧ (∃ C : ℝ, ∀ t : ℝ, 1 ≤ t → FL t ≤ C * Real.exp (-t)) ∧ ∀ t, 0 ≤ FL t :=
  ⟨FillA.FL_continuousOn_and_le_exp.1, FillA.FL_continuousOn_and_le_exp.2, FillA.FL_nonneg'⟩

end GoldbachBoundaries.Phi2Proof
