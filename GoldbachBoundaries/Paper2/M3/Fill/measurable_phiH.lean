import GoldbachBoundaries.Paper2.M3.Landau

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
namespace GoldbachBoundaries.Paper2.M3
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **`φ` is measurable** (unconditional). `phiH u = (Θ(e^{-u}) - e^u)²`, and `Θ` is continuous on `(0, ∞)`
(`TIdentity.Fw_continuousOn_and_le_exp`), `e^{-u} > 0`, so `phiH` is continuous on `ℝ` (`ContinuousOn.comp_continuous`)
hence measurable, and so is its restriction (`Measurable.comp measurable_subtype_coe`). Size: 30–60 lines. -/
theorem measurable_phiH : Measurable ((Ioi (0 : ℝ)).domRestrict phiH) := by
  have hc : Continuous phiH := by
    exact (TIdentity.continuousOn_hErr.comp_continuous
      (Real.continuous_exp.comp continuous_neg) (fun u => Real.exp_pos (-u))).pow 2
  exact hc.measurable.comp measurable_subtype_coe

end GoldbachBoundaries.Paper2.M3
