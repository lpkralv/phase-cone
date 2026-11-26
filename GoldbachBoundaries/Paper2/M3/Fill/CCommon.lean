import GoldbachBoundaries.Paper2.M3.Real

/-!
# Filler group C (limits and the residue at 2): shared helpers
-/

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
namespace GoldbachBoundaries.Paper2.M3
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- `Γ` is analytic on `Re z > 0`. -/
theorem cc_analyticAt_Gamma {z : ℂ} (hz : 0 < z.re) : AnalyticAt ℂ Gamma z := by
  have hd : DifferentiableOn ℂ Gamma (halfPlane 0) := fun w hw =>
    (Complex.differentiableAt_Gamma w fun m h => by
      have := congrArg Complex.re h
      have hw' : 0 < w.re := hw
      simp at this; linarith [(m : ℕ).cast_nonneg (α := ℝ)]).differentiableWithinAt
  exact hd.analyticAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz)

end GoldbachBoundaries.Paper2.M3
