import GoldbachBoundaries.Paper2.M3.Fill.LandauCommon

/-! Fill of `integrableOn_laplace_of_lt` (Paper2/M3/Landau.lean): domination by `φ(u)e^{-xu}`
(`LandauFill.integrableOn_lapI` with `n = 0`). -/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M3

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **Absolute convergence right of the abscissa** (general). With `x ∈ S`, `x < Re s`:
`‖φ(u)e^{-su}‖ = φ(u)e^{-(Re s)u} ≤ φ(u)e^{-xu}` on `u > 0` (`hφ0`, `Complex.norm_exp`), and the integrand is
`AEStronglyMeasurable` on `Ioi 0` (from `hφm`: `Measurable.comp` with the subtype, e.g.
`(measurableEmbedding_subtype_coe measurableSet_Ioi).measurable_extend` or `Measurable.of_comap_le` style; `exp` is
continuous). `Integrable.mono'`. Size: 60–120 lines. -/
theorem integrableOn_laplace_of_lt (φ : ℝ → ℝ) (hφm : Measurable ((Ioi (0 : ℝ)).domRestrict φ))
    (hφ0 : ∀ u, 0 < u → 0 ≤ φ u) {s : ℂ} (hs : ∃ x ∈ laplaceConvSet φ, x < s.re) :
    IntegrableOn (fun u : ℝ => (φ u : ℂ) * exp (-(s * u))) (Ioi (0 : ℝ)) := by
  obtain ⟨x, hx, hxs⟩ := hs
  refine (LandauFill.integrableOn_lapI hφ0 hx hxs 0).congr_fun (fun u _ => ?_) measurableSet_Ioi
  show ((-(u : ℂ)) ^ 0 * (φ u : ℂ)) * exp (-(s * u)) = _
  simp

end GoldbachBoundaries.Paper2.M3
