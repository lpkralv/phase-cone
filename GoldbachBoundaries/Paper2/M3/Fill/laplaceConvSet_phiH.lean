import GoldbachBoundaries.Paper2.M3.Fill.D2Common

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
namespace GoldbachBoundaries.Paper2.M3
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **The convergence sets agree** (unconditional). The substitution `t = e^{-u}` maps `(0, ∞)` onto `(0, 1)` with
`dt = e^{-u} du`, so `∫_0^1 h(t)² t^{x-1} dt = ∫_0^∞ h(e^{-u})² e^{-xu} du` as integrability statements
(`MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul` with `f = fun u => exp (-u)`, injective on
`Ioi 0` with derivative `-e^{-u}`; `Ioc 0 1` and `Ioo 0 1` differ by a null set). Size: 100–200 lines. -/
theorem laplaceConvSet_phiH : laplaceConvSet phiH = mellinConvSet := by
  ext x
  change IntegrableOn (fun u : ℝ => phiH u * Real.exp (-(x * u))) (Ioi (0 : ℝ)) ↔
    IntegrableOn (fun t : ℝ => hErr t ^ 2 * t ^ (x - 1)) (Ioc (0 : ℝ) 1)
  rw [integrableOn_Ioc_iff_integrableOn_Ioo, ← d2_exp_neg_image,
    integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
      (fun u _ => d2_exp_neg_deriv u) d2_exp_neg_inj]
  simp only [smul_eq_mul, d2_real_jacobian]

end GoldbachBoundaries.Paper2.M3
