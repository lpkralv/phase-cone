import GoldbachBoundaries.Paper2.M3.Fill.D2Common

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
namespace GoldbachBoundaries.Paper2.M3
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **`𝓛 = 𝓜`** (unconditional). The same substitution for the complex integrand
(`MeasureTheory.integral_image_eq_integral_abs_deriv_smul`): `((h(t)² : ℝ) : ℂ) t^{s-1}` at `t = e^{-u}` times
`e^{-u}` is `(phiH u : ℂ) e^{-su}` (`(e^{-u} : ℂ)^{s-1} = e^{-u(s-1)}`, `Complex.ofReal_cpow`, `Complex.exp_log`).
The hypothesis makes both integrals absolutely convergent (`integrableOn_hErr_sq_cpow_of_mem` after the up-set
property, or `integrableOn_laplace_of_lt` with `laplaceConvSet_phiH`); without it the identity is not claimed.
Size: 100–200 lines. -/
theorem laplace_phiH_eq_Mcal {s : ℂ} (hs : ∃ x ∈ mellinConvSet, x < s.re) : laplace phiH s = Mcal s := by
  have _ := hs
  unfold laplace Mcal
  rw [integral_Ioc_eq_integral_Ioo, ← d2_exp_neg_image,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
      (fun u _ => d2_exp_neg_deriv u) d2_exp_neg_inj]
  simp only [d2_complex_jacobian]

end GoldbachBoundaries.Paper2.M3
