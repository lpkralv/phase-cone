import GoldbachBoundaries.Paper2.M3.Real

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
namespace GoldbachBoundaries.Paper2.M3
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **Complex integrability from real** (unconditional). `‖((h(t)² : ℝ) : ℂ) t^{s-1}‖ = h(t)² t^{Re s - 1}` for
`t > 0` (`Complex.norm_cpow_eq_rpow_re_of_pos`), so `Integrable.mono'` (or `integrable_norm_iff` after
`AEStronglyMeasurable` from continuity of `hErr` on `(0, 1]`, `TIdentity.continuousOn_hErr`). Size: 40–80 lines. -/
theorem integrableOn_hErr_sq_cpow_of_mem {s : ℂ} (hs : s.re ∈ mellinConvSet) :
    IntegrableOn (fun t : ℝ => ((hErr t ^ 2 : ℝ) : ℂ) * (t : ℂ) ^ (s - 1)) (Ioc (0 : ℝ) 1) := by
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => ((hErr t ^ 2 : ℝ) : ℂ) * (t : ℂ) ^ (s - 1))
      (volume.restrict (Ioc (0 : ℝ) 1)) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioc
    apply ContinuousOn.mul
    · exact Complex.continuous_ofReal.comp_continuousOn
        ((TIdentity.continuousOn_hErr.mono Ioc_subset_Ioi_self).pow 2)
    · exact continuousOn_of_forall_continuousAt fun t ht =>
        (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr ht.1.ne'))
  apply Integrable.mono' hs hmeas
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _),
    Complex.norm_cpow_eq_rpow_re_of_pos ht.1]
  simp only [sub_re, one_re]
  exact le_rfl

end GoldbachBoundaries.Paper2.M3
