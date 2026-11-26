import GoldbachBoundaries.Paper2.M3.Landau
import Mathlib.MeasureTheory.Function.L2Space

set_option backward.isDefEq.respectTransparency false

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
namespace GoldbachBoundaries.Paper2.M3
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **Step 3, convergence of `N(z)`** (unconditional). Cauchy-Schwarz on `(0, 1]`:
`|h(t)| t^{Re z - 1} = (|h(t)| t^{(x-1)/2}) · t^{Re z - 1 - (x-1)/2}`, the first factor in `L²` (`x ∈ mellinConvSet`),
the second in `L²` because `t^{2 Re z - x - 1}` is integrable on `(0, 1]` (`2 Re z - x > 0`). `MemLp.integrable_mul`
with exponents `2, 2`; measurability from `TIdentity.continuousOn_hErr`; `‖(t : ℂ)^{z-1}‖ = t^{Re z - 1}`.
Size: 100–200 lines. -/
theorem integrableOn_hErr_mul_cpow_of_mem {x : ℝ} (hx : x ∈ mellinConvSet) {z : ℂ} (hz : x / 2 < z.re) :
    IntegrableOn (fun t : ℝ => (hErr t : ℂ) * (t : ℂ) ^ (z - 1)) (Ioc (0 : ℝ) 1) := by
  let a : ℝ := (x - 1) / 2
  let b : ℝ := z.re - 1 - a
  have hc : ContinuousOn hErr (Ioc (0 : ℝ) 1) :=
    TIdentity.continuousOn_hErr.mono Ioc_subset_Ioi_self
  have hp (r : ℝ) : ContinuousOn (fun t : ℝ => t ^ r) (Ioc (0 : ℝ) 1) :=
    continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt ht.1))
  have hf : MemLp (fun t : ℝ => hErr t * t ^ a) 2 (volume.restrict (Ioc (0 : ℝ) 1)) := by
    apply (memLp_two_iff_integrable_sq ((hc.mul (hp a)).aestronglyMeasurable measurableSet_Ioc)).2
    refine (show IntegrableOn (fun t : ℝ => hErr t ^ 2 * t ^ (x - 1)) (Ioc (0 : ℝ) 1) volume from hx).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    change hErr t ^ 2 * t ^ (x - 1) = (hErr t * t ^ a) ^ 2
    rw [mul_pow, ← Real.rpow_natCast (t ^ a) 2, ← Real.rpow_mul ht.1.le]
    dsimp [a]
    congr 2
    ring
  have hg : MemLp (fun t : ℝ => t ^ b) 2 (volume.restrict (Ioc (0 : ℝ) 1)) := by
    apply (memLp_two_iff_integrable_sq ((hp b).aestronglyMeasurable measurableSet_Ioc)).2
    have hi : IntegrableOn (fun t : ℝ => t ^ (b * 2)) (Ioc (0 : ℝ) 1) := by
      rw [integrableOn_Ioc_iff_integrableOn_Ioo]
      apply (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2
      dsimp [b, a]
      linarith
    refine hi.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [← Real.rpow_natCast (t ^ b) 2, ← Real.rpow_mul ht.1.le]
    norm_num
  have hi := hf.integrable_mul hg
  have hm : AEStronglyMeasurable (fun t : ℝ => (hErr t : ℂ) * (t : ℂ) ^ (z - 1))
      (volume.restrict (Ioc (0 : ℝ) 1)) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioc
    refine (Complex.continuous_ofReal.comp_continuousOn hc).mul ?_
    intro t ht
    exact (Complex.continuousAt_ofReal_cpow_const t (z - 1)
      (Or.inr (ne_of_gt ht.1))).continuousWithinAt
  apply (integrable_norm_iff hm).1
  refine hi.norm.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  simp only [Pi.mul_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_cpow_eq_rpow_re_of_pos ht.1, sub_re, one_re]
  rw [abs_of_pos (Real.rpow_pos_of_pos ht.1 a), abs_of_pos (Real.rpow_pos_of_pos ht.1 b),
    mul_assoc, ← Real.rpow_add ht.1]
  congr 2
  dsimp [b]
  ring

end GoldbachBoundaries.Paper2.M3
