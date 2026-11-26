import GoldbachBoundaries.Paper2.M3.Landau
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.L2Space

set_option backward.isDefEq.respectTransparency false

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
namespace GoldbachBoundaries.Paper2.M3
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

lemma d2_exp_neg_image : (fun u : ℝ => Real.exp (-u)) '' Ioi 0 = Ioo 0 1 := by
  ext t
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (neg_neg_of_pos hu)⟩
  · intro ht
    refine ⟨-Real.log t, neg_pos.mpr (Real.log_neg ht.1 ht.2), ?_⟩
    simp [Real.exp_log ht.1]

lemma d2_exp_neg_deriv (u : ℝ) :
    HasDerivWithinAt (fun u : ℝ => Real.exp (-u)) (-Real.exp (-u)) (Ioi 0) u := by
  exact mul_neg_one (Real.exp (-u)) ▸
    ((Real.hasDerivAt_exp (-u)).comp u (hasDerivAt_neg u)).hasDerivWithinAt

lemma d2_exp_neg_inj : InjOn (fun u : ℝ => Real.exp (-u)) (Ioi 0) := by
  intro u hu v hv huv
  exact neg_injective (Real.exp_injective huv)

lemma d2_real_jacobian (u x : ℝ) :
    |-Real.exp (-u)| * (hErr (Real.exp (-u)) ^ 2 * Real.exp (-u) ^ (x - 1)) =
      phiH u * Real.exp (-(x * u)) := by
  rw [abs_neg, abs_of_pos (Real.exp_pos _), Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  unfold phiH
  rw [mul_left_comm, ← Real.exp_add]
  congr 2
  ring

lemma d2_complex_jacobian (u : ℝ) (s : ℂ) :
    |-Real.exp (-u)| • (((hErr (Real.exp (-u)) ^ 2 : ℝ) : ℂ) *
      (Real.exp (-u) : ℂ) ^ (s - 1)) =
      (phiH u : ℂ) * exp (-(s * u)) := by
  rw [abs_neg, abs_of_pos (Real.exp_pos _)]
  change (Real.exp (-u) : ℂ) * _ = _
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))]
  rw [← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp]
  unfold phiH
  rw [Complex.ofReal_exp, mul_left_comm, ← Complex.exp_add]
  push_cast
  congr 2
  ring

end GoldbachBoundaries.Paper2.M3
