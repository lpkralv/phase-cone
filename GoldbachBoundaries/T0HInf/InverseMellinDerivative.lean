import GoldbachBoundaries.T0HInf.Defs

/-! Differentiating an absolutely convergent inverse Mellin integral on a fixed vertical line. -/
noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
namespace GoldbachBoundaries.T0HInf
open GoldbachBoundaries Paper2

lemma real_cpow_derivative {x : ℝ} (hx : 0 < x) (z : ℂ) :
    HasDerivAt (fun t : ℝ => (t : ℂ) ^ z) (z * (x : ℂ) ^ (z - 1)) x := by
  by_cases hz : z = 0
  · subst z
    simpa using hasDerivAt_const x (1 : ℂ)
  · exact hasDerivAt_ofReal_cpow_const hx.ne' hz

lemma integrable_inverse_kernel {σ x : ℝ} (hx : 0 < x) {f : ℂ → ℂ}
    (hf : Integrable (fun y : ℝ => f (σ + y * I))) :
    Integrable (fun y : ℝ => (x : ℂ) ^ (-(σ + y * I)) * f (σ + y * I)) := by
  refine (hf.norm.const_mul (x ^ (-σ))).mono' ?_ (Eventually.of_forall fun y => ?_)
  · have hc : Continuous (fun y : ℝ => (x : ℂ) ^ (-((σ : ℂ) + y * I))) :=
      Continuous.const_cpow (by fun_prop) (Or.inl (ofReal_ne_zero.mpr hx.ne'))
    exact hc.aestronglyMeasurable.mul hf.aestronglyMeasurable
  · rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx]
    simp

lemma hasDerivAt_inverse_integral {σ x : ℝ} (hx : 0 < x) {f : ℂ → ℂ}
    (hf : Integrable (fun y : ℝ => f (σ + y * I)))
    (hzf : Integrable (fun y : ℝ => (σ + y * I) * f (σ + y * I))) :
    HasDerivAt (fun t : ℝ => ∫ y : ℝ, (t : ℂ) ^ (-(σ + y * I)) * f (σ + y * I))
      (∫ y : ℝ, (-(σ + y * I)) * (x : ℂ) ^ (-(σ + y * I) - 1) * f (σ + y * I)) x := by
  let J : Set ℝ := Icc (x / 2) (2 * x)
  have hJ : J ∈ 𝓝 x := Icc_mem_nhds (by linarith) (by linarith)
  have hpos (t : ℝ) (ht : t ∈ J) : 0 < t := by have := ht.1; dsimp [J] at *; linarith
  have hc : ContinuousOn (fun t : ℝ => t ^ (-σ - 1)) J := by
    apply continuousOn_of_forall_continuousAt
    intro t ht
    exact Real.continuousAt_rpow_const _ _ (Or.inl (hpos t ht).ne')
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  have hD : ∀ t ∈ J, ∀ y : ℝ,
      HasDerivAt (fun t : ℝ => (t : ℂ) ^ (-(σ + y * I)) * f (σ + y * I))
        (-(σ + y * I) * (t : ℂ) ^ (-(σ + y * I) - 1) * f (σ + y * I)) t := by
    intro t ht y
    exact (real_cpow_derivative (hpos t ht) _).mul_const _
  have hmeas : ∀ᶠ t : ℝ in 𝓝 x, AEStronglyMeasurable
      (fun y : ℝ => (t : ℂ) ^ (-(σ + y * I)) * f (σ + y * I)) volume := by
    filter_upwards [Ioi_mem_nhds hx] with t ht
    exact (integrable_inverse_kernel ht hf).aestronglyMeasurable
  have hmeas' : AEStronglyMeasurable (fun y : ℝ =>
      -(σ + y * I) * (x : ℂ) ^ (-(σ + y * I) - 1) * f (σ + y * I)) volume := by
    have hp : Continuous (fun y : ℝ => (x : ℂ) ^ (-((σ : ℂ) + y * I) - 1)) :=
      Continuous.const_cpow (by fun_prop) (Or.inl (ofReal_ne_zero.mpr hx.ne'))
    convert! hp.aestronglyMeasurable.mul hzf.aestronglyMeasurable.neg using 1
    ext y
    simp only [Pi.neg_apply, Pi.mul_apply]
    ring
  have hbound : ∀ᵐ y : ℝ, ∀ t ∈ J,
      ‖-(σ + y * I) * (t : ℂ) ^ (-(σ + y * I) - 1) * f (σ + y * I)‖ ≤
        |K| * ‖(σ + y * I) * f (σ + y * I)‖ := by
    filter_upwards [] with y t ht
    have hb : t ^ (-σ - 1) ≤ |K| := by
      have hh := hK t ht
      rw [Real.norm_eq_abs] at hh
      exact (le_abs_self _).trans (hh.trans (le_abs_self _))
    calc
      _ = t ^ (-σ - 1) * ‖(σ + y * I) * f (σ + y * I)‖ := by
        rw [show -(σ + y * I) * (t : ℂ) ^ (-(σ + y * I) - 1) * f (σ + y * I) =
          (t : ℂ) ^ (-(σ + y * I) - 1) * -((σ + y * I) * f (σ + y * I)) by ring,
          norm_mul, norm_neg, norm_cpow_eq_rpow_re_of_pos (hpos t ht)]
        simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hb (norm_nonneg _)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hJ hmeas
    (integrable_inverse_kernel hx hf) hmeas' hbound (hzf.norm.const_mul |K|)
    (Eventually.of_forall fun y t ht => hD t ht y)).2

lemma norm_inverse_vertical_le {σ x : ℝ} (hx : 0 < x) (f : ℂ → ℂ) :
    ‖VerticalIntegral' (fun z => (x : ℂ) ^ (-z) * f z) σ‖ ≤
      ((1 / (2 * Real.pi)) * ∫ y : ℝ, ‖f (σ + y * I)‖) * x ^ (-σ) := by
  have hn (y : ℝ) : ‖(x : ℂ) ^ (-(σ + y * I)) * f (σ + y * I)‖ =
      x ^ (-σ) * ‖f (σ + y * I)‖ := by
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx]
    simp
  have hI : ‖(1 / (2 * (Real.pi : ℂ) * I))‖ * ‖I‖ = 1 / (2 * Real.pi) := by
    simp [abs_of_pos Real.pi_pos]
  calc
    _ = (1 / (2 * Real.pi)) *
        ‖∫ y : ℝ, (x : ℂ) ^ (-(σ + y * I)) * f (σ + y * I)‖ := by
        simp only [VerticalIntegral', VerticalIntegral, norm_smul]
        rw [← mul_assoc, hI]
    _ ≤ (1 / (2 * Real.pi)) * ∫ y : ℝ, ‖(x : ℂ) ^ (-(σ + y * I)) * f (σ + y * I)‖ :=
        mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
    _ = _ := by rw [integral_congr_ae (Eventually.of_forall hn), integral_const_mul]; ring

end GoldbachBoundaries.T0HInf
