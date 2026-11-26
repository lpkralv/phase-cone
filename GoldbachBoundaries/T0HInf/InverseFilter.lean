import GoldbachBoundaries.T0HInf.InverseMellinDerivative

/-! Apply the Euler filter `1 + x d/dx` inside an absolutely convergent inverse Mellin integral. -/
noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
namespace GoldbachBoundaries.T0HInf
open GoldbachBoundaries Paper2

lemma integrable_inverse_derivative {σ x : ℝ} (hx : 0 < x) {f : ℂ → ℂ}
    (hzf : Integrable (fun y : ℝ => (σ + y * I) * f (σ + y * I))) :
    Integrable (fun y : ℝ => -(σ + y * I) * (x : ℂ) ^ (-(σ + y * I) - 1) * f (σ + y * I)) := by
  have hi := (integrable_inverse_kernel (σ := σ) (f := fun z => z * f z) hx hzf).const_mul (-(x : ℂ)⁻¹)
  apply hi.congr
  filter_upwards [] with y
  rw [cpow_sub _ _ (ofReal_ne_zero.mpr hx.ne'), cpow_one]
  ring

lemma hasDerivAt_inverse_vertical {σ x : ℝ} (hx : 0 < x) {f : ℂ → ℂ}
    (hf : Integrable (fun y : ℝ => f (σ + y * I)))
    (hzf : Integrable (fun y : ℝ => (σ + y * I) * f (σ + y * I))) :
    HasDerivAt (fun t : ℝ => VerticalIntegral' (fun z => (t : ℂ) ^ (-z) * f z) σ)
      (VerticalIntegral' (fun z => -z * (x : ℂ) ^ (-z - 1) * f z) σ) x := by
  have h := hasDerivAt_inverse_integral hx hf hzf
  simpa only [VerticalIntegral', VerticalIntegral, smul_eq_mul] using
    (h.const_mul I).const_mul (1 / (2 * Real.pi * I))

lemma filter_inverse_vertical {σ x : ℝ} (hx : 0 < x) {f : ℂ → ℂ}
    (hf : Integrable (fun y : ℝ => f (σ + y * I)))
    (hzf : Integrable (fun y : ℝ => (σ + y * I) * f (σ + y * I))) :
    VerticalIntegral' (fun z => (x : ℂ) ^ (-z) * f z) σ +
      (x : ℂ) * VerticalIntegral' (fun z => -z * (x : ℂ) ^ (-z - 1) * f z) σ =
        VerticalIntegral' (fun z => (x : ℂ) ^ (-z) * ((1 - z) * f z)) σ := by
  have hi := integrable_inverse_kernel hx hf
  have hd := integrable_inverse_derivative hx hzf
  have he : (fun y : ℝ => (x : ℂ) ^ (-(σ + y * I)) * ((1 - (σ + y * I)) * f (σ + y * I))) =
      fun y : ℝ => (x : ℂ) ^ (-(σ + y * I)) * f (σ + y * I) +
        (x : ℂ) * (-(σ + y * I) * (x : ℂ) ^ (-(σ + y * I) - 1) * f (σ + y * I)) := by
    ext y
    rw [cpow_sub _ _ (ofReal_ne_zero.mpr hx.ne'), cpow_one]
    field_simp [ofReal_ne_zero.mpr hx.ne']
    <;> ring
  simp only [VerticalIntegral', VerticalIntegral, smul_eq_mul]
  rw [he, integral_add hi (hd.const_mul _), integral_const_mul]
  ring

end GoldbachBoundaries.T0HInf
