import GoldbachBoundaries.Paper2.M3.Landau
import GoldbachBoundaries.Paper2.M3.Fill.integrableOn_hErr_mul_cpow_of_mem

/-!
# Fill: shared helpers for filler group F

* `differentiableOn_integral_Ioc_cpow_of_integrable`: `s ↦ ∫_0^1 g(t) t^{s-1} dt` is holomorphic on `Re s > c` as
  soon as `g(t) t^{y-1}` is integrable on `(0, 1]` for every real `y > c` (no pointwise bound on `g`).
* `differentiableOn_m1_of_mem`: for `x ∈ mellinConvSet`, paper 1's `m₁` is holomorphic on `Re z > x/2`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M3

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- Holomorphy of `∫_0^1 g(t) t^{s-1} dt` on `Re s > c` from integrability of `g(t) t^{y-1}` for every real `y > c`. -/
theorem differentiableOn_integral_Ioc_cpow_of_integrable {g : ℝ → ℂ} {c : ℝ}
    (hg : AEStronglyMeasurable g (volume.restrict (Ioc (0 : ℝ) 1)))
    (hint : ∀ y : ℝ, c < y → IntegrableOn (fun t : ℝ => g t * (t : ℂ) ^ ((y : ℂ) - 1)) (Ioc (0 : ℝ) 1)) :
    DifferentiableOn ℂ (fun s : ℂ => ∫ t in Ioc (0 : ℝ) 1, g t * (t : ℂ) ^ (s - 1)) (halfPlane c) := by
  intro z₀ hz₀
  have hz₀' : c < z₀.re := hz₀
  set δ : ℝ := (z₀.re - c) / 3 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  set y : ℝ := z₀.re - 2 * δ with hy
  have hcy : c < y := by rw [hy, hδ]; linarith
  have hcont : ∀ s : ℂ, ContinuousOn (fun t : ℝ => (t : ℂ) ^ (s - 1)) (Ioc (0 : ℝ) 1) := by
    intro s t ht
    apply ContinuousAt.continuousWithinAt
    exact continuousAt_ofReal_cpow_const t (s - 1) (Or.inr ht.1.ne')
  have hmeas : ∀ s : ℂ, AEStronglyMeasurable (fun t : ℝ => g t * (t : ℂ) ^ (s - 1))
      (volume.restrict (Ioc (0 : ℝ) 1)) := fun s =>
    hg.mul ((hcont s).aestronglyMeasurable measurableSet_Ioc)
  let F' : ℂ → ℝ → ℂ := fun s t => g t * ((t : ℂ) ^ (s - 1) * Complex.log t)
  let bound : ℝ → ℝ := fun t => ‖g t * (t : ℂ) ^ ((y : ℂ) - 1)‖ * (1 / δ)
  have hnorm : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ s ∈ ball z₀ δ, ‖F' s t‖ ≤ bound t := by
    intro t ht s hs
    have ht0 : 0 < t := ht.1
    have hsre : y + δ < s.re := by
      have h1 : |(s - z₀).re| < δ :=
        lt_of_le_of_lt (abs_re_le_norm _) (by rw [← dist_eq]; exact mem_ball.mp hs)
      rw [sub_re, abs_lt] at h1; rw [hy]; linarith
    simp only [F', bound, norm_mul, norm_cpow_eq_rpow_re_of_pos ht0]
    have hlog : ‖Complex.log (t : ℂ)‖ = |Real.log t| := by
      rw [← ofReal_log ht0.le, norm_real, Real.norm_eq_abs]
    rw [hlog]
    simp only [sub_re, one_re, ofReal_re]
    -- t^{Re s - 1} |log t| ≤ t^{y-1} (t^δ |log t|) ≤ t^{y-1}/δ
    have hpow : t ^ (s.re - 1) ≤ t ^ (y - 1) * t ^ δ := by
      rw [← Real.rpow_add ht0]
      exact Real.rpow_le_rpow_of_exponent_ge ht0 ht.2 (by linarith)
    have hlt : t ^ δ * |Real.log t| ≤ 1 / δ := by
      have := Real.abs_log_mul_self_rpow_lt t δ ht0 ht.2 hδpos
      rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg ht0.le _)] at this
      linarith
    have hgn : 0 ≤ ‖g t‖ := norm_nonneg _
    have hty : 0 ≤ t ^ (y - 1) := Real.rpow_nonneg ht0.le _
    calc ‖g t‖ * (t ^ (s.re - 1) * |Real.log t|)
        ≤ ‖g t‖ * ((t ^ (y - 1) * t ^ δ) * |Real.log t|) := by gcongr
      _ = ‖g t‖ * t ^ (y - 1) * (t ^ δ * |Real.log t|) := by ring
      _ ≤ ‖g t‖ * t ^ (y - 1) * (1 / δ) := by gcongr
  have hderiv : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ s ∈ ball z₀ δ,
      HasDerivAt (fun s => g t * (t : ℂ) ^ (s - 1)) (F' s t) s := by
    intro t ht s _
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.1.ne'
    have h := ((hasDerivAt_id s).sub_const 1).const_cpow (c := (t : ℂ)) (Or.inl ht0)
    simpa [F', mul_comm, mul_assoc, mul_left_comm] using h.const_mul (g t)
  have hres := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioc (0 : ℝ) 1))
    (F := fun s t => g t * (t : ℂ) ^ (s - 1)) (F' := F') (x₀ := z₀) (bound := bound)
    (ball_mem_nhds z₀ hδpos) (Eventually.of_forall fun s => hmeas s) ?_ ?_
    (ae_restrict_of_forall_mem measurableSet_Ioc hnorm) ?_
    (ae_restrict_of_forall_mem measurableSet_Ioc hderiv)
  · exact hres.2.differentiableAt.differentiableWithinAt
  · -- integrability at `z₀` from integrability at `y < Re z₀`
    refine Integrable.mono' ((hint y hcy).norm) (hmeas z₀) ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_
    have ht0 : 0 < t := ht.1
    simp only [norm_mul, norm_cpow_eq_rpow_re_of_pos ht0, sub_re, one_re, ofReal_re]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge ht0 ht.2 (by rw [hy]; linarith))
      (norm_nonneg _)
  · refine hg.mul (((hcont z₀).mul ?_).aestronglyMeasurable measurableSet_Ioc)
    intro t ht
    exact ((continuous_ofReal.continuousAt).clog (ofReal_mem_slitPlane.mpr ht.1)).continuousWithinAt
  · exact (hint y hcy).norm.mul_const _

/-- For `x ∈ mellinConvSet`, `m₁(z) = ∫_0^1 h(t) t^{z-1} dt` is holomorphic on `Re z > x/2`. -/
theorem differentiableOn_m1_of_mem {x : ℝ} (hx : x ∈ mellinConvSet) :
    DifferentiableOn ℂ TIdentity.m1 (halfPlane (x / 2)) := by
  have hg : AEStronglyMeasurable (fun t : ℝ => ((hErr t : ℝ) : ℂ)) (volume.restrict (Ioc (0 : ℝ) 1)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
    exact continuous_ofReal.comp_continuousOn (TIdentity.continuousOn_hErr.mono Ioc_subset_Ioi_self)
  have := differentiableOn_integral_Ioc_cpow_of_integrable hg (c := x / 2) fun y hy =>
    integrableOn_hErr_mul_cpow_of_mem hx (z := (y : ℂ)) (by simpa using hy)
  exact this

/-- `Γ` is analytic on `Re z > 0`. -/
theorem analyticAt_Gamma_of_re_pos_F {z : ℂ} (hz : 0 < z.re) : AnalyticAt ℂ Gamma z := by
  have hd : DifferentiableOn ℂ Gamma (halfPlane 0) := fun w hw =>
    (Complex.differentiableAt_Gamma w fun m h => by
      have : (0 : ℝ) < w.re := hw
      rw [h] at this; simp at this; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]).differentiableWithinAt
  exact hd.analyticAt ((isOpen_lt continuous_const continuous_re).mem_nhds hz)

end GoldbachBoundaries.Paper2.M3
