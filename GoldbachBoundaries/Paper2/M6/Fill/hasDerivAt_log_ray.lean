import GoldbachBoundaries.Paper2.M6.Defs

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M6

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **The logarithm cut along the ray** (general). For `z` off `a + [0, ∞)e^{iθ}`, `w = (z - a)/(-e^{iθ})` lies in the
slit plane: if `w = -u` with `u ≥ 0` real then `z = a + u e^{iθ}`. So `Complex.hasDerivAt_log` applies, and by the
chain rule the derivative is `(1/(-e^{iθ})) / ((z - a)/(-e^{iθ})) = 1/(z - a)`. -/
theorem hasDerivAt_log_ray {a z : ℂ} {θ : ℝ} (hz : z ∉ rayFrom a θ) :
    HasDerivAt (fun z => Complex.log ((z - a) / (-exp (θ * I)))) (1 / (z - a)) z := by
  set c : ℂ := -exp (θ * I) with hc
  have hc0 : c ≠ 0 := neg_ne_zero.mpr (exp_ne_zero _)
  have hza : z - a ≠ 0 := by
    intro h
    exact hz ⟨0, le_rfl, by simp [sub_eq_zero.mp h]⟩
  have hslit : (z - a) / c ∈ slitPlane := by
    rw [mem_slitPlane_iff]
    by_contra hcon
    push Not at hcon
    obtain ⟨hre, him⟩ := hcon
    apply hz
    refine ⟨-((z - a) / c).re, by linarith, ?_⟩
    have hw : (z - a) / c = (((z - a) / c).re : ℂ) := by
      apply Complex.ext <;> simp [him]
    have : z - a = (((z - a) / c).re : ℂ) * c := by
      rw [← hw]; field_simp
    rw [hc] at this
    push_cast
    linear_combination this
  have h1 : HasDerivAt (fun z => (z - a) / c) (1 / c) z := by
    simpa using ((hasDerivAt_id z).sub_const a).div_const c
  convert h1.clog hslit using 1
  field_simp

end GoldbachBoundaries.Paper2.M6
