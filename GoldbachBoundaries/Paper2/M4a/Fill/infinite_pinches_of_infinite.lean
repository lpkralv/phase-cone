import GoldbachBoundaries.Paper2.M4a.Defs

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
namespace GoldbachBoundaries.Paper2.M4a
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **Transfer through `L`** (general). On the line, `L(s₀) = 1 + i·Im L(s₀)` (`Re L(s₀) = 1`). The map
`u ↦ L⁻¹(1 + u) = (1 + u - ℓ₀)/ℓ` is injective, sends `u` to a point `α` with `L(α) - 1 = u`, and
`‖α - s₀‖ = ‖1 + u - L(s₀)‖/ℓ = ‖u - i·Im L(s₀)‖/ℓ < r`. So the image of the infinite set lies in the target set
(`Set.Infinite.image` with `InjOn`, then `Set.Infinite.mono`). Size: 60–120 lines. -/
theorem infinite_pinches_of_infinite (A : Aff) {s₀ : ℂ} (hs₀ : s₀ ∈ A.lineL) {r : ℝ} (hr : 0 < r) {S : Set ℂ}
    (hS : {u : ℂ | u ∈ S ∧ ‖u - (((A.app s₀).im : ℝ) : ℂ) * I‖ < A.ell * r}.Infinite) :
    {α : ℂ | A.app α - 1 ∈ S ∧ α ∈ ball s₀ r}.Infinite := by
  let f : ℂ → ℂ := fun u => (1 + u - (A.ell0 : ℂ)) / (A.ell : ℂ)
  have hl : (A.ell : ℂ) ≠ 0 := by exact_mod_cast A.ell_pos.ne'
  have hf (u : ℂ) : A.app (f u) = 1 + u := by
    dsimp [f, Aff.app]
    field_simp
    <;> ring
  have hi : Function.Injective f := by
    intro u v huv
    have := congrArg A.app huv
    simpa only [hf, add_right_inj] using this
  refine (hS.image hi.injOn).mono ?_
  rintro α ⟨u, ⟨hu, hd⟩, rfl⟩
  refine ⟨by simpa only [hf, add_sub_cancel_left] using hu, ?_⟩
  rw [mem_ball, dist_eq_norm]
  have heq : f u - s₀ = (u - (((A.app s₀).im : ℝ) : ℂ) * I) / (A.ell : ℂ) := by
    have hline : A.app s₀ = 1 + (((A.app s₀).im : ℝ) : ℂ) * I := by
      apply Complex.ext
      · simpa [Aff.lineL] using hs₀
      · simp
    have hfu := hf u
    change (A.ell : ℂ) * f u + (A.ell0 : ℂ) = 1 + u at hfu
    change (A.ell : ℂ) * s₀ + (A.ell0 : ℂ) = 1 + (((A.app s₀).im : ℝ) : ℂ) * I at hline
    apply (eq_div_iff hl).mpr
    linear_combination hfu - hline
  rw [heq, norm_div]
  have hnorm : ‖(A.ell : ℂ)‖ = A.ell := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos A.ell_pos]
  rw [hnorm]
  exact (div_lt_iff₀ A.ell_pos).mpr (by simpa [mul_comm] using hd)

end GoldbachBoundaries.Paper2.M4a
