import GoldbachBoundaries.Paper2.M6.Defs

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M6

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **Equal derivatives near a point give a constant difference near it** (general). On a ball `B` about `z₁` where
both derivative statements hold, `f` and `g` are differentiable with equal derivatives, so `f = g + C` on the
connected open `B` (`IsOpen.exists_eq_add_of_deriv_eq`). -/
theorem eventuallyEq_add_const_of_hasDerivAt {f g φ : ℂ → ℂ} {z₁ : ℂ}
    (h : ∀ᶠ z in 𝓝 z₁, HasDerivAt f (φ z) z ∧ HasDerivAt g (φ z) z) :
    ∃ C : ℂ, f =ᶠ[𝓝 z₁] fun z => g z + C := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp h
  obtain ⟨C, hC⟩ := isOpen_ball.exists_eq_add_of_deriv_eq (convex_ball z₁ ε).isPreconnected
    (fun z hz => (hball z hz).1.differentiableAt.differentiableWithinAt)
    (fun z hz => (hball z hz).2.differentiableAt.differentiableWithinAt)
    (fun z hz => by rw [(hball z hz).1.deriv, (hball z hz).2.deriv])
  exact ⟨C, Filter.eventuallyEq_of_mem (ball_mem_nhds z₁ hε) hC⟩

end GoldbachBoundaries.Paper2.M6
