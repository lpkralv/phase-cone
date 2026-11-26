import GoldbachBoundaries.Paper2.M6.Defs

/-!
# M6 group B: shared helpers (real proofs)

* `B_eventuallyEq_add_const`: equal derivatives near a point give a constant difference near it (the content of
  `eventuallyEq_add_const_of_hasDerivAt`, restated here so that `Branch.lean`'s fill need not import `Local.lean`).
* `B_exists_primitive_ball`: a function holomorphic on a ball has a primitive there (Mathlib's
  `DifferentiableOn.isExactOn_ball`).
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M6

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- Equal derivatives near `z₁` give `f = g + C` near `z₁` (`IsOpen.exists_eq_add_of_deriv_eq` on a ball). -/
theorem B_eventuallyEq_add_const {f g φ : ℂ → ℂ} {z₁ : ℂ}
    (h : ∀ᶠ z in 𝓝 z₁, HasDerivAt f (φ z) z ∧ HasDerivAt g (φ z) z) :
    ∃ C : ℂ, f =ᶠ[𝓝 z₁] fun z => g z + C := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp h
  obtain ⟨C, hC⟩ := isOpen_ball.exists_eq_add_of_deriv_eq (convex_ball z₁ ε).isPreconnected
    (fun z hz => (hball z hz).1.differentiableAt.differentiableWithinAt)
    (fun z hz => (hball z hz).2.differentiableAt.differentiableWithinAt)
    (fun z hz => by rw [(hball z hz).1.deriv, (hball z hz).2.deriv])
  exact ⟨C, Filter.eventuallyEq_of_mem (ball_mem_nhds z₁ hε) hC⟩

/-- A function holomorphic on a ball has a primitive on it (Morera, `DifferentiableOn.isExactOn_ball`). -/
theorem B_exists_primitive_ball {g : ℂ → ℂ} {c : ℂ} {r : ℝ} (hg : DifferentiableOn ℂ g (ball c r)) :
    ∃ Φ : ℂ → ℂ, ∀ z ∈ ball c r, HasDerivAt Φ (g z) z :=
  hg.isExactOn_ball

end GoldbachBoundaries.Paper2.M6
