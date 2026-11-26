import GoldbachBoundaries.Paper2.M6.Defs

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M6

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **The ray is closed** (general). `rayFrom a θ` is the image of `[0, ∞)` under the isometry
`t ↦ a + t e^{iθ}` (`|e^{iθ}| = 1`), a closed embedding. -/
theorem isClosed_rayFrom (a : ℂ) (θ : ℝ) : IsClosed (rayFrom a θ) := by
  have hiso : Isometry (fun t : ℝ => a + (t : ℂ) * exp (θ * I)) := by
    refine Isometry.of_dist_eq fun s t => ?_
    rw [dist_eq_norm, dist_eq_norm, add_sub_add_left_eq_sub, ← sub_mul, norm_mul,
      norm_exp_ofReal_mul_I, mul_one, ← ofReal_sub, norm_real, Real.norm_eq_abs]
  have hset : rayFrom a θ = (fun t : ℝ => a + (t : ℂ) * exp (θ * I)) '' Ici 0 := by
    ext z
    simp only [rayFrom, mem_ofPred_eq, mem_image, mem_Ici]
    constructor
    · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, rfl⟩
    · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, rfl⟩
  rw [hset]
  exact hiso.isClosedEmbedding.isClosedMap _ isClosed_Ici

end GoldbachBoundaries.Paper2.M6
