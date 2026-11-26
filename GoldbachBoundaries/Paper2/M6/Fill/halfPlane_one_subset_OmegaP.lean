import GoldbachBoundaries.Paper2.M6.Defs

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M6

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **`{Re z > 1} ⊆ Ω`** (unconditional). `1 < Re z` gives `0 < Re z`; a point `a - t` of a cut (`a ∈ Σ`, `t ≥ 0`) has
`Re(a - t) = Re a - t ≤ 1` by M1's `poleSetQ_re_bounds`. -/
theorem halfPlane_one_subset_OmegaP : halfPlane 1 ⊆ OmegaP := by
  intro z hz
  simp only [halfPlane, mem_ofPred_eq] at hz
  refine ⟨show (0 : ℝ) < z.re by linarith, fun hcut => ?_⟩
  obtain ⟨a, ha, t, ht, rfl⟩ : ∃ a ∈ PoleSetQ, ∃ t : ℝ, 0 ≤ t ∧ z = a - t := by
    simpa using hcut
  have := (M1.poleSetQ_re_bounds ha).2.1
  simp at hz
  linarith

end GoldbachBoundaries.Paper2.M6
