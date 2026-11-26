import GoldbachBoundaries.Paper2.M6.Defs

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M6

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **`Ω ⊆ {Re z > 0} ∖ Σ`** (unconditional). `Ω ⊆ halfPlane 0` by definition, and `a ∈ Σ` lies on its own cut
(`t = 0`, `a = a - 0`). -/
theorem OmegaP_subset : OmegaP ⊆ halfPlane 0 \ PoleSetQ := by
  intro z hz
  refine ⟨hz.1, fun hzP => hz.2 ?_⟩
  exact mem_iUnion₂.mpr ⟨z, hzP, 0, le_rfl, by simp⟩

end GoldbachBoundaries.Paper2.M6
