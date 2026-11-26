import GoldbachBoundaries.Paper2.M6.Defs

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M6

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **`Ω` is symmetric under conjugation** (unconditional). `Re(z̄) = Re z`; if `conj z = a - t` with `a ∈ Σ`, then
`z = conj a - t` with `conj a ∈ Σ` (M1's `conj_mem_poleSetQ`), contradicting `z ∈ Ω`. -/
theorem conj_mem_OmegaP {z : ℂ} (hz : z ∈ OmegaP) : conj z ∈ OmegaP := by
  obtain ⟨hz0, hzc⟩ := hz
  simp only [halfPlane, mem_ofPred_eq] at hz0
  refine ⟨show (0 : ℝ) < (conj z).re by simpa using hz0, fun hcut => hzc ?_⟩
  obtain ⟨a, ha, t, ht, he⟩ : ∃ a ∈ PoleSetQ, ∃ t : ℝ, 0 ≤ t ∧ conj z = a - t := by
    simpa using hcut
  refine mem_iUnion₂.mpr ⟨conj a, M1.conj_mem_poleSetQ ha, t, ht, ?_⟩
  have := congrArg conj he
  simpa using this

end GoldbachBoundaries.Paper2.M6
