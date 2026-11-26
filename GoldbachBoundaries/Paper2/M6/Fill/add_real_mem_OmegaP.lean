import GoldbachBoundaries.Paper2.M6.Defs

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M6

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **Eastward rays stay in `Ω`** (unconditional). `Re(z + t) ≥ Re z > 0`; if `z + t = a - t'` with `t' ≥ 0`, then
`z = a - (t + t')` lies on the cut of `a`, contradicting `z ∈ Ω`. -/
theorem add_real_mem_OmegaP {z : ℂ} (hz : z ∈ OmegaP) {t : ℝ} (ht : 0 ≤ t) : z + t ∈ OmegaP := by
  obtain ⟨hz0, hzc⟩ := hz
  simp only [halfPlane, mem_ofPred_eq] at hz0
  refine ⟨show (0 : ℝ) < (z + t).re by simp; linarith, fun hcut => hzc ?_⟩
  obtain ⟨a, ha, t', ht', he⟩ : ∃ a ∈ PoleSetQ, ∃ t' : ℝ, 0 ≤ t' ∧ z + t = a - t' := by
    simpa using hcut
  refine mem_iUnion₂.mpr ⟨a, ha, t + t', by linarith, ?_⟩
  push_cast
  linear_combination he

end GoldbachBoundaries.Paper2.M6
