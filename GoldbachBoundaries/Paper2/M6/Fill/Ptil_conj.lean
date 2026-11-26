import GoldbachBoundaries.Paper2.M6.Fill.OmegaP_subset
import GoldbachBoundaries.Paper2.M6.Fill.add_real_mem_OmegaP
import GoldbachBoundaries.Paper2.M6.Fill.P_conj

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M6

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **`P̃(z̄) = conj P̃(z)` on `Ω`** (unconditional). `conj z + 2 = conj (z + 2)`, so the first term is `P_conj`. For
`t ∈ [0, 2]`, `z + t ∈ Ω ⊆ {Re z > 0} ∖ Σ`, so `Qcont(conj z + t) = conj Qcont(z + t)` (M1's `Qcont_conj`); then
`intervalIntegral.integral_congr` and `intervalIntegral_conj`. -/
theorem Ptil_conj {z : ℂ} (hz : z ∈ OmegaP) : Ptil (conj z) = conj (Ptil z) := by
  unfold Ptil
  have h1 : P (conj z + 2) = conj (P (z + 2)) := by
    rw [show conj z + 2 = conj (z + 2) by rw [map_add, map_ofNat]]
    exact P_conj (z + 2)
  have h2 : EqOn (fun t : ℝ => Qcont (conj z + t)) (fun t : ℝ => conj (Qcont (z + t))) (uIcc 0 2) := by
    intro t ht
    rw [uIcc_of_le (by norm_num)] at ht
    have hmem := OmegaP_subset (add_real_mem_OmegaP hz ht.1)
    simp only
    rw [show conj z + (t : ℂ) = conj (z + t) by simp]
    exact M1.Qcont_conj hmem
  rw [intervalIntegral.integral_congr h2, intervalIntegral.intervalIntegral_conj, h1, map_add]

end GoldbachBoundaries.Paper2.M6
