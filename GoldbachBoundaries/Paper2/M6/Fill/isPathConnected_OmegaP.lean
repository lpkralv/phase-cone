import GoldbachBoundaries.Paper2.M6.Fill.add_real_mem_OmegaP
import GoldbachBoundaries.Paper2.M6.Fill.halfPlane_one_subset_OmegaP

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M6

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- The eastward push `z + max(0, 2 - Re z)`, which has real part `≥ 2`. -/
def eastPushA (z : ℂ) : ℂ := z + (max 0 (2 - z.re) : ℝ)

lemma two_le_re_eastPushA (z : ℂ) : 2 ≤ (eastPushA z).re := by
  simp only [eastPushA, add_re, ofReal_re]
  have := le_max_right 0 (2 - z.re); linarith

lemma continuous_eastPushA : Continuous eastPushA := by
  unfold eastPushA
  fun_prop

/-- The segment from `z ∈ Ω` to its eastward push lies in `Ω`. -/
lemma segment_eastPushA_subset {z : ℂ} (hz : z ∈ OmegaP) : segment ℝ z (eastPushA z) ⊆ OmegaP := by
  rintro w ⟨a, b, ha, hb, hab, rfl⟩
  have : a • z + b • eastPushA z = z + ((b * max 0 (2 - z.re) : ℝ) : ℂ) := by
    simp only [eastPushA, real_smul, smul_add, ofReal_mul]
    have hab' : (a : ℂ) + b = 1 := by exact_mod_cast hab
    linear_combination z * hab'
  rw [this]
  exact add_real_mem_OmegaP hz (mul_nonneg hb (le_max_left _ _))

/-- `{Re z ≥ 2}` is a convex subset of `Ω`. -/
lemma convex_re_ge_two_A : Convex ℝ {w : ℂ | 2 ≤ w.re} := convex_halfSpace_re_ge 2

lemma re_ge_two_subset_OmegaP_A : {w : ℂ | 2 ≤ w.re} ⊆ OmegaP := fun w hw =>
  halfPlane_one_subset_OmegaP (show (1 : ℝ) < w.re by simp only [mem_ofPred_eq] at hw; linarith)

/-- **`Ω` is path connected** (unconditional). -/
theorem isPathConnected_OmegaP : IsPathConnected OmegaP := by
  refine ⟨2, re_ge_two_subset_OmegaP_A (by simp), fun {y} hy => ?_⟩
  have h1 : JoinedIn OmegaP y (eastPushA y) := JoinedIn.of_segment_subset (segment_eastPushA_subset hy)
  have h2 : JoinedIn OmegaP (eastPushA y) 2 := JoinedIn.of_segment_subset
    ((convex_re_ge_two_A.segment_subset (two_le_re_eastPushA y) (by simp)).trans re_ge_two_subset_OmegaP_A)
  exact (h1.trans h2).symm

end GoldbachBoundaries.Paper2.M6
