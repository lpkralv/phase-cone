import GoldbachBoundaries.Paper2.M2.Single

/-!
# Filler (Group D): `exists_imagAxis_mem`

If `W` missed the imaginary axis it would lie in the union of the disjoint open half-planes `{Re z > 0}` and
`{Re z < 0}`; being preconnected and meeting the first (at `1`), it would lie in `{Re z > 0}`, contradicting
`halfPlane 0 ⊂ W`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M2

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **A connected set properly containing `{Re z > 0}` meets the imaginary axis** (topology). Otherwise
`W = (W ∩ {Re z > 0}) ∪ (W ∩ {Re z < 0})`, two disjoint relatively open sets, the first containing `1`, the second a
point of `W ∖ {Re z > 0}` (which has `Re < 0`); this contradicts `IsPreconnected W`
(`isPreconnected_iff_subset_of_disjoint` or `IsPreconnected.subset_left_of_subset_union`). The point `w` with `Re w = 0`
is `(Im w) i`. Openness of `W` is not needed. Size: 60–120 lines. -/
theorem exists_imagAxis_mem {W : Set ℂ} (hWc : IsConnected W) (hsub : halfPlane 0 ⊂ W) :
    ∃ y : ℝ, (y : ℂ) * I ∈ W := by
  by_contra hno
  push Not at hno
  have hre : ∀ w ∈ W, w.re ≠ 0 := by
    intro w hw h0
    apply hno w.im
    have : (w.im : ℂ) * I = w := by
      apply Complex.ext <;> simp [h0]
    rw [this]; exact hw
  have hu : IsOpen (halfPlane 0) := isOpen_halfPlane 0
  have hv : IsOpen {z : ℂ | z.re < 0} := isOpen_lt Complex.continuous_re continuous_const
  have huv : Disjoint (halfPlane 0) {z : ℂ | z.re < 0} := by
    rw [Set.disjoint_left]
    intro z h1 h2
    have h1' : 0 < z.re := h1
    have h2' : z.re < 0 := h2
    linarith
  have hsuv : W ⊆ halfPlane 0 ∪ {z : ℂ | z.re < 0} := by
    intro w hw
    rcases lt_or_gt_of_ne (hre w hw) with h | h
    · exact Or.inr h
    · exact Or.inl h
  have h1 : (1 : ℂ) ∈ halfPlane 0 := by norm_num [halfPlane]
  have hne : (W ∩ halfPlane 0).Nonempty := ⟨1, hsub.1 h1, h1⟩
  have hWu := hWc.isPreconnected.subset_left_of_subset_union hu hv huv hsuv hne
  exact hsub.2 hWu

end GoldbachBoundaries.Paper2.M2
