import GoldbachBoundaries.Paper2.M6.Defs

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
namespace GoldbachBoundaries.Paper2.M6
open GoldbachBoundaries GoldbachBoundaries.Paper2

theorem isOpen_isPreconnected_slitHalf :
    IsOpen (halfPlane (1 / 2) \ {z | ∃ x : ℝ, 1 / 2 < x ∧ x ≤ 1 ∧ z = x}) ∧
      IsPreconnected (halfPlane (1 / 2) \ {z | ∃ x : ℝ, 1 / 2 < x ∧ x ≤ 1 ∧ z = x}) := by
  have hset : (halfPlane (1 / 2) \ {z | ∃ x : ℝ, 1 / 2 < x ∧ x ≤ 1 ∧ z = x}) =
      {z : ℂ | 1 / 2 < z.re ∧ (z.im ≠ 0 ∨ 1 < z.re)} := by
    ext z
    constructor
    · rintro ⟨hz, hn⟩
      refine ⟨hz, ?_⟩
      by_cases hi : z.im = 0
      · right
        by_contra hr
        apply hn
        exact ⟨z.re, hz, le_of_not_gt hr, by apply Complex.ext <;> simp [hi]⟩
      · exact Or.inl hi
    · rintro ⟨hz, hi | hr⟩ <;> refine ⟨hz, ?_⟩ <;> rintro ⟨x, hx, hx1, rfl⟩
      · exact hi (by simp)
      · simp only [ofReal_re] at hr; linarith
  rw [hset]
  refine ⟨?_, ?_⟩
  · exact (isOpen_lt continuous_const continuous_re).inter
      ((isOpen_ne_fun continuous_im continuous_const).union
        (isOpen_lt continuous_const continuous_re))
  · have hs : StarConvex ℝ (2 : ℂ)
        {z : ℂ | 1 / 2 < z.re ∧ (z.im ≠ 0 ∨ 1 < z.re)} := by
      intro z hz a b ha hb hab
      simp only [mem_ofPred_eq, add_re, add_im, smul_re, smul_im, smul_eq_mul]
      norm_num only [re_ofNat, im_ofNat, mul_zero, zero_add]
      have hcomb (r : ℝ) (hr2 : r < 2) (hrz : r < z.re) : r < a * 2 + b * z.re := by
        by_cases hb0 : b = 0
        · simp [hb0] at hab ⊢
          linarith
        · have hpos := mul_pos (lt_of_le_of_ne hb (Ne.symm hb0)) (sub_pos.mpr hrz)
          nlinarith [mul_nonneg ha (sub_nonneg.mpr hr2.le)]
      refine ⟨hcomb (1 / 2) (by norm_num) hz.1, ?_⟩
      rcases hz.2 with hi | hr
      · by_cases hb0 : b = 0
        · right; simp [hb0] at hab ⊢; linarith
        · exact Or.inl (mul_ne_zero hb0 hi)
      · exact Or.inr (hcomb 1 (by norm_num) hr)
    exact (hs.isPathConnected (by norm_num)).isConnected.isPreconnected

end GoldbachBoundaries.Paper2.M6
