import GoldbachBoundaries.Paper2.M4a.Fill.isMeromorphic₂_restrict_line

/-!
# M4a filler E: `bracket_meromorphic_of_K4`

Restrict `k` to the lines `z = 1` (`c₀ = 1, c₁ = 0`) and `z = L(s) - 1` (`c₀ = ℓ₀ - 1, c₁ = ℓ`) with
`isMeromorphic₂_restrict_line`, getting `g₁`, `g₂`. The extension is `f = 𝔟` on `D_L` and `g₁ + g₂` elsewhere. On
`D_L`, (K1) makes `k(·, y)` continuous at `1` and at `L(y) - 1`, so `𝔟 = g₁ + g₂` there off isolated points; hence
`f = g₁ + g₂` on a punctured neighbourhood of every point of the disc, and `f` is meromorphic (`MeromorphicAt.congr`).
-/

noncomputable section

open Complex Filter Topology Set Metric

namespace GoldbachBoundaries.Paper2.M4a

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **Under (K4) the bracket extends meromorphically across the line** ((K1), (K4)). Apply
`isMeromorphic₂_restrict_line` to the lines `c₀ = 1, c₁ = 0` and `c₀ = ℓ₀ - 1, c₁ = ℓ` (so `c₀ + c₁s = L(s) - 1`) at
`s₀`, giving `g₁`, `g₂` on `ball s₀ r` (the smaller radius). Let `f = (ball s₀ r ∩ D_L).piecewise (bracket A k) (g₁ + g₂)`.
For `y ∈ D_L`, `z ↦ k(z, y)` is continuous at `1` and at `L(y) - 1` ((K1): open domain, joint differentiability),
so `f = g₁ + g₂` on a punctured neighbourhood of every point of the ball (`Filter.EventuallyEq` from the two
restriction statements and `piecewise`); hence `MeromorphicOn f` (`MeromorphicAt.congr`), and `f = 𝔟` on
`ball s₀ r ∩ D_L` by construction. Size: 100–200 lines. -/
theorem bracket_meromorphic_of_K4 (A : Aff) (k : ℂ → ℂ → ℂ) (hK1 : K1 A k) (hK4 : K4 k) :
    ∀ s₀ ∈ A.lineL, ∃ r : ℝ, 0 < r ∧ ∃ f : ℂ → ℂ, MeromorphicOn f (ball s₀ r) ∧
      EqOn f (bracket A k) (ball s₀ r ∩ A.DL) := by
  classical
  intro s₀ _
  obtain ⟨r₁, hr₁, g₁, hg₁, h₁⟩ := isMeromorphic₂_restrict_line hK4 1 0 s₀
  obtain ⟨r₂, hr₂, g₂, hg₂, h₂⟩ :=
    isMeromorphic₂_restrict_line hK4 ((A.ell0 : ℂ) - 1) (A.ell : ℂ) s₀
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, fun s => if s ∈ A.DL then bracket A k s else g₁ s + g₂ s, ?_, ?_⟩
  · intro x hx
    have hx1 : x ∈ ball s₀ r₁ := ball_subset_ball (min_le_left _ _) hx
    have hx2 : x ∈ ball s₀ r₂ := ball_subset_ball (min_le_right _ _) hx
    refine ((hg₁ x hx1).add (hg₂ x hx2)).congr ?_
    filter_upwards [h₁ x hx1, h₂ x hx2] with y hy1 hy2
    by_cases hy : y ∈ A.DL
    · have e1 : (1 : ℂ) + 0 * y = 1 := by ring
      have e2 : ((A.ell0 : ℂ) - 1) + (A.ell : ℂ) * y = A.app y - 1 := by simp only [Aff.app]; ring
      have c1 : ContinuousAt (fun z => k z y) ((1 : ℂ) + 0 * y) := by
        rw [e1]
        exact FillE.continuousAt_slice_of_K1 hK1 hy (FillE.one_mem_Str hy).1 (FillE.one_mem_Str hy).2
      have c2 : ContinuousAt (fun z => k z y) (((A.ell0 : ℂ) - 1) + (A.ell : ℂ) * y) := by
        rw [e2]
        exact FillE.continuousAt_slice_of_K1 hK1 hy (FillE.app_sub_one_mem_Str hy).1
          (FillE.app_sub_one_mem_Str hy).2
      simp only [Pi.add_apply, hy, ite_true, bracket]
      rw [← hy1 c1, ← hy2 c2, e1, e2]
    · simp only [Pi.add_apply, hy, ite_false]
  · intro s hs
    simp only [hs.2, ite_true]

end GoldbachBoundaries.Paper2.M4a
