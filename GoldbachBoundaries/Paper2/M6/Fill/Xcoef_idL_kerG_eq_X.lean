import GoldbachBoundaries.Paper2.M6.Defs

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M6

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **Paper 2's `X_α` for `G` is paper 1's** (`α ∈ 𝒞`). At `α = 2` both are `J_{11}`. Otherwise, with
`b = α - 1 ∈ Σ`, `c₁c_b(J_{1b} + J_{b1}) = (-1)(-R_b) · 2J_{1b}` and `R_b = Res_b(Qcont) = sigmaRes b`. -/
theorem Xcoef_idL_kerG_eq_X {α : ℂ} (hα : α ∈ catalogue) : Xcoef Aff.idL kerG α = ThmA.X α := by
  -- `Jseg_idL_kerG_eq_J` and `J_swap_one`, proved inline (same proofs as in their own Fill files) so this file
  -- depends on no sorry lemma.
  have Jseg_idL_kerG_eq_J_proof : ∀ a b s : ℂ, Jseg Aff.idL kerG a b s = ThmA.J a b s := by
    intro a b s
    simp only [Jseg, ThmA.J, ThmA.segInt, M4a.app_idL, kerG, KerS, ThmA.Kern]
    have h : s - a - b = s - b - a := by ring
    rw [h]
  have J_swap_one_proof : ∀ b s : ℂ, ThmA.J b 1 s = ThmA.J 1 b s := by
    intro b s
    simp only [ThmA.J, ThmA.segInt]
    have h1 : s - 1 - b = s - b - 1 := by ring
    rw [h1]
    congr 1
    have := intervalIntegral.integral_comp_sub_left
      (fun τ : ℝ => ThmA.Kern s (b + (τ : ℂ) * (s - b - 1))) (a := 0) (b := 1) (1 : ℝ)
    simp only [sub_zero, sub_self] at this
    rw [← this]
    congr 1
    funext τ
    have : b + ((1 - τ : ℝ) : ℂ) * (s - b - 1) = s - (1 + (τ : ℂ) * (s - b - 1)) := by
      push_cast; ring
    rw [this]
    exact M1.KerS_sub_symm s _
  by_cases h2 : α = 2
  · have h : Aff.idL.app α - 1 = 1 := by rw [M4a.app_idL, h2]; norm_num
    rw [M4a.Xcoef_of_eq _ _ h]
    funext s
    simp only [ThmA.X, h2, ite_true]
    exact Jseg_idL_kerG_eq_J_proof 1 1 s
  · have h : Aff.idL.app α - 1 ≠ 1 := by
      rw [M4a.app_idL]; intro h; exact h2 (by linear_combination h)
    rw [M4a.Xcoef_of_ne _ _ h]
    funext s
    have hb := sub_one_mem_poleSetQ_of_mem_catalogue hα
    have hres : sigmaRes (α - 1) = Rcoef (α - 1) := sigmaRes_eq (M1.hasResidue_Qcont_Rcoef hb)
    simp only [ThmA.X, h2, ite_false, M4a.app_idL, Jseg_idL_kerG_eq_J_proof, cP, M1.Rcoef_one', hres]
    rw [J_swap_one_proof]
    ring

end GoldbachBoundaries.Paper2.M6
