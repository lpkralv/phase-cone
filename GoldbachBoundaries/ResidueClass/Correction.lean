import GoldbachBoundaries.ResidueClass.GammaWeights
import GoldbachBoundaries.PhiR.Proof.M2Continuation

/-! # The meromorphic correction in the binary Mellin identity -/

noncomputable section

open Complex Filter Set

namespace GoldbachBoundaries.ResidueClass

variable (q : ℕ) [NeZero q]

/-- Completing the Mellin transform of the linear term gives this correction.
The rational term subtracts one copy of the squared principal contribution. -/
def W (s : ℂ) : ℂ :=
  2 * principalWeight q * (Gamma (s - 1) * D q (s - 1)) - principalWeight q ^ 2 / (s - 2)

theorem meromorphic_W : Meromorphic (W q) := by
  intro s
  have hm : MeromorphicAt (fun z ↦ Gamma z * D q z) (s - 1) :=
    (PhiRProof.meromorphicAt_Gamma _).mul (meromorphic_D _)
  have hshift : MeromorphicAt (fun z ↦ Gamma (z - 1) * D q (z - 1)) s :=
    hm.comp_analyticAt (g := fun z : ℂ ↦ z - 1) (by fun_prop)
  exact ((MeromorphicAt.const _ s).mul hshift).sub
    ((MeromorphicAt.const _ s).div (analyticAt_id.sub analyticAt_const).meromorphicAt)

variable {q}

private theorem hasResidue_shiftedGammaD {z R : ℂ} (hz : 0 < z.re) (h : HasResidue (D q) z R) :
    HasResidue (fun s ↦ 2 * principalWeight q * (Gamma (s - 1) * D q (s - 1)))
      (z + 1) (2 * principalWeight q * (Gamma z * R)) := by
  have hg := (PhiRProof.analyticAt_Gamma_of_re_pos hz).continuousAt
  unfold HasResidue at h
  have hr : HasResidue (fun s ↦ Gamma s * D q s) z (Gamma z * R) := by
    simpa only [HasResidue, mul_left_comm] using (hg.tendsto.mono_left nhdsWithin_le_nhds).mul h
  exact (hr.comp_sub_const 1).const_mul _

/-- The principal residue at two comes from the difference of two simple poles. -/
theorem hasResidue_W_two : HasResidue (W q) 2 (principalWeight q ^ 2) := by
  have hr := (hasResidue_shiftedGammaD (by norm_num : (0 : ℝ) < (1 : ℂ).re)
    (hasResidue_D_one (q := q))).sub (hasResidue_div_sub (1 + 1) (principalWeight q ^ 2))
  rw [show (1 : ℂ) + 1 = 2 by norm_num] at hr
  convert hr using 1
  · rfl
  · simp only [Gamma_one, one_mul, principalWeight]
    ring

/-- The mixed residue at a translate of a critical point. -/
theorem hasResidue_W_critical (t : ℝ) :
    HasResidue (W q) (criticalPoint t + 1) (-(2 * principalWeight q * gammaWeight q t)) := by
  have hz : 0 < (criticalPoint t).re := by rw [criticalPoint_re]; norm_num
  have hne : criticalPoint t ≠ 1 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num [criticalPoint_re] at hh
  have hs : criticalPoint t + 1 ≠ 2 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num [criticalPoint_re] at hh
  have hrat : AnalyticAt ℂ (fun s : ℂ ↦ principalWeight q ^ 2 / (s - 2)) (criticalPoint t + 1) :=
    analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hs)
  have hr := (hasResidue_shiftedGammaD hz (hasResidue_D (q := q) hz hne)).sub
    (hasResidue_zero_of_analyticAt hrat)
  convert hr using 1
  · rfl
  · simp only [sub_zero, gammaWeight, ordinateWeight, principalWeight]
    ring

/-- In the open half-plane of continuation the correction is holomorphic
away from the principal pole and the translated critical ordinates. -/
theorem analyticAt_W (hGRH : GRH q) {s : ℂ} (hs : 1 < s.re) (hs₂ : s ≠ 2)
    (hcrit : ∀ t ∈ Ordinates q, s ≠ criticalPoint t + 1) : AnalyticAt ℂ (W q) s := by
  have hp : 0 < (s - 1).re := by simp; linarith
  have hp₁ : s - 1 ≠ 1 := fun h ↦ hs₂ (by linear_combination h)
  have hD : AnalyticAt ℂ (D q) (s - 1) := by
    apply analyticAt_D hp hp₁
    intro χ
    by_cases hre : 1 ≤ (s - 1).re
    · exact primitiveL_ne_zero_of_one_le_re χ hre
    · intro hzero
      have hmem : s - 1 ∈ primitiveZeros χ := ⟨hzero, hp, lt_of_not_ge hre⟩
      have he : criticalPoint (s - 1).im = s - 1 :=
        Complex.ext (by rw [criticalPoint_re, hGRH χ _ hmem]) (criticalPoint_im _)
      exact hcrit _ (mem_Ordinates_iff.mpr ⟨χ, he.symm ▸ hmem⟩) (by rw [he, sub_add_cancel])
  have hp' : AnalyticAt ℂ (fun z : ℂ ↦ Gamma (z - 1) * D q (z - 1)) s :=
    ((PhiRProof.analyticAt_Gamma_of_re_pos hp).mul hD).comp (f := fun z : ℂ ↦ z - 1)
      (show AnalyticAt ℂ (fun z : ℂ ↦ z - 1) s by fun_prop)
  exact (analyticAt_const.mul hp').sub
    (analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hs₂))

end GoldbachBoundaries.ResidueClass
