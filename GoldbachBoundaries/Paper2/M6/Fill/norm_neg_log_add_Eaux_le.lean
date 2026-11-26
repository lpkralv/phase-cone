import GoldbachBoundaries.Paper2.M6.Defs

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
namespace GoldbachBoundaries.Paper2.M6
open GoldbachBoundaries GoldbachBoundaries.Paper2

theorem norm_neg_log_add_Eaux_le (hRH : RiemannHypothesis) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ x y : ℝ, 1 / 2 + ε ≤ x → x ≤ 3 → 3 ≤ |y| →
      ‖-Complex.log ((x : ℂ) + y * I - 1) + ThmA.Eaux ((x : ℂ) + y * I)‖ ≤ C * Real.log |y| := by
  obtain ⟨C₀, hC₀⟩ := ThmA.norm_Eaux_le hRH (σ₁ := 3) hε
  let A := max C₀ 0
  let B := A + Real.log 3 + Real.pi
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hB : 0 ≤ B := by dsimp [B, A]; positivity
  refine ⟨A + 1 + B / Real.log 3, ?_⟩
  intro x y hx hx3 hy
  have hypos : 0 < |y| := by linarith
  have hlogy : Real.log 3 ≤ Real.log |y| := Real.log_le_log (by norm_num) hy
  have hlogy0 : 0 ≤ Real.log |y| := le_trans hlog3.le hlogy
  have hnormlo : |y| ≤ ‖(x : ℂ) + y * I - 1‖ := by
    simpa using Complex.abs_im_le_norm ((x : ℂ) + y * I - 1)
  have hnormpos : 0 < ‖(x : ℂ) + y * I - 1‖ := lt_of_lt_of_le hypos hnormlo
  have hnormhi : ‖(x : ℂ) + y * I - 1‖ ≤ 3 * |y| := by
    have h := Complex.norm_le_abs_re_add_abs_im ((x : ℂ) + y * I - 1)
    simp only [sub_re, add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im,
      mul_zero, mul_one, sub_self, add_zero, one_re, sub_im, add_im, mul_im,
      zero_add, one_im, sub_zero] at h
    have habs : |x - 1| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    linarith
  have hlognorm0 : 0 ≤ Real.log ‖(x : ℂ) + y * I - 1‖ :=
    Real.log_nonneg (by linarith)
  have hlognorm : Real.log ‖(x : ℂ) + y * I - 1‖ ≤ Real.log 3 + Real.log |y| := by
    simpa [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (ne_of_gt hypos)] using
      Real.log_le_log hnormpos hnormhi
  have hL := ThmA.GroupE.lines_norm_log_le ((x : ℂ) + y * I - 1)
  rw [abs_of_nonneg hlognorm0] at hL
  have hE := hC₀ ((x : ℂ) + y * I) (by simpa using hx) (by simpa using hx3)
    (by simpa using (show 2 ≤ |y| by linarith))
  simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_one, mul_zero, add_zero, zero_add] at hE
  have hEA : ‖ThmA.Eaux ((x : ℂ) + y * I)‖ ≤ A * (1 + Real.log |y|) := by
    refine hE.trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
  have habsorb : B ≤ (B / Real.log 3) * Real.log |y| := by
    calc
      B = (B / Real.log 3) * Real.log 3 := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hlogy (div_nonneg hB hlog3.le)
  calc
    _ ≤ ‖Complex.log ((x : ℂ) + y * I - 1)‖ + ‖ThmA.Eaux ((x : ℂ) + y * I)‖ := by
      simpa using norm_add_le (-Complex.log ((x : ℂ) + y * I - 1)) (ThmA.Eaux ((x : ℂ) + y * I))
    _ ≤ (A + 1 + B / Real.log 3) * Real.log |y| := by dsimp [B] at habsorb; nlinarith

end GoldbachBoundaries.Paper2.M6
