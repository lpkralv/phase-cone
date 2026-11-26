import GoldbachBoundaries.Paper2.M5.TkLine

/-!
# M5 filler T3: `tkPack_one`

The base case `k = 1` of Theorem G: `F = Qcont`, `H = 0`, from paper 1's facts about `Qcont`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

theorem tkPack_one (hRH : RiemannHypothesis) : TkPack 1 Qcont 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    have hs' : (0 : ℝ) < s.re := by
      have : ((1 : ℕ) : ℝ) - 1 < s.re := hs
      simpa using this
    exact meromorphicAt_Qcont hs'
  · intro s hs
    have hs' : (1 : ℝ) < s.re := by
      have : ((1 : ℕ) : ℝ) < s.re := hs
      simpa using this
    rw [Tk_one']
    exact TIdentity.Qcont_eq_Q_of_one_lt hs'
  · exact differentiableOn_const 0
  · intro s hs _ _
    have hs' : (0 : ℝ) < s.re := by simpa using hs
    have hG : Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs'
    simp only [Nat.cast_one, sub_add_cancel, Pi.zero_apply, zero_add, one_mul]
    rw [div_self hG, one_mul]
  · intro s hs hs1
    have hs' : 1 / 2 < s.re := by
      have : ((1 : ℕ) : ℝ) - 1 / 2 < s.re := hs
      norm_num at this ⊢; linarith
    exact TIdentity.analyticAt_Qcont_of_RH hRH hs' (by simpa using hs1)
  · have hm : MeromorphicAt Qcont 1 := meromorphicAt_Qcont (by norm_num)
    simpa using hasResidue_Qcont_one.meromorphicOrderAt_eq_neg_one hm one_ne_zero
  · simpa using hasResidue_Qcont_one
  · intro x₁ x₂ hx₁ _
    have hε : 0 < x₁ - 1 / 2 := by
      have : ((1 : ℕ) : ℝ) - 1 / 2 < x₁ := hx₁
      norm_num at this ⊢; linarith
    obtain ⟨C₀, hC₀⟩ := TIdentity.norm_Qcont_le_log hRH hε
    refine ⟨1, |C₀|, 4, fun x hx y hy => ?_⟩
    have hre : 1 / 2 + (x₁ - 1 / 2) ≤ ((x : ℂ) + y * I).re := by
      simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero]
      linarith [hx.1]
    have him : ((x : ℂ) + y * I).im = y := by simp
    have h := hC₀ _ hre (by rw [him]; exact hy)
    rw [him] at h
    have hy0 : 0 < |y| := by linarith
    have hlog0 : 0 ≤ Real.log |y| := Real.log_nonneg (by linarith)
    have hlog : Real.log |y| ≤ |y| := (Real.log_le_sub_one_of_pos hy0).trans (by linarith)
    rw [Real.rpow_one]
    calc ‖Qcont (x + y * I)‖ ≤ C₀ * Real.log |y| := h
      _ ≤ |C₀| * Real.log |y| := mul_le_mul_of_nonneg_right (le_abs_self _) hlog0
      _ ≤ |C₀| * |y| := mul_le_mul_of_nonneg_left hlog (abs_nonneg _)

end GoldbachBoundaries.Paper2.M5
