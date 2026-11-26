import GoldbachBoundaries.Paper2.M5.General
import GoldbachBoundaries.Paper2.M5.Fill.QCommon
import GoldbachBoundaries.Paper2.M5.Fill.poleSetQ_re_cases
import GoldbachBoundaries.Paper2.M5.Fill.norm_sigmaTail_four_le

/-! Filler group Q: `Qleft_i` (`Qleft.lean`). `w = x₀ + iy`, `1/3 < x₀ < 1/2`. Off `Σ_Q` by `poleSetQ_re_cases`.
For `|y| ≥ 2`: `Q(w) = A(w) - A(2w) - A(3w) + tail`; `norm_negLogDerivZeta_le_of_sep` at `w` (`δ = 1/2 - x₀`) and at
`2w` (`δ = 2x₀ - 1/2`), using RH (`Re ρ = 1/2`); `Re 3w = 3x₀ > 1`; the tail by `norm_sigmaTail_four_le`. For
`|y| ≤ 2`: `Qcont` is continuous on the compact segment (it misses `Σ_Q`). -/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **`cl:lem:Qleft`(i) for `Qcont`** (RH, (Z1)-(Z3)). -/
theorem Qleft_i (hRH : RiemannHypothesis) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) :
    ∀ x₀ : ℝ, 1 / 3 < x₀ → x₀ < 1 / 2 → ∃ C : ℝ, ∀ y : ℝ,
      (x₀ + y * I : ℂ) ∉ PoleSetQ ∧ ‖Qcont (x₀ + y * I)‖ ≤ C * Real.log (|y| + 3) := by
  intro x₀ hx1 hx2
  obtain ⟨Ks, hKs0, hKs⟩ := exists_sep_bound_nonneg hZ1 hZ2 hZ3
  obtain ⟨T, hT⟩ := norm_sigmaTail_four_le
  have hRHre : ∀ ρ ∈ NontrivialZeros, ρ.re = 1 / 2 := fun ρ hρ => sigmaFinite_re_eq_half hRH hρ
  have hre : ∀ y : ℝ, ((x₀ : ℂ) + y * I).re = x₀ := fun y => by simp
  have him : ∀ y : ℝ, ((x₀ : ℂ) + y * I).im = y := fun y => by simp
  have hnot : ∀ y : ℝ, ((x₀ : ℂ) + y * I) ∉ PoleSetQ := fun y hy => by
    rcases poleSetQ_re_cases hRH hy with h | ⟨h, -⟩ | h
    · have := congrArg Complex.re h
      rw [hre] at this
      norm_num at this
      linarith
    · rw [hre] at h; linarith
    · rw [hre] at h; linarith
  -- the compact segment `|y| ≤ 2`
  have hcont : ContinuousOn (fun y : ℝ => Qcont ((x₀ : ℂ) + y * I)) (Icc (-2) 2) := by
    intro y _
    have han : AnalyticAt ℂ Qcont ((x₀ : ℂ) + y * I) :=
      M2.isQCont_Qcont.2.2 _ ⟨show 0 < ((x₀ : ℂ) + y * I).re by rw [hre]; linarith, hnot y⟩
    have hlin : Continuous fun y : ℝ => (x₀ : ℂ) + y * I := by fun_prop
    exact (han.continuousAt.comp (f := fun y : ℝ => (x₀ : ℂ) + y * I) hlin.continuousAt).continuousWithinAt
  obtain ⟨B0, hB0⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  set K3 := ∑' m : ℕ, ArithmeticFunction.vonMangoldt m * (m : ℝ) ^ (-(3 * x₀)) with hK3def
  have hK3 : 0 ≤ K3 :=
    tsum_nonneg fun m => mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
  have hd1 : 0 < 1 / 2 - x₀ := by linarith
  have hd2 : 0 < 2 * x₀ - 1 / 2 := by linarith
  refine ⟨Ks / (1 / 2 - x₀) + 2 * Ks / (2 * x₀ - 1 / 2) + K3 + |T| + |B0|, fun y => ⟨hnot y, ?_⟩⟩
  set w : ℂ := (x₀ : ℂ) + y * I with hwdef
  have hlog1 : 1 ≤ Real.log (|y| + 3) := one_le_log_add_three (abs_nonneg _)
  have hc1 : 0 ≤ Ks / (1 / 2 - x₀) := by positivity
  have hc2 : 0 ≤ 2 * Ks / (2 * x₀ - 1 / 2) := by positivity
  by_cases hy : 2 ≤ |y|
  · -- `A(w)`
    have hζ1 : riemannZeta w ≠ 0 := fun hz => by
      have := hRHre w ⟨hz, by rw [hre]; linarith, by rw [hre]; linarith⟩
      rw [hre] at this; linarith
    have ha1 : ‖negLogDerivZeta w‖ ≤ Ks / (1 / 2 - x₀) * Real.log (|y| + 3) := by
      have h := hKs w (by rw [hre]; linarith) (by rw [hre]; linarith) (by rw [him]; exact hy) hζ1
        (1 / 2 - x₀) hd1 (by linarith) (fun ρ hρ _ => by
          have h1 := Complex.re_le_norm (ρ - w)
          rw [Complex.sub_re, hRHre ρ hρ, hre, norm_sub_rev] at h1
          exact h1)
      rwa [him] at h
    -- `A(2w)`
    have h2re : (2 * w).re = 2 * x₀ := by rw [show (2 * w).re = 2 * w.re by simp, hre]
    have h2im : (2 * w).im = 2 * y := by rw [show (2 * w).im = 2 * w.im by simp, him]
    have hζ2 : riemannZeta (2 * w) ≠ 0 := fun hz => by
      have := hRHre (2 * w) ⟨hz, by rw [h2re]; linarith, by rw [h2re]; linarith⟩
      rw [h2re] at this; linarith
    have hab2 : |(2 * w).im| = 2 * |y| := by rw [h2im, abs_mul]; norm_num
    have ha2 : ‖negLogDerivZeta (2 * w)‖ ≤ 2 * Ks / (2 * x₀ - 1 / 2) * Real.log (|y| + 3) := by
      have h := hKs (2 * w) (by rw [h2re]; linarith) (by rw [h2re]; linarith) (by rw [hab2]; linarith) hζ2
        (2 * x₀ - 1 / 2) hd2 (by linarith) (fun ρ hρ _ => by
          have h1 := Complex.re_le_norm (2 * w - ρ)
          rw [Complex.sub_re, hRHre ρ hρ, h2re] at h1
          exact h1)
      rw [hab2] at h
      have hl := log_mul_add_three_le (abs_nonneg y) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num)
      calc ‖negLogDerivZeta (2 * w)‖ ≤ Ks / (2 * x₀ - 1 / 2) * Real.log (2 * |y| + 3) := h
        _ ≤ Ks / (2 * x₀ - 1 / 2) * (2 * Real.log (|y| + 3)) := by gcongr
        _ = _ := by ring
    -- `A(3w)` and the tail
    have ha3 : ‖negLogDerivZeta (3 * w)‖ ≤ K3 :=
      norm_negLogDerivZeta_le_of_re (by linarith) (by rw [show (3 * w).re = 3 * w.re by simp, hre])
    have ht : ‖sigmaTail 4 w‖ ≤ T := hT w (by rw [hre]; linarith)
    have hQ := norm_Qcont_le_four (w := w) (by rw [hre]; linarith)
    have hrest : K3 + |T| + |B0| ≤ (K3 + |T| + |B0|) * Real.log (|y| + 3) := by
      have : 0 ≤ K3 + |T| + |B0| := by positivity
      nlinarith
    have hT' := le_abs_self T
    have hB0' := abs_nonneg B0
    calc ‖Qcont w‖ ≤ Ks / (1 / 2 - x₀) * Real.log (|y| + 3) +
          2 * Ks / (2 * x₀ - 1 / 2) * Real.log (|y| + 3) + (K3 + |T| + |B0|) := by linarith
      _ ≤ Ks / (1 / 2 - x₀) * Real.log (|y| + 3) + 2 * Ks / (2 * x₀ - 1 / 2) * Real.log (|y| + 3) +
          (K3 + |T| + |B0|) * Real.log (|y| + 3) := by linarith
      _ = _ := by ring
  · push Not at hy
    have hb := hB0 y (abs_le.mp hy.le)
    have hrest : |B0| ≤ (Ks / (1 / 2 - x₀) + 2 * Ks / (2 * x₀ - 1 / 2) + K3 + |T| + |B0|) *
        Real.log (|y| + 3) := by
      have h0 : 0 ≤ Ks / (1 / 2 - x₀) + 2 * Ks / (2 * x₀ - 1 / 2) + K3 + |T| := by positivity
      have hB := abs_nonneg B0
      nlinarith
    exact hb.trans ((le_abs_self B0).trans hrest)

end GoldbachBoundaries.Paper2.M5
