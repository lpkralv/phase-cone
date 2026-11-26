import GoldbachBoundaries.T0HInf.PrimeCorrection

/-! Horizontal separation from all zeros controls the prime-square correction without RH. -/
noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
namespace GoldbachBoundaries.T0HInf
open GoldbachBoundaries Paper2

lemma primeCorrection_strip_bound (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℂ, remainderAbscissa ≤ z.re → 1 ≤ |z.im| →
      ‖primeCorrection z‖ ≤ K * (1 + |z.im|) := by
  have hb := cutoff_bounds hH
  obtain ⟨C, hC, hsep⟩ := M5.exists_sep_bound_nonneg hZ1 hZ2 hZ3
  obtain ⟨T, hT⟩ := M5.norm_sigmaTail_four_le
  let δ := min (2 * remainderAbscissa - Bsup) 1
  have hδ : 0 < δ := lt_min (by linarith [hb.1]) zero_lt_one
  let K3 : ℝ := ∑' m : ℕ, ArithmeticFunction.vonMangoldt m * (m : ℝ) ^ (-(3 * remainderAbscissa))
  have hK3 : 0 ≤ K3 := tsum_nonneg (fun _ => mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity))
  have hvm := vmConst_nonneg
  refine ⟨2 * C / δ + vmConst + K3 + |T|, by positivity, ?_⟩
  intro z hz hy
  have hz0 : 0 < z.re := by linarith [hb.2.1]
  have h2 : ‖negLogDerivZeta (2 * z)‖ ≤ (2 * C / δ + vmConst) * (1 + |z.im|) := by
    by_cases hz2 : (2 * z).re ≤ 2
    · have hB : Bsup < (2 * z).re := by simp only [mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]; linarith [hb.1]
      have hn := zeta_ne_zero_right_of_Bsup hZ1 hB
      have he := hsep (2 * z) (by simp only [mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]; linarith) hz2
        (by simpa only [mul_im, re_ofNat, im_ofNat, zero_mul, add_zero, mul_one, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using mul_le_mul_of_nonneg_left hy (by norm_num : (0 : ℝ) ≤ 2))
        hn δ hδ (min_le_right _ _) (by
          intro ρ hρ _
          have hr := (M1.Bsup_facts hZ1).1 ρ hρ
          have he := (le_abs_self (2 * z.re - ρ.re)).trans (by simpa only [sub_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero] using abs_re_le_norm (2 * z - ρ))
          have hd : δ ≤ 2 * remainderAbscissa - Bsup := min_le_left _ _
          linarith)
      have hl : Real.log (|(2 * z).im| + 3) ≤ 2 * (1 + |z.im|) := by
        simp only [mul_im, re_ofNat, im_ofNat, zero_mul, add_zero, mul_one, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        have := Real.log_le_sub_one_of_pos (show 0 < 2 * |z.im| + 3 by positivity)
        linarith
      calc
        _ ≤ C / δ * Real.log (|(2 * z).im| + 3) := he
        _ ≤ C / δ * (2 * (1 + |z.im|)) := mul_le_mul_of_nonneg_left hl (by positivity)
        _ = (2 * C / δ) * (1 + |z.im|) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hvm) (by positivity)
    · have he := norm_negLogDerivZeta_le (le_of_lt (not_le.mp hz2))
      have hp : (2 : ℝ) ^ (-(2 * z).re) ≤ 1 / 4 := by
        calc
          _ ≤ (2 : ℝ) ^ (-(2 : ℝ)) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          _ = _ := by norm_num
      have hh : ‖negLogDerivZeta (2 * z)‖ ≤ vmConst := he.trans (by nlinarith)
      have hCd : 0 ≤ 2 * C / δ := by positivity
      have hmul := mul_nonneg (add_nonneg hCd hvm) (abs_nonneg z.im)
      exact hh.trans (by nlinarith)
  have h3 : ‖negLogDerivZeta (3 * z)‖ ≤ K3 :=
    M1.norm_negLogDerivZeta_le_of_re (by linarith [hb.2.1]) (by simp only [mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]; linarith)
  have ht := (hT z (by linarith [hb.2.1])).trans (le_abs_self T)
  have hbase := norm_primeCorrection_le_three hz0
  calc
    _ ≤ (2 * C / δ + vmConst) * (1 + |z.im|) + K3 + |T| := by linarith
    _ ≤ _ := by nlinarith [mul_nonneg hK3 (abs_nonneg z.im), mul_nonneg (abs_nonneg T) (abs_nonneg z.im)]

lemma primeCorrection_line_bound (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℝ,
      ‖primeCorrection (remainderAbscissa + y * I)‖ ≤ K * (1 + |y|) := by
  obtain ⟨K, hK, hb⟩ := primeCorrection_strip_bound hH hZ1 hZ2 hZ3
  have hc : Continuous (fun y : ℝ => primeCorrection (remainderAbscissa + y * I)) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    apply (analyticAt_primeCorrection hH hZ1 (by simp) (by
      intro he
      have := congrArg Complex.re he
      simp at this
      linarith [(cutoff_bounds hH).2.2.1])).continuousAt.comp
    fun_prop
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn (hc.continuousOn (s := Icc (-1 : ℝ) 1))
  refine ⟨K + |D|, by positivity, ?_⟩
  intro y
  by_cases hy : 1 ≤ |y|
  · have hh := hb (remainderAbscissa + y * I) (by simp) (by simpa using hy)
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero, zero_add] at hh
    exact hh.trans (by nlinarith [mul_nonneg (abs_nonneg D) (show 0 ≤ 1 + |y| by positivity)])
  · have hh := (hD y (abs_le.mp (not_le.mp hy).le)).trans (le_abs_self D)
    exact hh.trans (by nlinarith [mul_nonneg hK (abs_nonneg y), mul_nonneg (abs_nonneg D) (abs_nonneg y)])

end GoldbachBoundaries.T0HInf
