import GoldbachBoundaries.T0HInf.GammaIntegrals

/-! Shift the prime/Lambda correction past its unique prime-square pole. -/
noncomputable section
open Complex Filter Topology Set Metric MeasureTheory Asymptotics
open scoped Interval
namespace GoldbachBoundaries.T0HInf
open GoldbachBoundaries Paper2

def correctionKernel (x : ℝ) (z : ℂ) : ℂ := (x : ℂ) ^ (-z) * (Gamma z * primeCorrection z)

def correctionIntegral (x : ℝ) : ℂ := VerticalIntegral' (correctionKernel x) remainderAbscissa

lemma norm_correctionKernel_horizontal (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3)
    {x : ℝ} (hx : 0 < x) :
    ∃ K : ℝ, ∀ y : ℝ, 1 ≤ |y| → ∀ b ∈ Icc remainderAbscissa 2,
      ‖correctionKernel x (b + y * I)‖ ≤ K * (1 + |y|)⁻¹ := by
  have ha : 0 < remainderAbscissa := by linarith [(cutoff_bounds hH).2.1]
  obtain ⟨C, hC, hb⟩ := primeCorrection_strip_bound hH hZ1 hZ2 hZ3
  obtain ⟨G, hG⟩ := TIdentity.norm_Gamma_mul_one_add_abs_im_pow_le
    (a := remainderAbscissa) (a' := 2) ha 2
  let T : ℝ := x ^ (1 / 2 : ℝ) + x ^ (-(2 : ℝ))
  have hT : 0 ≤ T := by positivity
  refine ⟨T * C * G, ?_⟩
  intro y hy b hbb
  have hpow : ‖(x : ℂ) ^ (-((b : ℂ) + y * I))‖ ≤ T := by
    rw [norm_cpow_eq_rpow_re_of_pos hx]
    simp only [neg_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_self, add_zero]
    convert Phi2HInf.regularized_rpow_neg_le hx (show -(1 / 2) ≤ b by linarith [hbb.1]) hbb.2 using 1 <;> norm_num [T]
  have hgam := hG (b + y * I) (by simpa using hbb.1) (by simpa using hbb.2)
  have hcor := hb (b + y * I) (by simpa using hbb.1) (by simpa using hy)
  simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero, zero_add] at hgam hcor
  rw [← div_eq_mul_inv, le_div_iff₀ (show 0 < 1 + |y| by positivity)]
  simp only [correctionKernel, norm_mul]
  calc
    _ ≤ T * (‖Gamma (b + y * I)‖ * (C * (1 + |y|))) * (1 + |y|) := by gcongr
    _ = T * C * (‖Gamma (b + y * I)‖ * (1 + |y|) ^ 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hgam (mul_nonneg hT hC)

lemma tendsto_correction_horizontal (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3)
    {x : ℝ} (hx : 0 < x) {l : Filter ℝ} (hl : Tendsto (fun y : ℝ => |y|) l atTop) :
    Tendsto (fun y : ℝ => ∫ b in remainderAbscissa..2, correctionKernel x (b + y * I)) l (𝓝 0) := by
  obtain ⟨K, hK⟩ := norm_correctionKernel_horizontal hH hZ1 hZ2 hZ3 hx
  have hlim : Tendsto (fun y : ℝ => K * (1 + |y|)⁻¹ * |2 - remainderAbscissa|) l (𝓝 0) := by
    have hi : Tendsto (fun y : ℝ => (1 + |y|)⁻¹) l (𝓝 0) :=
      (tendsto_atTop_add_const_left _ 1 hl).inv_tendsto_atTop
    simpa using (hi.const_mul K).mul_const |2 - remainderAbscissa|
  apply squeeze_zero_norm' _ hlim
  filter_upwards [hl.eventually (eventually_ge_atTop 1)] with y hy
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro b hb
  rw [uIoc_of_le (show remainderAbscissa ≤ 2 by linarith [(cutoff_bounds hH).2.2.1])] at hb
  exact hK y hy b ⟨hb.1.le, hb.2⟩

lemma correctionKernel_pole {x : ℝ} (hx : 0 < x) :
    (correctionKernel x - fun z => (-(Real.sqrt Real.pi : ℂ) / 2 *
      (x : ℂ) ^ (-(1 / 2 : ℂ))) / (z - 1 / 2)) =O[𝓝[≠] (1 / 2 : ℂ)] (1 : ℂ → ℂ) := by
  have hm := meromorphicAt_primeCorrection (z := 1 / 2) (by norm_num)
  have hr := hasResidue_primeCorrection
  have ho := hr.meromorphicOrderAt_eq_neg_one hm (by norm_num : -(1 / 2 : ℂ) ≠ 0)
  have hg : AnalyticAt ℂ (fun z : ℂ => (x : ℂ) ^ (-z) * Gamma z) (1 / 2) :=
    (show AnalyticAt ℂ (fun z : ℂ => (x : ℂ) ^ (-z)) (1 / 2) from
      (by
        exact (show Differentiable ℂ (fun z : ℂ => (x : ℂ) ^ (-z)) from
          fun z => TIdentity.differentiableAt_ofReal_cpow_neg hx z).analyticAt _)).mul ((show DifferentiableOn ℂ Gamma (halfPlane 0) from
        fun z hz => (TIdentity.differentiableAt_Gamma_of_re_pos hz).differentiableWithinAt).analyticAt
          ((isOpen_halfPlane 0).mem_nhds (by change (0 : ℝ) < (1 / 2 : ℂ).re; norm_num)))
  have hb := M4b.isBigO_mul_sub_residue hm (by rw [ho]; norm_num) hr hg
  convert! hb using 1
  ext z
  simp only [Pi.sub_apply, correctionKernel, Gamma_one_half_eq]
  rw [Real.sqrt_eq_rpow, ofReal_cpow Real.pi_nonneg]
  norm_num only [ofReal_div, ofReal_one, ofReal_ofNat]
  ring

lemma correction_contour_shift (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3)
    {x : ℝ} (hx : 0 < x) :
    VerticalIntegral' (correctionKernel x) 2 =
      -(Real.sqrt Real.pi : ℂ) / 2 * (x : ℂ) ^ (-(1 / 2 : ℂ)) + correctionIntegral x := by
  have hb := cutoff_bounds hH
  apply TIdentity.verticalIntegral'_eq_add_of_simplePole (p := 1 / 2)
    (A := -(Real.sqrt Real.pi : ℂ) / 2 * (x : ℂ) ^ (-(1 / 2 : ℂ)))
    ⟨by simpa using hb.2.2.1, by norm_num⟩ _ (correctionKernel_pole hx)
    (tendsto_correction_horizontal hH hZ1 hZ2 hZ3 hx tendsto_abs_atBot_atTop)
    (tendsto_correction_horizontal hH hZ1 hZ2 hZ3 hx tendsto_abs_atTop_atTop)
    (integrable_inverse_kernel (σ := remainderAbscissa) (f := fun z => Gamma z * primeCorrection z) hx (integrable_Gamma_primeCorrection hH hZ1 hZ2 hZ3))
    (integrable_inverse_kernel (σ := 2) (f := fun z => Gamma z * primeCorrection z) hx integrable_Gamma_primeCorrection_two)
  rintro z ⟨hz, hzhalf⟩
  obtain ⟨hzlo, hzhi⟩ := (mem_reProdIm.mp hz).1
  have hz0 : 0 < z.re := by linarith [hb.2.1]
  exact ((TIdentity.differentiableAt_ofReal_cpow_neg hx _).mul
    ((TIdentity.differentiableAt_Gamma_of_re_pos hz0).mul
      (analyticAt_primeCorrection hH hZ1 hzlo hzhalf).differentiableAt)).differentiableWithinAt

end GoldbachBoundaries.T0HInf
