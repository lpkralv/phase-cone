import GoldbachBoundaries.T0HInf.Defs

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
namespace GoldbachBoundaries.T0HInf
open GoldbachBoundaries Paper2
open _root_.GoldbachBoundaries.Phi2HInf (StirlingStrip)

theorem summable_norm_zeroCoef (hZ1 : Z1) (hZ2 : Z2) :
    Summable (fun ρ : NontrivialZeros => ‖zeroCoef ρ‖) := by
  obtain ⟨Cm, hCm⟩ := M2.zetaMult_le_log hZ1 hZ2
  obtain ⟨K, hK⟩ := TIdentity.norm_Gamma_mul_one_add_abs_im_pow_le (a := 1) (a' := 2)
    (by norm_num) 3
  have hs := M5.summable_zeros_inv_sq hZ1 hZ2
  have hfin : {ρ : NontrivialZeros | |(ρ : ℂ).im| ≤ 1}.Finite := by
    refine ((M1.finite_zeros_abs_im_le 1).preimage
      (Subtype.val_injective (p := fun ρ : ℂ => ρ ∈ NontrivialZeros)).injOn).subset ?_
    intro ρ hρ
    exact ⟨ρ.2, hρ⟩
  have hev : ∀ᶠ ρ : NontrivialZeros in cofinite, 1 < |(ρ : ℂ).im| := by
    rw [Filter.eventually_cofinite]
    simpa only [not_lt] using hfin
  apply (hs.mul_left (4 * |Cm| * |K|)).of_norm_bounded_eventually
  filter_upwards [hev] with ρ hρ
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  set γ := (ρ : ℂ).im with hγ
  have hm := hCm ρ ρ.2
  have hG := hK ((ρ : ℂ) + 1)
    (by simp only [add_re, one_re]; linarith [ρ.2.2.1])
    (by simp only [add_re, one_re]; linarith [ρ.2.2.2])
  have hρ0 : (ρ : ℂ) ≠ 0 := by
    intro he
    have hr := ρ.2.2.1
    rw [he] at hr
    simp at hr
  rw [Gamma_add_one _ hρ0, norm_mul] at hG
  simp only [add_im, one_im, add_zero] at hG
  have hnorm : 1 ≤ ‖(ρ : ℂ)‖ := hρ.le.trans (abs_im_le_norm _)
  have hfilter : ‖(ρ : ℂ) - 1‖ ≤ 2 * ‖(ρ : ℂ)‖ := by
    have h := norm_sub_le (ρ : ℂ) 1
    rw [norm_one] at h
    linarith
  have hGbase : ‖((ρ : ℂ) - 1) * Gamma (ρ : ℂ)‖ *
      (1 + |(ρ : ℂ).im|) ^ 3 ≤ 2 * K := by
    rw [norm_mul]
    calc ‖(ρ : ℂ) - 1‖ * ‖Gamma (ρ : ℂ)‖ * (1 + |(ρ : ℂ).im|) ^ 3
        ≤ 2 * (‖(ρ : ℂ)‖ * ‖Gamma (ρ : ℂ)‖ * (1 + |(ρ : ℂ).im|) ^ 3) := by
          nlinarith [mul_le_mul_of_nonneg_right hfilter
            (mul_nonneg (norm_nonneg (Gamma (ρ : ℂ))) (by positivity : 0 ≤ (1 + |(ρ : ℂ).im|) ^ 3))]
      _ ≤ 2 * K := by linarith
  have hy0 : 0 ≤ |γ| := abs_nonneg _
  have hpos : 0 < 1 + |γ| := by linarith
  have hlog : Real.log (|γ| + 3) ≤ 2 * (1 + |γ|) := by
    have := Real.log_le_sub_one_of_pos (show 0 < |γ| + 3 by positivity)
    linarith
  have hlog0 : 0 ≤ Real.log (|γ| + 3) := Real.log_nonneg (by linarith)
  have hm' : (zetaMult (ρ : ℂ) : ℝ) ≤ |Cm| * (2 * (1 + |γ|)) :=
    hm.trans ((mul_le_mul_of_nonneg_right (le_abs_self Cm) hlog0).trans
      (mul_le_mul_of_nonneg_left hlog (abs_nonneg Cm)))
  have hG' : ‖((ρ : ℂ) - 1) * Gamma (ρ : ℂ)‖ ≤ 2 * |K| / (1 + |γ|) ^ 3 := by
    rw [le_div_iff₀ (by positivity)]
    exact hGbase.trans (by linarith [le_abs_self K])
  have heq : zeroCoef ρ = (zetaMult (ρ : ℂ) : ℂ) * (((ρ : ℂ) - 1) * Gamma (ρ : ℂ)) := by
    unfold zeroCoef Phi2Proof.zeroCoef
    ring
  rw [heq, norm_mul, Complex.norm_natCast]
  calc (zetaMult (ρ : ℂ) : ℝ) * ‖((ρ : ℂ) - 1) * Gamma (ρ : ℂ)‖
      ≤ (|Cm| * (2 * (1 + |γ|))) * (2 * |K| / (1 + |γ|) ^ 3) :=
        mul_le_mul hm' hG' (norm_nonneg _) (by positivity)
    _ = 4 * |Cm| * |K| * (1 / (1 + |γ|) ^ 2) := by field_simp; ring

theorem norm_U_le (hZ1 : Z1) (hZ2 : Z2)
    {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) :
    ‖U x‖ ≤ (∑' ρ : NontrivialZeros, ‖zeroCoef ρ‖) * x⁻¹ := by
  have ha := summable_norm_zeroCoef hZ1 hZ2
  have hbound (ρ : NontrivialZeros) :
      ‖zeroCoef ρ * (x : ℂ) ^ (-(ρ : ℂ))‖ ≤ ‖zeroCoef ρ‖ * x⁻¹ := by
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx.1, neg_re]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_ge hx.1 hx.2 (by linarith [ρ.2.2.2])
  have hmajor := ha.mul_right x⁻¹
  have habs : Summable (fun ρ : NontrivialZeros =>
      ‖zeroCoef ρ * (x : ℂ) ^ (-(ρ : ℂ))‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound hmajor
  calc ‖U x‖ ≤ ∑' ρ : NontrivialZeros,
        ‖zeroCoef ρ * (x : ℂ) ^ (-(ρ : ℂ))‖ := norm_tsum_le_tsum_norm habs
    _ ≤ ∑' ρ : NontrivialZeros, ‖zeroCoef ρ‖ * x⁻¹ := habs.tsum_le_tsum hbound hmajor
    _ = _ := tsum_mul_right

end GoldbachBoundaries.T0HInf
