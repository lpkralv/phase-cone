import GoldbachBoundaries.Paper2.M3.Fill.tendsto_mul_Theta

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
namespace GoldbachBoundaries.Paper2.M3
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- `∫_0^1 (a t^{x-3} + K) dt = a/(x-2) + K` for `x > 2`, with integrability. -/
lemma cc_integral_bound {x : ℝ} (hx : 2 < x) (a K : ℝ) :
    IntegrableOn (fun t : ℝ => a * t ^ (x - 3) + K) (Ioc (0 : ℝ) 1) ∧
      ∫ t in Ioc (0 : ℝ) 1, (a * t ^ (x - 3) + K) = a / (x - 2) + K := by
  have hr : (-1 : ℝ) < x - 3 := by linarith
  have hii : IntervalIntegrable (fun t : ℝ => t ^ (x - 3)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' hr
  have hI : IntegrableOn (fun t : ℝ => t ^ (x - 3)) (Ioc (0 : ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 hii
  have hK : IntegrableOn (fun _ : ℝ => K) (Ioc (0 : ℝ) 1) := integrableOn_const (by simp)
  refine ⟨(hI.const_mul a).add hK, ?_⟩
  rw [integral_add (hI.const_mul a) hK, integral_const_mul, ← intervalIntegral.integral_of_le zero_le_one,
    integral_rpow (Or.inl hr)]
  simp only [setIntegral_const, Real.volume_real_Ioc, sub_zero,
    smul_eq_mul]
  have h1 : x - 3 + 1 = x - 2 := by ring
  rw [h1, Real.one_rpow, Real.zero_rpow (by linarith)]
  norm_num
  field_simp

/-- **`(s - 2)𝓜(s) → 0` as `s ↓ 2`** (from `tendsto_mul_Theta`). `h(t) = (tΘ(t) - 1)/t = o(1/t)`: given `ε`, take
`t_ε ∈ (0, 1)` with `|h(t)| ≤ ε/t` on `(0, t_ε]`; for real `x ∈ (2, 3)`,
`0 ≤ (x-2)𝓜(x) ≤ ε²(x-2)∫_0^{t_ε} t^{x-3} dt + (x-2)∫_{t_ε}^1 h² t^{x-1} ≤ ε² + (x-2) max_{[t_ε,1]} h²`
(`hErr` is continuous on `[t_ε, 1]`, `TIdentity.continuousOn_hErr`). `𝓜(x)` is real and the integral is the
`Ioc 0 1` integral of `Mcal`. Size: 100–200 lines. -/
theorem tendsto_sub_two_mul_Mcal :
    Tendsto (fun x : ℝ => ((x : ℂ) - 2) * Mcal x) (𝓝[>] 2) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  set ε : ℝ := min 1 (η / 2) with hεdef
  have hε0 : 0 < ε := lt_min one_pos (by linarith)
  have hε2 : ε ^ 2 ≤ η / 2 := by
    have h1 : ε ≤ 1 := min_le_left _ _
    have h2 : ε ≤ η / 2 := min_le_right _ _
    nlinarith
  obtain ⟨δ, hδ, hδt⟩ := Metric.tendsto_nhdsWithin_nhds.1 tendsto_mul_Theta ε hε0
  set t₁ : ℝ := min (δ / 2) (1 / 2) with ht₁
  have ht₁0 : 0 < t₁ := lt_min (by linarith) (by norm_num)
  have ht₁δ : t₁ < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  -- `|t h(t)| < ε` on `(0, t₁]`
  have hsmall : ∀ t : ℝ, 0 < t → t ≤ t₁ → |t * hErr t| < ε := by
    intro t ht htt
    have := hδt (mem_Ioi.2 ht) (by rw [Real.dist_eq, sub_zero, abs_of_pos ht]; linarith)
    rw [Real.dist_eq] at this
    have heq : t * hErr t = t * Theta t - 1 := by
      unfold hErr; field_simp
    rw [heq]; exact this
  -- `h` is bounded on `[t₁, 1]`
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := t₁) (b := 1)).exists_bound_of_continuousOn
    (TIdentity.continuousOn_hErr.mono fun t ht => lt_of_lt_of_le ht₁0 ht.1)
  set K : ℝ := B ^ 2 with hK
  have hK0 : 0 ≤ K := sq_nonneg _
  -- the pointwise bound
  have hpt : ∀ x : ℝ, 2 < x → ∀ t ∈ Ioc (0 : ℝ) 1, hErr t ^ 2 * t ^ (x - 1) ≤ ε ^ 2 * t ^ (x - 3) + K := by
    intro x hx t ht
    have ht0 : 0 < t := ht.1
    have hpow : t ^ (x - 1) = t ^ (x - 3) * t ^ 2 := by
      rw [show x - 1 = (x - 3) + 2 by ring, Real.rpow_add ht0]
      norm_cast
    have hp3 : 0 ≤ t ^ (x - 3) := Real.rpow_nonneg ht0.le _
    by_cases htt : t ≤ t₁
    · have h1 := hsmall t ht0 htt
      have h2 : (t * hErr t) ^ 2 ≤ ε ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1.le 2
      calc hErr t ^ 2 * t ^ (x - 1) = (t * hErr t) ^ 2 * t ^ (x - 3) := by rw [hpow]; ring
        _ ≤ ε ^ 2 * t ^ (x - 3) := mul_le_mul_of_nonneg_right h2 hp3
        _ ≤ ε ^ 2 * t ^ (x - 3) + K := le_add_of_nonneg_right hK0
    · push Not at htt
      have hb := hB t ⟨htt.le, ht.2⟩
      rw [Real.norm_eq_abs] at hb
      have h1 : hErr t ^ 2 ≤ K := by
        rw [hK, ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hb 2
      have h2 : t ^ (x - 1) ≤ 1 := Real.rpow_le_one ht0.le ht.2 (by linarith)
      have h3 : hErr t ^ 2 * t ^ (x - 1) ≤ K :=
        (mul_le_mul h1 h2 (Real.rpow_nonneg ht0.le _) hK0).trans_eq (mul_one K)
      linarith [mul_nonneg (sq_nonneg ε) hp3]
  -- eventually `(x - 2) K < η / 2`
  have hev : Ioo (2 : ℝ) (2 + η / (2 * (K + 1))) ∈ 𝓝[>] (2 : ℝ) :=
    Ioo_mem_nhdsGT (by have : 0 < η / (2 * (K + 1)) := by positivity
                       linarith)
  filter_upwards [hev] with x hx
  have hx2 : 2 < x := hx.1
  obtain ⟨hint, hval⟩ := cc_integral_bound hx2 (ε ^ 2) K
  have hnormM : ‖Mcal x‖ ≤ ε ^ 2 / (x - 2) + K := by
    rw [← hval]
    unfold Mcal
    refine norm_integral_le_of_norm_le hint ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_
    have ht0 : 0 < t := ht.1
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _),
      Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    have hre : ((x : ℂ) - 1).re = x - 1 := by simp
    rw [hre]
    exact hpt x hx2 t ht
  rw [dist_zero_right, norm_mul]
  have hn2 : ‖(x : ℂ) - 2‖ = x - 2 := by
    rw [show (x : ℂ) - 2 = ((x - 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
  rw [hn2]
  have hxK : (x - 2) * K < η / 2 := by
    have h1 : x - 2 < η / (2 * (K + 1)) := by linarith [hx.2]
    have h2 : (x - 2) * (K + 1) < η / 2 := by
      calc (x - 2) * (K + 1) < η / (2 * (K + 1)) * (K + 1) :=
            mul_lt_mul_of_pos_right h1 (by linarith)
        _ = η / 2 := by field_simp
    nlinarith
  calc (x - 2) * ‖Mcal x‖ ≤ (x - 2) * (ε ^ 2 / (x - 2) + K) :=
        mul_le_mul_of_nonneg_left hnormM (by linarith)
    _ = ε ^ 2 + (x - 2) * K := by
        have hx0 : x - 2 ≠ 0 := (show (0 : ℝ) < x - 2 by linarith).ne'
        field_simp
    _ < η := by linarith

end GoldbachBoundaries.Paper2.M3
