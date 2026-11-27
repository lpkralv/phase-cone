import GoldbachBoundaries.ResidueClass.LocalLogDerivative
import GoldbachBoundaries.ResidueClass.SelectedHeights

/-! # Bounds for the character average on the positive contour -/

noncomputable section

open Complex Set MeasureTheory

namespace GoldbachBoundaries.ResidueClass

variable {q : ℕ}

/-- Every lower-bounded positive strip has a uniform bound for the Euler
corrections, including primes dividing the conductor. -/
private theorem norm_eulerCorrection_le {δ : ℝ} (hδ : 0 < δ)
    (χ : DirichletCharacter ℂ q) {z : ℂ} (hz : δ ≤ z.re) :
    ‖∑ p ∈ q.primeFactors,
      χ.primitiveCharacter p * (p : ℂ) ^ (-z) * (Real.log p : ℂ) / eulerFactor χ p z‖ ≤
      ∑ p ∈ q.primeFactors, Real.log p / (1 - (p : ℝ) ^ (-δ)) := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p hp ↦ ?_)
  have hp' := Nat.prime_of_mem_primeFactors hp
  have hp₁ : (1 : ℝ) < p := by exact_mod_cast hp'.one_lt
  have hpδ : (p : ℝ) ^ (-δ) < 1 := by
    simpa using Real.rpow_lt_rpow_of_exponent_lt hp₁ (neg_lt_zero.mpr hδ)
  have hlog : 0 ≤ Real.log p := Real.log_nonneg hp₁.le
  have hb : 1 - (p : ℝ) ^ (-δ) ≤ ‖eulerFactor χ p z‖ :=
    one_sub_rpow_le_norm_eulerFactor χ hp' hz
  have ht : ‖χ.primitiveCharacter p * (p : ℂ) ^ (-z)‖ ≤ 1 :=
    (norm_eulerTerm_le χ hp'.pos z).trans ((Real.rpow_le_rpow_of_exponent_le hp₁.le
      (neg_le_neg hz)).trans hpδ.le)
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hlog]
  exact div_le_div_of_nonneg_left hlog (sub_pos.mpr hpδ) hb |>.trans'
    (div_le_div_of_nonneg_right (mul_le_of_le_one_left hlog ht) (norm_nonneg _))

variable [NeZero q]

/-- If a high point is at distance at least `d` from the critical points, the
same local bound holds for the average up to a bounded Euler correction. -/
private theorem exists_norm_D_le_of_separated_of_high_critical {δ : ℝ} (hδ : 0 < δ)
    {T : ℝ}
    (hline : ∀ (χ : DirichletCharacter ℂ q) ρ, ρ ∈ primitiveZeros χ →
      T ≤ |ρ.im| → ρ.re = 1 / 2) (hZ3 : Paper2.Z3) (hLocal : LogDerivPrimitiveLocal q) :
    ∃ A B E T₀ : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 ≤ E ∧ 2 ≤ T₀ ∧ T < T₀ ∧
      ∀ (z : ℂ) (d : ℝ), 0 < d → δ ≤ z.re → z.re ≤ 2 → T₀ ≤ |z.im| →
        (∀ t ∈ Ordinates q, d ≤ ‖z - criticalPoint t‖) →
        ‖D q z‖ ≤ A * Real.log (2 + |z.im|) + B * Real.log (|z.im| + 4) / d + E := by
  obtain ⟨A, B, T₀, hA, hB, hT, hTT, hlog⟩ :=
    exists_norm_logDeriv_primitive_le_of_separated_of_high_critical hline hZ3 hLocal
  let E : ℝ := ∑ p ∈ q.primeFactors, Real.log p / (1 - (p : ℝ) ^ (-δ))
  let K : ℝ := ‖(q.totient : ℂ)⁻¹‖ * Fintype.card (DirichletCharacter ℂ q)
  have hE : 0 ≤ E := (norm_nonneg _).trans (norm_eulerCorrection_le hδ
    (1 : DirichletCharacter ℂ q) (show δ ≤ (δ : ℂ).re by simp))
  have hK : 0 ≤ K := by positivity
  refine ⟨K * A, K * B, K * E, T₀, mul_nonneg hK hA, mul_nonneg hK hB,
    mul_nonneg hK hE, hT, by linarith, fun z d hd hz hz₂ hy hdist ↦ ?_⟩
  have hz₁ : z ≠ 1 := by
    rintro rfl
    simp at hy
    linarith
  have hpoint (χ : DirichletCharacter ℂ q) (ρ : ℂ) (hρ : ρ ∈ primitiveZeros χ)
      (hnear : |ρ.im - z.im| ≤ 1) :
      d ≤ ‖z - ρ‖ := by
    have he : criticalPoint ρ.im = ρ :=
      Complex.ext (by rw [criticalPoint_re, hline χ ρ hρ (by linarith [abs_sub_abs_le_abs_sub z.im ρ.im, abs_sub_comm z.im ρ.im])]) (criticalPoint_im _)
    exact he ▸ hdist ρ.im (mem_Ordinates_iff.mpr ⟨χ, he.symm ▸ hρ⟩)
  have hne (χ : DirichletCharacter ℂ q) : primitiveL χ z ≠ 0 := by
    by_cases hz' : 1 ≤ z.re
    · exact primitiveL_ne_zero_of_one_le_re χ hz'
    · intro h
      have := hpoint χ z ⟨h, hδ.trans_le hz, lt_of_not_ge hz'⟩ (by simp)
      simp at this
      linarith
  rw [D_eq_primitive_average (hδ.trans_le hz) hz₁ hne, norm_mul]
  calc
    _ ≤ ‖(q.totient : ℂ)⁻¹‖ *
        ∑ _χ : DirichletCharacter ℂ q,
          (A * Real.log (2 + |z.im|) + B * Real.log (|z.im| + 4) / d + E) := by
      gcongr
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun χ _ ↦ ?_)
      apply (norm_sub_le _ _).trans
      rw [norm_neg]
      refine add_le_add (hlog χ z d hd (hδ.trans_le hz) hz₂ hy (hne χ) ?_)
        (norm_eulerCorrection_le hδ χ hz)
      exact fun ρ hρ hnear ↦ hpoint χ ρ hρ hnear
    _ = _ := by simp [K]; ring

/-- On the left line each critical point is separated by the real-part gap. -/
theorem analyticAt_D_left_of_left_of_zeros {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 2)
    (hleft : ∀ (χ : DirichletCharacter ℂ q) ρ, ρ ∈ primitiveZeros χ → δ < ρ.re)
    {z : ℂ} (hz : z.re = δ) : AnalyticAt ℂ (D q) z := by
  have hne : z ≠ 1 := by
    rintro rfl
    rw [one_re] at hz
    linarith
  refine analyticAt_D (hz.symm ▸ hδ) hne fun χ h ↦ ?_
  have hh := hleft χ z ⟨h, hz.symm ▸ hδ, by linarith⟩
  linarith

theorem exists_norm_D_left_bound_of_high_critical {T : ℝ}
    (hline : ∀ (χ : DirichletCharacter ℂ q) ρ, ρ ∈ primitiveZeros χ →
      T ≤ |ρ.im| → ρ.re = 1 / 2) (hZ3 : Paper2.Z3)
    (hLocal : LogDerivPrimitiveLocal q) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 2)
    (hleft : ∀ (χ : DirichletCharacter ℂ q) ρ, ρ ∈ primitiveZeros χ → δ < ρ.re) :
    ∃ K : ℝ, ∀ y : ℝ, ‖D q (δ + y * I)‖ ≤ K * (1 + |y|) := by
  obtain ⟨A, B, E, T₀, hA, hB, hE, hT, hTT, hbound⟩ :=
    exists_norm_D_le_of_separated_of_high_critical hδ hline hZ3 hLocal
  let d : ℝ := 1 / 2 - δ
  have hd : 0 < d := sub_pos.mpr hδ'
  have hcont : Continuous (fun y : ℝ ↦ D q (δ + y * I)) := by
    rw [continuous_iff_continuousAt]
    exact fun y ↦ (analyticAt_D_left_of_left_of_zeros hδ hδ' hleft (z := δ + y * I) (by simp)).continuousAt.comp
      (f := fun u : ℝ ↦ (δ : ℂ) + u * I) (by fun_prop)
  obtain ⟨L, hL⟩ := (isCompact_Icc (a := -T₀) (b := T₀)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max L 0 + (2 * A + 4 * (B / d) + E), fun y ↦ ?_⟩
  by_cases hy : T₀ ≤ |y|
  · have hs := hbound ((δ : ℂ) + y * I) d hd (by simp) (by simp; linarith) (by simpa)
        (fun t _ ↦ by
          have h := abs_re_le_norm (((δ : ℂ) + y * I) - criticalPoint t)
          have hr : ((δ : ℂ) + y * I).re = δ := by simp
          rwa [sub_re, hr, criticalPoint_re, abs_of_nonpos (sub_nonpos.mpr hδ'.le), neg_sub] at h)
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
      zero_add] at hs
    have hy₀ : 0 ≤ |y| := abs_nonneg _
    have h1 : Real.log (2 + |y|) ≤ 2 * (1 + |y|) := by
      linarith [Real.log_le_self (show 0 ≤ 2 + |y| by positivity)]
    have h2 : Real.log (|y| + 4) ≤ 4 * (1 + |y|) := by
      linarith [Real.log_le_self (show 0 ≤ |y| + 4 by positivity)]
    refine hs.trans ?_
    calc
      _ ≤ A * (2 * (1 + |y|)) + B * (4 * (1 + |y|)) / d + E * (1 + |y|) := by
        gcongr
        exact le_mul_of_one_le_right hE (by linarith)
      _ = (2 * A + 4 * (B / d) + E) * (1 + |y|) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_left (le_max_right L 0)) (by positivity)
  · have hL₀ : 0 ≤ max L 0 := le_max_right _ _
    have hC₀ : 0 ≤ 2 * A + 4 * (B / d) + E := by positivity
    calc
      _ ≤ L := hL y (abs_le.mp (le_of_lt (lt_of_not_ge hy)))
      _ ≤ max L 0 := le_max_left _ _
      _ ≤ max L 0 + (2 * A + 4 * (B / d) + E) := le_add_of_nonneg_right hC₀
      _ ≤ _ := le_mul_of_one_le_right (add_nonneg hL₀ hC₀) (by linarith [abs_nonneg y])

theorem integrable_Gamma_mul_D_left_of_high_critical {T : ℝ}
    (hline : ∀ (χ : DirichletCharacter ℂ q) ρ, ρ ∈ primitiveZeros χ →
      T ≤ |ρ.im| → ρ.re = 1 / 2) (hZ3 : Paper2.Z3)
    (hLocal : LogDerivPrimitiveLocal q) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 2)
    (hleft : ∀ (χ : DirichletCharacter ℂ q) ρ, ρ ∈ primitiveZeros χ → δ < ρ.re) :
    Integrable fun y : ℝ ↦ Gamma (δ + y * I) * D q (δ + y * I) := by
  obtain ⟨K, hK⟩ := exists_norm_D_left_bound_of_high_critical hline hZ3 hLocal hδ hδ' hleft
  refine TIdentity.integrable_Gamma_mul_of_bound hδ ?_ hK
  rw [continuous_iff_continuousAt]
  exact fun y ↦ (analyticAt_D_left_of_left_of_zeros hδ hδ' hleft (z := δ + y * I) (by simp)).continuousAt.comp
    (f := fun u : ℝ ↦ (δ : ℂ) + u * I) (by fun_prop)

/-- Selected heights avoid every ordinate and bound the average on both
horizontal sides by a quadratic polynomial. -/
theorem exists_D_horizontal_bounds_of_high_critical {T : ℝ}
    (hline : ∀ (χ : DirichletCharacter ℂ q) ρ, ρ ∈ primitiveZeros χ →
      T ≤ |ρ.im| → ρ.re = 1 / 2) (hZ3 : Paper2.Z3)
    (hLocal : LogDerivPrimitiveLocal q) {δ : ℝ} (hδ : 0 < δ) :
    ∃ K Y₀ : ℝ, 0 ≤ K ∧ 2 ≤ Y₀ ∧ T < Y₀ ∧ ∀ Y : ℝ, Y₀ ≤ Y → ∃ H ∈ Icc Y (Y + 1),
      (∀ t ∈ Ordinates q, |t| ≠ H) ∧
      ∀ z : ℂ, δ ≤ z.re → z.re ≤ 2 → |z.im| = H → ‖D q z‖ ≤ K * (1 + H) ^ 2 := by
  obtain ⟨C, hC, hselect⟩ := exists_selected_height_unconditional q
  obtain ⟨A, B, E, T₀, hA, hB, hE, hT, hTT, hbound⟩ :=
    exists_norm_D_le_of_separated_of_high_critical hδ hline hZ3 hLocal
  refine ⟨2 * A + 4 * B * (2 + 6 * C) + E, T₀, by positivity, hT, hTT, fun Y hY ↦ ?_⟩
  obtain ⟨H, hH, hsep⟩ := hselect Y (hT.trans hY)
  have hH₀ : 0 ≤ H := by linarith [hH.1]
  let M := 2 + C * Real.log (Y + 6)
  have hM : 0 < M := by
    have : 0 ≤ Real.log (Y + 6) := Real.log_nonneg (by linarith)
    positivity
  have hd : 0 < 1 / M := by positivity
  have hdist (y : ℝ) (hy : |y| = H) (t : ℝ) (ht : t ∈ Ordinates q) : 1 / M ≤ |y - t| := by
    rcases (abs_eq hH₀).mp hy with rfl | rfl
    · exact (hsep t ht).1
    · exact (hsep t ht).2
  refine ⟨H, hH, fun t ht he ↦ ?_, fun z hz hz₂ hy ↦ ?_⟩
  · have := hdist t he t ht
    simp at this
    linarith
  have hb := hbound z (1 / M) hd hz hz₂ (by rw [hy]; exact hY.trans hH.1)
    (fun t ht ↦ (hdist z.im hy t ht).trans (by
      simpa [sub_im, criticalPoint_im] using abs_im_le_norm (z - criticalPoint t)))
  rw [hy, div_eq_mul_inv _ (1 / M), one_div, inv_inv] at hb
  have h1 : Real.log (2 + H) ≤ 2 * (1 + H) := by
    linarith [Real.log_le_self (show 0 ≤ 2 + H by positivity)]
  have h2 : Real.log (H + 4) ≤ 4 * (1 + H) := by
    linarith [Real.log_le_self (show 0 ≤ H + 4 by positivity)]
  have h3 : Real.log (Y + 6) ≤ 6 * (1 + H) := by
    linarith [Real.log_le_self (show 0 ≤ Y + 6 by linarith), hH.1]
  have hM' : M ≤ (2 + 6 * C) * (1 + H) := by
    dsimp [M]
    nlinarith [mul_le_mul_of_nonneg_left h3 hC]
  have hsq : 1 + H ≤ (1 + H) ^ 2 := by nlinarith
  have hsq' : 1 ≤ (1 + H) ^ 2 := by linarith
  calc
    _ ≤ A * Real.log (2 + H) + B * Real.log (H + 4) * M + E := hb
    _ ≤ A * (2 * (1 + H)) + B * (4 * (1 + H)) * ((2 + 6 * C) * (1 + H)) + E := by gcongr
    _ = (2 * A) * (1 + H) + (4 * B * (2 + 6 * C)) * (1 + H) ^ 2 + E * 1 := by ring
    _ ≤ _ := by rw [add_mul, add_mul]; gcongr

theorem analyticAt_D_left (hGRH : GRH q) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 2)
    {z : ℂ} (hz : z.re = δ) : AnalyticAt ℂ (D q) z :=
  analyticAt_D_left_of_left_of_zeros hδ hδ' (fun χ ρ hρ ↦ by rw [hGRH χ ρ hρ]; exact hδ') hz

theorem exists_norm_D_left_bound (hGRH : GRH q) (hZ3 : Paper2.Z3)
    (hLocal : LogDerivPrimitiveLocal q) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 2) :
    ∃ K : ℝ, ∀ y : ℝ, ‖D q (δ + y * I)‖ ≤ K * (1 + |y|) :=
  exists_norm_D_left_bound_of_high_critical (T := 0) (fun χ ρ hρ _ ↦ hGRH χ ρ hρ) hZ3 hLocal hδ hδ' (fun χ ρ hρ ↦ by rw [hGRH χ ρ hρ]; exact hδ')

theorem integrable_Gamma_mul_D_left (hGRH : GRH q) (hZ3 : Paper2.Z3)
    (hLocal : LogDerivPrimitiveLocal q) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 2) :
    Integrable fun y : ℝ ↦ Gamma (δ + y * I) * D q (δ + y * I) :=
  integrable_Gamma_mul_D_left_of_high_critical (T := 0) (fun χ ρ hρ _ ↦ hGRH χ ρ hρ) hZ3 hLocal hδ hδ' (fun χ ρ hρ ↦ by rw [hGRH χ ρ hρ]; exact hδ')

theorem exists_D_horizontal_bounds (hGRH : GRH q) (hZ3 : Paper2.Z3)
    (hLocal : LogDerivPrimitiveLocal q) {δ : ℝ} (hδ : 0 < δ) :
    ∃ K Y₀ : ℝ, 0 ≤ K ∧ 2 ≤ Y₀ ∧ ∀ Y : ℝ, Y₀ ≤ Y → ∃ H ∈ Icc Y (Y + 1),
      (∀ t ∈ Ordinates q, |t| ≠ H) ∧
      ∀ z : ℂ, δ ≤ z.re → z.re ≤ 2 → |z.im| = H → ‖D q z‖ ≤ K * (1 + H) ^ 2 := by
  obtain ⟨K, Y₀, hK, hY, _, h⟩ := exists_D_horizontal_bounds_of_high_critical
    (T := 0) (fun χ ρ hρ _ ↦ hGRH χ ρ hρ) hZ3 hLocal hδ
  exact ⟨K, Y₀, hK, hY, h⟩

private theorem exists_norm_D_le_of_separated {δ : ℝ} (hδ : 0 < δ)
    (hGRH : GRH q) (hZ3 : Paper2.Z3) (hLocal : LogDerivPrimitiveLocal q) :
    ∃ A B E T₀ : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 ≤ E ∧ 2 ≤ T₀ ∧
      ∀ (z : ℂ) (d : ℝ), 0 < d → δ ≤ z.re → z.re ≤ 2 → T₀ ≤ |z.im| →
        (∀ t ∈ Ordinates q, d ≤ ‖z - criticalPoint t‖) →
        ‖D q z‖ ≤ A * Real.log (2 + |z.im|) + B * Real.log (|z.im| + 4) / d + E := by
  obtain ⟨A, B, E, T₀, hA, hB, hE, hT, _, h⟩ := exists_norm_D_le_of_separated_of_high_critical hδ
    (T := 0) (fun χ ρ hρ _ ↦ hGRH χ ρ hρ) hZ3 hLocal
  exact ⟨A, B, E, T₀, hA, hB, hE, hT, h⟩

end GoldbachBoundaries.ResidueClass
