import GoldbachBoundaries.ResidueClass.ContourShift
import GoldbachBoundaries.ResidueClass.MellinSquare
import GoldbachBoundaries.ResidueClass.CauchySquare
import GoldbachBoundaries.ResidueClass.Correction

/-! # The binary Mellin identity and meromorphic continuation -/

noncomputable section

open Complex Filter Set MeasureTheory

namespace GoldbachBoundaries.ResidueClass

open TIdentity (integral_Ioc_cpow_of_neg_one_lt integrableOn_Ioc_cpow_of_neg_one_lt
  differentiableOn_integral_Ioc_cpow differentiable_integral_Ioi_cpow ofReal_cpow_add_one)

variable {q : ℕ} [NeZero q]

/-- The smoothed sum with its principal term removed. -/
def smoothedResidual (q : ℕ) (x : ℝ) : ℂ :=
  (smoothed q x : ℂ) - principalWeight q / (x : ℂ)

omit [NeZero q] in
theorem continuousOn_smoothedResidual : ContinuousOn (smoothedResidual q) (Ioi 0) :=
  (continuous_ofReal.comp_continuousOn (continuousOn_smoothed q)).sub
    (continuousOn_const.div continuous_ofReal.continuousOn
      (fun _ hx ↦ ofReal_ne_zero.mpr (ne_of_gt (mem_Ioi.mp hx))))

/-- The Mellin integral from one to infinity of a power of the smoothed sum. -/
def tailMellin (q k : ℕ) (s : ℂ) : ℂ :=
  ∫ x in Ioi (1 : ℝ), (smoothed q x : ℂ)^k * (x : ℂ) ^ (s - 1)

omit [NeZero q] in
theorem differentiable_tailMellin {k : ℕ} (hk : 1 ≤ k) :
    Differentiable ℂ (tailMellin q k) := by
  obtain ⟨C, hC, h⟩ := exists_smoothed_le_exp q
  apply differentiable_integral_Ioi_cpow (C := C ^ k)
  · exact ((continuous_ofReal.comp_continuousOn ((continuousOn_smoothed q).mono
      (Ioi_subset_Ioi zero_le_one))).pow k).aestronglyMeasurable measurableSet_Ioi
  · intro x hx
    have hx₁ : 1 ≤ x := le_of_lt hx
    have h₁ := pow_le_pow_left₀ (smoothed_nonneg q x) (h x hx₁) k
    have he : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg (smoothed_nonneg q x)]
    calc
      _ ≤ C ^ k * Real.exp (-x) ^ k := by simpa only [mul_pow] using h₁
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (by simpa using pow_le_pow_of_le_one (Real.exp_pos (-x)).le he hk) (pow_nonneg hC _)

/-- Subtracting the zero square leaves two terms with at least one
positive-line contour factor. -/
def smallRemainder (q : ℕ) [NeZero q] (x : ℝ) : ℂ :=
  smoothedResidual q x ^ 2 - zeroTerm q x ^ 2

private theorem smallRemainder_meas :
    AEStronglyMeasurable (smallRemainder q) (volume.restrict (Ioc 0 1)) :=
  (((continuousOn_smoothedResidual (q := q)).mono Ioc_subset_Ioi_self).pow 2).aestronglyMeasurable
    measurableSet_Ioc |>.sub (aestronglyMeasurable_zeroTerm.pow 2)

theorem exists_norm_smallRemainder_bound (hGRH : GRH q) (hZ3 : Paper2.Z3)
    (hLocal : LogDerivPrimitiveLocal q) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 2) :
    ∃ C : ℝ, ∀ x ∈ Ioc (0 : ℝ) 1, ‖smallRemainder q x‖ ≤ C * x ^ (-(1 / 2 + δ)) := by
  obtain ⟨K, hK, hR⟩ := norm_lineRemainder_le q δ
  let Z := ∑' t : Ordinates q, ‖gammaWeight q t‖
  have hZ : 0 ≤ Z := tsum_nonneg fun _ ↦ norm_nonneg _
  refine ⟨2 * Z * K + K ^ 2, fun x hx ↦ ?_⟩
  have hF := smoothed_explicit_formula hGRH hZ3 hLocal hδ hδ' hx.1
  have he : smallRemainder q x = -(2 * zeroTerm q x * lineRemainder q δ x) +
      lineRemainder q δ x ^ 2 := by
    rw [smallRemainder, smoothedResidual, hF]
    ring
  rw [he]
  calc
    _ ≤ 2 * ‖zeroTerm q x‖ * ‖lineRemainder q δ x‖ + ‖lineRemainder q δ x‖ ^ 2 := by
      simpa only [norm_neg, norm_mul, Complex.norm_ofNat, norm_pow] using norm_add_le (-(2 * zeroTerm q x * lineRemainder q δ x))
        (lineRemainder q δ x ^ (2 : ℕ))
    _ ≤ 2 * (Z * x ^ (-(1 / 2 : ℝ))) * (K * x ^ (-δ)) + (K * x ^ (-δ)) ^ 2 := by
      have hRₓ := hR x hx.1
      have hZₓ := norm_zeroTerm_le hGRH hx.1
      exact add_le_add
        (mul_le_mul (mul_le_mul_of_nonneg_left hZₓ (by norm_num)) hRₓ (norm_nonneg _)
            (mul_nonneg (by norm_num) (mul_nonneg hZ (Real.rpow_nonneg hx.1.le _))))
        (pow_le_pow_left₀ (norm_nonneg _) hRₓ _)
    _ = (2 * Z * K) * x ^ (-(1 / 2 + δ)) + K ^ 2 * x ^ (-(δ + δ)) := by
      rw [mul_pow, ← Real.rpow_mul_natCast hx.1.le, show -δ * (↑(2 : ℕ) : ℝ) = -(δ + δ) by simp; ring]
      have he : x ^ (-(1 / 2 : ℝ)) * x ^ (-δ) = x ^ (-(1 / 2 + δ)) := by
        rw [← Real.rpow_add hx.1]
        congr 1
        ring
      rw [← he]
      ring
    _ ≤ _ := by
      rw [add_mul]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_ge hx.1 hx.2 (by linarith : -(1 / 2 + δ) ≤ -(δ + δ)))
          (sq_nonneg K))

def holomorphicCorrection (q : ℕ) [NeZero q] (s : ℂ) : ℂ :=
  (∫ x in Ioc (0 : ℝ) 1, smallRemainder q x * (x : ℂ) ^ (s - 1)) +
    tailMellin q 2 s - 2 * principalWeight q * tailMellin q 1 (s - 1)

theorem differentiableOn_holomorphicCorrection (hGRH : GRH q) (hZ3 : Paper2.Z3)
    (hLocal : LogDerivPrimitiveLocal q) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 2) :
    DifferentiableOn ℂ (holomorphicCorrection q) (halfPlane (1 / 2 + δ)) := by
  obtain ⟨C, hC⟩ := exists_norm_smallRemainder_bound hGRH hZ3 hLocal hδ hδ'
  have hsmall := differentiableOn_integral_Ioc_cpow smallRemainder_meas hC
  have htail : Differentiable ℂ (fun s ↦ 2 * principalWeight q * tailMellin q 1 (s - 1)) :=
    ((differentiable_tailMellin (q := q) le_rfl).comp (differentiable_id.sub_const _)).const_mul _
  exact (hsmall.add (differentiable_tailMellin (by omega)).differentiableOn).sub htail.differentiableOn

/-- Completion of the linear Mellin term gives the correction `W`. -/
theorem Gamma_mul_Phi2_eq (hGRH : GRH q) (hZ3 : Paper2.Z3) (hLocal : LogDerivPrimitiveLocal q)
    {s : ℂ} (hs : 2 < s.re) :
    Gamma s * Phi2 q s = W q s + cauchySquare q s + holomorphicCorrection q s := by
  have hs₁ : 1 < (s - 1).re := by simp; linarith
  obtain ⟨hFs, hFsV⟩ := mellin_smoothed_sq q hs
  obtain ⟨hF, hFV⟩ := mellin_smoothed q hs₁
  have hF' : IntegrableOn (fun x : ℝ ↦ (smoothed q x : ℂ) * (x : ℂ) ^ (s - 1 - 1)) (Ioi 0) := by
    simpa only [MellinConvergent, smul_eq_mul, mul_comm] using hF
  have hFV' : (∫ x in Ioi (0 : ℝ), (smoothed q x : ℂ) * (x : ℂ) ^ (s - 1 - 1)) =
      Gamma (s - 1) * D q (s - 1) := by
    simpa only [mellin, smul_eq_mul, mul_comm] using hFV
  have hI : Ioc (0 : ℝ) 1 ⊆ Ioi 0 := Ioc_subset_Ioi_self
  have hJ : Ioi (1 : ℝ) ⊆ Ioi 0 := Ioi_subset_Ioi zero_le_one
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 from zero_le_one),
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi (hFs.mono_set hI) (hFs.mono_set hJ)] at hFsV
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 from zero_le_one),
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi (hF'.mono_set hI) (hF'.mono_set hJ)] at hFV'
  obtain ⟨hZ, hZV⟩ := integral_zeroTerm_sq hGRH (show 1 < s.re by linarith)
  obtain ⟨C, hC⟩ := exists_norm_smallRemainder_bound hGRH hZ3 hLocal
    (δ := 1 / 4) (by norm_num) (by norm_num)
  have hR := Phi2Proof.C_integrableOn_mellin smallRemainder_meas hC (s := s) (by linarith)
  have hpow : -1 < (s - 3).re := by simp; linarith
  let c := principalWeight q
  have hpI (x : ℝ) (hx : x ∈ Ioc (0 : ℝ) 1) :
      (smoothed q x : ℂ)^2 * (x : ℂ) ^ (s - 1) =
        (zeroTerm q x ^ 2 * (x : ℂ) ^ (s - 1) + smallRemainder q x * (x : ℂ) ^ (s - 1)) +
          2 * c * ((smoothed q x : ℂ) * (x : ℂ) ^ (s - 1 - 1)) - c^2 * (x : ℂ) ^ (s - 3) := by
    have hn : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.1.ne'
    have h₁ : (x : ℂ) ^ (s - 1 - 1) = (x : ℂ) ^ (s - 3) * x := by
      rw [← ofReal_cpow_add_one hx.1]
      congr 1
      ring
    have h₂ : (x : ℂ) ^ (s - 1) = (x : ℂ) ^ (s - 3) * x * x := by
      rw [← h₁, ← ofReal_cpow_add_one hx.1]
      congr 1
      ring
    rw [h₁, h₂]
    simp only [smallRemainder, smoothedResidual, c]
    field_simp
    ring
  have hFsmall := (hF'.mono_set hI).const_mul (2 * c)
  have hPsmall := (integrableOn_Ioc_cpow_of_neg_one_lt hpow).const_mul (c ^ 2)
  have hIntegral := integral_sub ((hZ.add hR).add hFsmall) hPsmall
  simp only [Pi.add_apply] at hIntegral
  rw [setIntegral_congr_fun measurableSet_Ioc hpI, hIntegral] at hFsV
  have hAdd₁ := integral_add (hZ.add hR) hFsmall
  have hAdd₂ := integral_add hZ hR
  simp only [Pi.add_apply] at hAdd₁ hAdd₂
  rw [hAdd₁, hAdd₂, integral_const_mul, integral_const_mul, hZV,
    integral_Ioc_cpow_of_neg_one_lt hpow] at hFsV
  rw [W, holomorphicCorrection, ← hFV', ← hFsV]
  rw [show s - 3 + 1 = s - 2 by ring]
  simp only [c, tailMellin, pow_one, div_eq_mul_inv]
  ring

/-- Normalized binary continuation on the right of the line of pair poles. -/
def phi2Continuation (q : ℕ) [NeZero q] (s : ℂ) : ℂ :=
  (Gamma s)⁻¹ * (W q s + cauchySquare q s + holomorphicCorrection q s)

theorem meromorphicOn_phi2Continuation (hGRH : GRH q) (hZ3 : Paper2.Z3)
    (hLocal : LogDerivPrimitiveLocal q) : MeromorphicOn (phi2Continuation q) HH := by
  intro s hs
  have hs' : 1 < s.re := hs
  have hC := (differentiableOn_cauchySquare hGRH).analyticAt ((isOpen_halfPlane 1).mem_nhds hs)
  have hH := (differentiableOn_holomorphicCorrection hGRH hZ3 hLocal
    (δ := 1 / 4) (by norm_num) (by norm_num)).analyticAt
      ((isOpen_halfPlane _).mem_nhds (show 1 / 2 + 1 / 4 < s.re by linarith))
  exact (PhiRProof.analyticAt_inv_Gamma s).meromorphicAt.mul
    (((meromorphic_W q s).add hC.meromorphicAt).add hH.meromorphicAt)

theorem eqOn_phi2Continuation (hGRH : GRH q) (hZ3 : Paper2.Z3) (hLocal : LogDerivPrimitiveLocal q) :
    EqOn (phi2Continuation q) (Phi2 q) (halfPlane 2) := by
  intro s hs
  have hs' : 2 < s.re := hs
  rw [phi2Continuation, ← Gamma_mul_Phi2_eq hGRH hZ3 hLocal hs', ← mul_assoc,
    inv_mul_cancel₀ (Gamma_ne_zero_of_re_pos (by linarith)), one_mul]

end GoldbachBoundaries.ResidueClass
