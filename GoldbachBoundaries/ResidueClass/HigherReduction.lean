import GoldbachBoundaries.ResidueClass.BinaryBoundary

/-! # Reduction of the higher residue-class series to the binary continuation -/

noncomputable section

open Complex Filter Set MeasureTheory Topology

namespace GoldbachBoundaries.ResidueClass

variable {q : ℕ} [NeZero q]

def principalTerm (q : ℕ) (x : ℝ) : ℂ := principalWeight q / (x : ℂ)

/-- The contribution of monomials containing at least three residual factors. -/
def higherTail (q r : ℕ) (x : ℝ) : ℂ :=
  ∑ j ∈ Finset.Ico 3 (r + 1), (r.choose j : ℂ) *
    principalTerm q x ^ (r - j) * smoothedResidual q x ^ j

private theorem norm_smoothedResidual_le (hGRH : GRH q) (hZ3 : Paper2.Z3)
    (hLocal : LogDerivPrimitiveLocal q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Ioc (0 : ℝ) 1, ‖smoothedResidual q x‖ ≤ C * x ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨K, hK, hR⟩ := norm_lineRemainder_le q (1 / 4)
  let Z := ∑' t : Ordinates q, ‖gammaWeight q t‖
  have hZ : 0 ≤ Z := tsum_nonneg fun _ ↦ norm_nonneg _
  refine ⟨Z + K, add_nonneg hZ hK, fun x hx ↦ ?_⟩
  have hF := smoothed_explicit_formula hGRH hZ3 hLocal (δ := 1 / 4) (by norm_num) (by norm_num) hx.1
  have he : smoothedResidual q x = -zeroTerm q x + lineRemainder q (1 / 4) x := by
    rw [smoothedResidual, hF]
    ring
  rw [he, add_mul]
  refine (norm_add_le _ _).trans ?_
  rw [norm_neg]
  exact add_le_add (norm_zeroTerm_le hGRH hx.1) ((hR x hx.1).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hx.1 hx.2 (by norm_num)) hK))

private theorem higherTail_meas (q r : ℕ) :
    AEStronglyMeasurable (higherTail q r) (volume.restrict (Ioc 0 1)) := by
  have hg : ContinuousOn (principalTerm q) (Ioc (0 : ℝ) 1) :=
    continuousOn_const.div continuous_ofReal.continuousOn (fun _ hx ↦ ofReal_ne_zero.mpr hx.1.ne')
  have hu : ContinuousOn (smoothedResidual q) (Ioc (0 : ℝ) 1) :=
    (continuousOn_smoothedResidual (q := q)).mono Ioc_subset_Ioi_self
  apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioc
  exact continuousOn_finsetSum _ fun j _ ↦
    ((continuousOn_const.mul (hg.pow _)).mul (hu.pow j))

private theorem higherTail_bound (hGRH : GRH q) (hZ3 : Paper2.Z3)
    (hLocal : LogDerivPrimitiveLocal q) (r : ℕ) :
    ∃ C : ℝ, ∀ x ∈ Ioc (0 : ℝ) 1, ‖higherTail q r x‖ ≤ C * x ^ (-((r : ℝ) - 3 / 2)) := by
  obtain ⟨C, hC, hU⟩ := norm_smoothedResidual_le hGRH hZ3 hLocal
  let M (j : ℕ) := (r.choose j : ℝ) * ‖principalWeight q‖ ^ (r - j) * C ^ j
  refine ⟨∑ j ∈ Finset.Ico 3 (r + 1), M j, fun x hx ↦ ?_⟩
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj ↦ ?_)
  have hj₃ := (Finset.mem_Ico.mp hj).1
  have hjr : j ≤ r := by have := (Finset.mem_Ico.mp hj).2; omega
  have h₁ : ‖principalTerm q x‖ = ‖principalWeight q‖ * x ^ (-(1 : ℝ)) := by
    rw [principalTerm, norm_div, norm_real, Real.norm_of_nonneg hx.1.le, Real.rpow_neg_one, div_eq_mul_inv]
  rw [norm_mul, norm_mul, Complex.norm_natCast, norm_pow, norm_pow, h₁]
  calc
    _ ≤ (r.choose j : ℝ) * (‖principalWeight q‖ * x ^ (-(1 : ℝ))) ^ (r - j) *
        (C * x ^ (-(1 / 2 : ℝ))) ^ j :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hU x hx) j)
        (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (mul_nonneg (norm_nonneg _)
          (Real.rpow_nonneg hx.1.le _)) _))
    _ = M j * x ^ (-((r : ℝ) - (j : ℝ) / 2)) := by
      rw [mul_pow, mul_pow, ← Real.rpow_mul_natCast hx.1.le, ← Real.rpow_mul_natCast hx.1.le]
      have h := (Real.rpow_add hx.1 (-(1 : ℝ) * ((r - j : ℕ) : ℝ)) (-(1 / 2 : ℝ) * (j : ℝ))).symm
      rw [Nat.cast_sub hjr] at h
      have h' : -(1 : ℝ) * ((r : ℝ) - j) + -(1 / 2 : ℝ) * j = -((r : ℝ) - (j : ℝ) / 2) := by ring
      rw [h'] at h
      rw [Nat.cast_sub hjr, ← h]
      dsimp [M]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hx.1 hx.2
      (by
        have hj : (3 : ℝ) ≤ j := by exact_mod_cast hj₃
        linarith)) (by dsimp [M]; positivity)

private def binaryFactor (q r : ℕ) : ℂ := (r.choose 2 : ℂ) * principalWeight q ^ (r - 2)
private def linearFactor (q r : ℕ) : ℂ := ((r : ℂ) - 2 * (r.choose 2 : ℂ)) * principalWeight q ^ (r - 1)
private def constantFactor (q r : ℕ) : ℂ := (1 - (r : ℂ) + (r.choose 2 : ℂ)) * principalWeight q ^ r

omit [NeZero q] in
private theorem higherTail_split {r : ℕ} (hr : 2 ≤ r) (x : ℝ) :
    (smoothed q x : ℂ)^r =
      (r.choose 2 : ℂ) * principalTerm q x ^ (r - 2) * (smoothed q x : ℂ)^2 +
      ((r : ℂ) - 2 * (r.choose 2 : ℂ)) * principalTerm q x ^ (r - 1) * (smoothed q x : ℂ) +
      (1 - (r : ℂ) + (r.choose 2 : ℂ)) * principalTerm q x ^ r + higherTail q r x := by
  let a := smoothedResidual q x
  let b := principalTerm q x
  have he : (smoothed q x : ℂ) = a + b := by simp [a, b, smoothedResidual, principalTerm]
  have hsum := add_pow a b r
  rw [← Finset.sum_range_add_sum_Ico _ (show 3 ≤ r + 1 by omega)] at hsum
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.choose_zero_right, Nat.choose_one_right, Nat.cast_one, pow_zero, one_mul,
    mul_one, Nat.sub_zero, pow_one] at hsum
  have hp1 : b ^ (r - 1) = b ^ (r - 2) * b := by
    rw [← pow_succ]; congr 1; omega
  have hp0 : b ^ r = b ^ (r - 2) * b ^ 2 := by
    rw [← pow_add]; congr 1; omega
  have ht : (∑ j ∈ Finset.Ico 3 (r + 1), a ^ j * b ^ (r - j) * (r.choose j : ℂ)) =
      higherTail q r x := by
    apply Finset.sum_congr rfl
    intro j _
    change a ^ j * b ^ (r - j) * _ = _ * b ^ (r - j) * a ^ j
    ring
  rw [ht, hp0, hp1] at hsum
  rw [he, hsum]
  rw [show principalTerm q x = b by rfl, hp0, hp1]
  ring

private def higherRemainderWith (q r : ℕ) (M : ℂ → ℂ) (s : ℂ) : ℂ :=
  M s + tailMellin q r s - binaryFactor q r * tailMellin q 2 (s - r + 2) -
    linearFactor q r * tailMellin q 1 (s - r + 1)

private def higherRemainder (q r : ℕ) (s : ℂ) : ℂ :=
  (∫ x in Ioc (0 : ℝ) 1, higherTail q r x * (x : ℂ) ^ (s - 1)) +
    tailMellin q r s - binaryFactor q r * tailMellin q 2 (s - r + 2) -
      linearFactor q r * tailMellin q 1 (s - r + 1)

private theorem differentiableOn_higherRemainder (hGRH : GRH q) (hZ3 : Paper2.Z3)
    (hLocal : LogDerivPrimitiveLocal q) {r : ℕ} (hr : 2 ≤ r) :
    DifferentiableOn ℂ (higherRemainder q r) (halfPlane ((r : ℝ) - 3 / 2)) := by
  obtain ⟨C, hC⟩ := higherTail_bound hGRH hZ3 hLocal r
  have hI := TIdentity.differentiableOn_integral_Ioc_cpow (higherTail_meas q r) hC
  have h₂ := ((differentiable_tailMellin (q := q) (k := 2) (by omega)).comp
    ((differentiable_id.sub_const (r : ℂ)).add_const 2)).const_mul (binaryFactor q r)
  have h₁ := ((differentiable_tailMellin (q := q) (k := 1) le_rfl).comp
    ((differentiable_id.sub_const (r : ℂ)).add_const 1)).const_mul (linearFactor q r)
  exact (((hI.add (differentiable_tailMellin (by omega)).differentiableOn).sub
    h₂.differentiableOn).sub h₁.differentiableOn)

private theorem cpow_div_pow {x : ℝ} (hx : 0 < x) (s : ℂ) (n : ℕ) :
    (x : ℂ) ^ s / (x : ℂ)^n = (x : ℂ) ^ (s - (n : ℂ)) := by
  rw [← Complex.cpow_natCast, ← Complex.cpow_sub _ _ (ofReal_ne_zero.mpr hx.ne')]

private theorem integral_power_split (q k : ℕ) (s : ℂ)
    (hI : IntegrableOn (fun x : ℝ ↦ (smoothed q x : ℂ)^k * (x : ℂ) ^ (s - 1)) (Ioi 0)) :
    (∫ x in Ioi (0 : ℝ), (smoothed q x : ℂ)^k * (x : ℂ) ^ (s - 1)) =
      (∫ x in Ioc (0 : ℝ) 1, (smoothed q x : ℂ)^k * (x : ℂ) ^ (s - 1)) + tailMellin q k s := by
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 from zero_le_one),
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hI.mono_set Ioc_subset_Ioi_self) (hI.mono_set (Ioi_subset_Ioi zero_le_one))] <;> rfl

/-- The Mellin reduction on the initial half-plane. -/
private theorem Gamma_mul_PhiR_eq_of_integrable_tail {r : ℕ} (hr : 2 ≤ r)
    {s : ℂ} (hs : (r : ℝ) < s.re)
    (hH : IntegrableOn (fun x : ℝ ↦ higherTail q r x * (x : ℂ) ^ (s - 1)) (Ioc 0 1)) :
    Gamma s * PhiR q r s =
      binaryFactor q r * (Gamma (s - r + 2) * Phi2 q (s - r + 2)) +
      linearFactor q r * (Gamma (s - r + 1) * D q (s - r + 1)) +
      constantFactor q r / (s - r) + higherRemainder q r s := by
  have hs₂ : 2 < (s - r + 2).re := by simp; linarith
  have hs₁ : 1 < (s - r + 1).re := by simp; linarith
  obtain ⟨hR, hRV⟩ := mellin_smoothed_pow q (by omega : 1 ≤ r) hs
  obtain ⟨h₂, h₂V⟩ := mellin_smoothed_sq q hs₂
  obtain ⟨h₁, h₁V⟩ := mellin_smoothed q hs₁
  have hR' : IntegrableOn (fun x : ℝ ↦ (smoothed q x : ℂ)^r * (x : ℂ) ^ (s - 1)) (Ioi 0) := by
    simpa only [MellinConvergent, smul_eq_mul, ofReal_pow, mul_comm] using hR
  have h₁' : IntegrableOn (fun x : ℝ ↦ (smoothed q x : ℂ)^1 * (x : ℂ) ^ (s - r + 1 - 1)) (Ioi 0) := by
    simpa only [MellinConvergent, smul_eq_mul, pow_one, mul_comm] using h₁
  have hRV' : (∫ x in Ioi (0 : ℝ), (smoothed q x : ℂ)^r * (x : ℂ) ^ (s - 1)) = Gamma s * PhiR q r s := by
    simpa only [mellin, smul_eq_mul, ofReal_pow, mul_comm] using hRV
  have h₁V' : (∫ x in Ioi (0 : ℝ), (smoothed q x : ℂ)^1 * (x : ℂ) ^ (s - r + 1 - 1)) =
      Gamma (s - r + 1) * D q (s - r + 1) := by
    simpa only [mellin, smul_eq_mul, pow_one, mul_comm] using h₁V
  rw [integral_power_split q r s hR'] at hRV'
  rw [integral_power_split q 2 _ h₂] at h₂V
  rw [integral_power_split q 1 _ h₁'] at h₁V'
  have hP : -1 < (s - r - 1).re := by simp; linarith
  have hPt (x : ℝ) (hx : x ∈ Ioc (0 : ℝ) 1) :
      (smoothed q x : ℂ)^r * (x : ℂ) ^ (s - 1) =
        binaryFactor q r * ((smoothed q x : ℂ)^2 * (x : ℂ) ^ (s - r + 2 - 1)) +
        linearFactor q r * ((smoothed q x : ℂ)^1 * (x : ℂ) ^ (s - r + 1 - 1)) +
        constantFactor q r * (x : ℂ) ^ (s - r - 1) + higherTail q r x * (x : ℂ) ^ (s - 1) := by
    rw [higherTail_split hr x]
    have h₂c : ((r - 2 : ℕ) : ℂ) = (r : ℂ) - 2 := Nat.cast_sub hr
    have h₁c : ((r - 1 : ℕ) : ℂ) = (r : ℂ) - 1 := by
      simpa only [Nat.cast_one] using (Nat.cast_sub (by omega : 1 ≤ r) :
        ((r - 1 : ℕ) : ℂ) = (r : ℂ) - ((1 : ℕ) : ℂ))
    have h₂p := cpow_div_pow hx.1 (s - 1) (r - 2)
    have h₁p := cpow_div_pow hx.1 (s - 1) (r - 1)
    have h₀p := cpow_div_pow hx.1 (s - 1) r
    rw [h₂c, show s - 1 - ((r : ℂ) - 2) = s - r + 2 - 1 by ring] at h₂p
    rw [h₁c, show s - 1 - ((r : ℂ) - 1) = s - r + 1 - 1 by ring] at h₁p
    rw [show s - 1 - (r : ℂ) = s - r - 1 by ring] at h₀p
    rw [← h₂p, ← h₁p, ← h₀p]
    simp only [binaryFactor, linearFactor, constantFactor, principalTerm, div_pow, pow_one]
    ring
  have hI : Ioc (0 : ℝ) 1 ⊆ Ioi 0 := Ioc_subset_Ioi_self
  have h₂I := (h₂.mono_set hI).const_mul (binaryFactor q r)
  have h₁I := (h₁'.mono_set hI).const_mul (linearFactor q r)
  have hPI := (TIdentity.integrableOn_Ioc_cpow_of_neg_one_lt hP).const_mul (constantFactor q r)
  have hAdd₃ := integral_add ((h₂I.add h₁I).add hPI) hH
  have hAdd₂ := integral_add (h₂I.add h₁I) hPI
  have hAdd₁ := integral_add h₂I h₁I
  simp only [Pi.add_apply] at hAdd₃ hAdd₂ hAdd₁
  rw [setIntegral_congr_fun measurableSet_Ioc hPt, hAdd₃, hAdd₂, hAdd₁,
    integral_const_mul, integral_const_mul, integral_const_mul,
    TIdentity.integral_Ioc_cpow_of_neg_one_lt hP,
    show s - (r : ℂ) - 1 + 1 = s - r by ring] at hRV'
  rw [← hRV', ← h₂V, ← h₁V']
  unfold higherRemainder
  simp only [div_eq_mul_inv]
  ring

theorem Gamma_mul_PhiR_eq (hGRH : GRH q) (hZ3 : Paper2.Z3) (hLocal : LogDerivPrimitiveLocal q)
    {r : ℕ} (hr : 2 ≤ r) {s : ℂ} (hs : (r : ℝ) < s.re) :
    Gamma s * PhiR q r s =
      binaryFactor q r * (Gamma (s - r + 2) * Phi2 q (s - r + 2)) +
      linearFactor q r * (Gamma (s - r + 1) * D q (s - r + 1)) +
      constantFactor q r / (s - r) + higherRemainder q r s := by
  obtain ⟨C, hC⟩ := higherTail_bound hGRH hZ3 hLocal r
  exact Gamma_mul_PhiR_eq_of_integrable_tail hr hs
    (Phi2Proof.C_integrableOn_mellin (higherTail_meas q r) hC (s := s) (by linarith))

private def higherCoefficient (q r : ℕ) (s : ℂ) : ℂ :=
  (Gamma s)⁻¹ * (binaryFactor q r * Gamma (s - r + 2))

private def higherCorrectionWith (q r : ℕ) [NeZero q] (M : ℂ → ℂ) (s : ℂ) : ℂ :=
  (Gamma s)⁻¹ * (linearFactor q r * (Gamma (s - r + 1) * D q (s - r + 1)) +
    constantFactor q r / (s - r) + higherRemainderWith q r M s)

private def higherCorrection (q r : ℕ) [NeZero q] (s : ℂ) : ℂ :=
  (Gamma s)⁻¹ * (linearFactor q r * (Gamma (s - r + 1) * D q (s - r + 1)) +
    constantFactor q r / (s - r) + higherRemainder q r s)

/-- The shifted binary continuation and the meromorphic correction for the higher series. -/
def phiRContinuation (q r : ℕ) [NeZero q] (s : ℂ) : ℂ :=
  higherCorrection q r s + higherCoefficient q r s * phi2Continuation q (s - r + 2)

omit [NeZero q] in
private theorem analyticAt_higherCoefficient {r : ℕ} {s : ℂ} (hs : (r : ℝ) - 2 < s.re) :
    AnalyticAt ℂ (higherCoefficient q r) s := by
  have hpos : 0 < (s - r + 2).re := by simp; linarith
  have hg : AnalyticAt ℂ (fun w : ℂ ↦ Gamma (w - r + 2)) s :=
    (PhiRProof.analyticAt_Gamma_of_re_pos hpos).comp (f := fun w : ℂ ↦ w - r + 2) (by fun_prop)
  exact (PhiRProof.analyticAt_inv_Gamma s).mul (analyticAt_const.mul hg)

private theorem higherCoefficient_ne_zero {r : ℕ} (hr : 2 ≤ r) {s : ℂ} (hs : (r : ℝ) - 2 < s.re) :
    higherCoefficient q r s ≠ 0 := by
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hc : principalWeight q ≠ 0 :=
    inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (NeZero.pos q)).ne')
  exact mul_ne_zero (inv_ne_zero (Gamma_ne_zero_of_re_pos (by linarith))) (mul_ne_zero
    (mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.choose_pos hr).ne') (pow_ne_zero _ hc))
    (Gamma_ne_zero_of_re_pos (by simp; linarith)))

private theorem meromorphicOn_higherCorrectionWith {a : ℝ} {M : ℂ → ℂ}
    (hM : MeromorphicOn M (halfPlane a)) {r : ℕ} (hr : 2 ≤ r) :
    MeromorphicOn (higherCorrectionWith q r M) (halfPlane a) := by
  intro s hs
  have hm : MeromorphicAt (fun z ↦ Gamma z * D q z) (s - r + 1) :=
    (PhiRProof.meromorphicAt_Gamma _).mul (meromorphic_D _)
  have hshift : MeromorphicAt (fun z : ℂ ↦ Gamma (z - r + 1) * D q (z - r + 1)) s :=
    hm.comp_analyticAt (g := fun z : ℂ ↦ z - r + 1) (by fun_prop)
  have hrat : MeromorphicAt (fun z : ℂ ↦ constantFactor q r / (z - r)) s :=
    (MeromorphicAt.const _ s).div (analyticAt_id.sub analyticAt_const).meromorphicAt
  have ht (k : ℕ) (hk : 1 ≤ k) (f : ℂ → ℂ) (hf : AnalyticAt ℂ f s) :
      AnalyticAt ℂ (fun z ↦ tailMellin q k (f z)) s :=
    ((differentiable_tailMellin hk).analyticAt (f s)).comp hf
  have htR := ht r (by omega) id analyticAt_id
  have ht₂ := (MeromorphicAt.const (binaryFactor q r) s).mul
    (ht 2 (by omega) (fun z ↦ z - r + 2) (by fun_prop)).meromorphicAt
  have ht₁ := (MeromorphicAt.const (linearFactor q r) s).mul
    (ht 1 le_rfl (fun z ↦ z - r + 1) (by fun_prop)).meromorphicAt
  have hrem := (((hM s hs).add htR.meromorphicAt).sub ht₂).sub ht₁
  exact (PhiRProof.analyticAt_inv_Gamma s).meromorphicAt.mul
    ((((MeromorphicAt.const _ s).mul hshift).add hrat).add hrem)

private theorem meromorphicOn_higherCorrection (hGRH : GRH q) (hZ3 : Paper2.Z3)
    (hLocal : LogDerivPrimitiveLocal q) {r : ℕ} (hr : 2 ≤ r) :
    MeromorphicOn (higherCorrection q r) (halfPlane ((r : ℝ) - 3 / 2)) := by
  apply meromorphicOn_higherCorrectionWith (q := q)
    (M := fun z ↦ ∫ x in Ioc (0 : ℝ) 1, higherTail q r x * (x : ℂ) ^ (z - 1)) _ hr
  exact fun s hs ↦ ((TIdentity.differentiableOn_integral_Ioc_cpow (higherTail_meas q r)
    (higherTail_bound hGRH hZ3 hLocal r).choose_spec).analyticAt
      ((isOpen_halfPlane _).mem_nhds hs)).meromorphicAt

theorem meromorphicOn_phiRContinuation (hGRH : GRH q) (hZ3 : Paper2.Z3)
    (hLocal : LogDerivPrimitiveLocal q) {r : ℕ} (hr : 2 ≤ r) :
    MeromorphicOn (phiRContinuation q r) (halfPlane ((r : ℝ) - 1)) := by
  intro s hs
  have hs' : (r : ℝ) - 1 < s.re := hs
  have hB : MeromorphicAt (fun z : ℂ ↦ phi2Continuation q (z - r + 2)) s := by
    apply MeromorphicAt.comp_analyticAt (f := phi2Continuation q) (g := fun z : ℂ ↦ z - r + 2)
    · apply meromorphicOn_phi2Continuation hGRH hZ3 hLocal
      show 1 < (s - r + 2).re
      simp
      linarith
    · fun_prop
  have hR := meromorphicOn_higherCorrection hGRH hZ3 hLocal hr s
    (show (r : ℝ) - 3 / 2 < s.re by linarith)
  exact hR.add ((analyticAt_higherCoefficient (q := q) (r := r) (by linarith)).meromorphicAt.mul hB)

theorem eqOn_phiRContinuation (hGRH : GRH q) (hZ3 : Paper2.Z3)
    (hLocal : LogDerivPrimitiveLocal q) {r : ℕ} (hr : 2 ≤ r) :
    EqOn (phiRContinuation q r) (PhiR q r) (halfPlane r) := by
  intro s hs
  have hs' : (r : ℝ) < s.re := hs
  have hs₂ : 2 < (s - r + 2).re := by simp; linarith
  have h := Gamma_mul_PhiR_eq hGRH hZ3 hLocal hr hs'
  have h₀ : Gamma s ≠ 0 := Gamma_ne_zero_of_re_pos (by linarith [Nat.cast_nonneg (α := ℝ) r])
  have hEq : PhiR q r s = (Gamma s)⁻¹ * (Gamma s * PhiR q r s) := by
    rw [← mul_assoc, inv_mul_cancel₀ h₀, one_mul]
  rw [hEq, h, phiRContinuation, eqOn_phi2Continuation hGRH hZ3 hLocal hs₂]
  unfold higherCoefficient higherCorrection
  ring

/-- A meromorphic small-interval transform for the higher tail transfers the
binary boundary to the higher series. -/
theorem naturalBoundary_higher_of_mellin {r : ℕ} (hr : 2 ≤ r) {a : ℝ}
    (ha : a < (r : ℝ) - 1) {M B : ℂ → ℂ}
    (hM : MeromorphicOn M (halfPlane a))
    (hMellin : ∀ s : ℂ, (r : ℝ) < s.re →
      IntegrableOn (fun x : ℝ ↦ higherTail q r x * (x : ℂ) ^ (s - 1)) (Ioc 0 1) ∧
      (∫ x in Ioc (0 : ℝ) 1, higherTail q r x * (x : ℂ) ^ (s - 1)) = M s)
    (hB : MeromorphicOn B HH) (hInitB : EqOn B (Phi2 q) (halfPlane 2))
    (hBoundary : IsNaturalBoundary B HH lineOne) :
    (∃ F : ℂ → ℂ, MeromorphicOn F (halfPlane ((r : ℝ) - 1)) ∧
      EqOn F (PhiR q r) (halfPlane r)) ∧
    (∀ F : ℂ → ℂ, MeromorphicOn F (halfPlane ((r : ℝ) - 1)) →
      F =ᶠ[codiscreteWithin (halfPlane r)] PhiR q r →
      IsNaturalBoundary F (halfPlane ((r : ℝ) - 1)) (lineAt ((r : ℝ) - 1))) := by
  let U := halfPlane ((r : ℝ) - 1)
  let a' := max a ((r : ℝ) - 2)
  have ha' : a' < (r : ℝ) - 1 := max_lt ha (by linarith)
  let W := higherCorrectionWith q r M
  let C := higherCoefficient q r
  let F₀ : ℂ → ℂ := fun s ↦ W s + C s * B (s - r + 2)
  have hW : MeromorphicOn W (halfPlane a') :=
    fun s hs ↦ meromorphicOn_higherCorrectionWith (q := q) hM hr s (by
      show a < s.re
      exact (le_max_left a ((r : ℝ) - 2)).trans_lt (show a' < s.re from hs))
  have hcoeff (s : ℂ) (hs : s ∈ halfPlane a') : (r : ℝ) - 2 < s.re :=
    (le_max_right _ _).trans_lt hs
  have hF₀ : MeromorphicOn F₀ U := by
    intro s hs
    have hs' : (r : ℝ) - 1 < s.re := hs
    have hs'' : s ∈ halfPlane a' := ha'.trans hs'
    have hB' : MeromorphicAt (fun z : ℂ ↦ B (z - r + 2)) s :=
      (hB _ (show 1 < (s - r + 2).re by simp; linarith)).comp_analyticAt
        (g := fun z : ℂ ↦ z - r + 2) (by fun_prop)
    exact (hW s hs'').add ((analyticAt_higherCoefficient (hcoeff s hs'')).meromorphicAt.mul hB')
  have hInit : EqOn F₀ (PhiR q r) (halfPlane r) := by
    intro s hs
    have hs' : (r : ℝ) < s.re := hs
    obtain ⟨hI, hIv⟩ := hMellin s hs'
    have he := Gamma_mul_PhiR_eq_of_integrable_tail hr hs' hI
    unfold higherRemainder at he
    rw [hIv, ← hInitB (show 2 < (s - r + 2).re by simp; linarith)] at he
    have hΓ : Gamma s ≠ 0 := Gamma_ne_zero_of_re_pos (by linarith [Nat.cast_nonneg (α := ℝ) r])
    have h := congrArg (fun w ↦ (Gamma s)⁻¹ * w) he
    change (Gamma s)⁻¹ * (Gamma s * PhiR q r s) = _ at h
    rw [← mul_assoc, inv_mul_cancel₀ hΓ, one_mul] at h
    rw [h]
    unfold F₀ W C higherCorrectionWith higherCoefficient higherRemainderWith
    ring
  refine ⟨⟨F₀, hF₀, hInit⟩, fun F hF hAgree z hz ↦ ?_⟩
  have hz' : z.re = (r : ℝ) - 1 := hz
  have hEq₀ := Phi2Proof.eventuallyEq_codiscreteWithin_of_nhdsNE fun s hs ↦
    PhiRProof.eventuallyEq_nhdsNE_of_agree_halfPlane (by linarith) hF hF₀ hInit hAgree hs
  let c : ℝ := (r : ℝ) - 2
  have hEq : F =ᶠ[codiscreteWithin U] fun s ↦ W s + C s * B (s - (c : ℂ)) := by
    filter_upwards [hEq₀] with s hs
    have he : s - (c : ℂ) = s - r + 2 := by simp [c]; ring
    simpa only [F₀, he] using hs
  have hzW : z ∈ halfPlane a' := by show a' < z.re; rwa [hz']
  apply (PhiRProof.noMeromorphicExtensionAt_iff_of_eq_add_mul (isOpen_halfPlane _) hzW hW
    (fun s hs ↦ analyticAt_higherCoefficient (hcoeff s hs))
    (fun s hs ↦ higherCoefficient_ne_zero hr (hcoeff s hs)) hEq).mpr
  have hp : (fun s : ℂ ↦ s - (c : ℂ)) ⁻¹' HH = U := by
    rw [PhiRProof.preimage_sub_halfPlane]
    congr 1
    dsimp [c]
    ring
  have htrans := PhiRProof.noMeromorphicExtensionAt_comp_sub_iff (H := B) (U := HH)
    (z₀ := z - (c : ℂ)) (c := (c : ℂ))
  rw [sub_add_cancel, hp] at htrans
  apply htrans.mpr
  apply hBoundary
  change (z - (c : ℂ)).re = 1
  simp [c, hz']
  ring

/-- Any higher continuation agreeing on the initial half-plane has the shifted boundary. -/
theorem isNaturalBoundary_phiR_of_agrees (hGRH : GRH q) (hZ3 : Paper2.Z3)
    (hLocal : LogDerivPrimitiveLocal q) (hGap : Paper2.ZLittlewood) (hStir : Phi2HInf.StirlingStrip)
    {r : ℕ} (hr : 2 ≤ r) (F : ℂ → ℂ)
    (hF : MeromorphicOn F (halfPlane ((r : ℝ) - 1)))
    (hAgree : F =ᶠ[codiscreteWithin (halfPlane r)] PhiR q r) :
    IsNaturalBoundary F (halfPlane ((r : ℝ) - 1)) (lineAt ((r : ℝ) - 1)) := by
  let M : ℂ → ℂ := fun s ↦ ∫ x in Ioc (0 : ℝ) 1, higherTail q r x * (x : ℂ) ^ (s - 1)
  obtain ⟨K, hK⟩ := higherTail_bound hGRH hZ3 hLocal r
  have hD := TIdentity.differentiableOn_integral_Ioc_cpow (higherTail_meas q r) hK
  have hM : MeromorphicOn M (halfPlane ((r : ℝ) - 3 / 2)) :=
    fun s hs ↦ (hD.analyticAt ((isOpen_halfPlane _).mem_nhds hs)).meromorphicAt
  have hInit := eqOn_phi2Continuation hGRH hZ3 hLocal
  have hB := meromorphicOn_phi2Continuation hGRH hZ3 hLocal
  have hAgreeB : phi2Continuation q =ᶠ[codiscreteWithin (halfPlane 2)] Phi2 q := by
    filter_upwards [self_mem_codiscreteWithin (halfPlane 2)] with s hs using hInit hs
  have hbound := isNaturalBoundary_phi2_of_agrees hGRH hZ3 hLocal hGap hStir _ hB hAgreeB
  exact (naturalBoundary_higher_of_mellin hr (by linarith) hM
    (fun s hs ↦ ⟨Phi2Proof.C_integrableOn_mellin (higherTail_meas q r) hK
      (s := s) (by linarith), rfl⟩) hB hInit hbound).2 F hF hAgree

end GoldbachBoundaries.ResidueClass
