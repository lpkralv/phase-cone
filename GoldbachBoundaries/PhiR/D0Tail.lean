import GoldbachBoundaries.PhiR.UnsubtractedGap
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaHadamard

/-! # The Hadamard zero sum and the real-point tail -/

noncomputable section

open Complex ComplexConjugate Complex.Hadamard Filter Set Topology

namespace GoldbachBoundaries.PhiRProof

open GoldbachBoundaries.Paper2

private theorem xi_eq_zeta_mul {z : ℂ} (hz : 0 < z.re) (h1 : z ≠ 1) :
    riemannXi z = riemannZeta z * (z * (z - 1) * Gammaℝ z / 2) := by
  have h0 : z ≠ 0 := by
    rintro rfl
    simp at hz
  rw [riemannXi_eq_mul_completedRiemannZeta h0 h1, riemannZeta_def_of_ne_zero h0]
  field_simp [Gammaℝ_ne_zero_of_re_pos hz]

private theorem xi_prefactor_ne_zero {z : ℂ} (hz : 0 < z.re) (h1 : z ≠ 1) :
    z * (z - 1) * Gammaℝ z / 2 ≠ 0 := by
  have h0 : z ≠ 0 := by
    rintro rfl
    simp at hz
  exact div_ne_zero (mul_ne_zero (mul_ne_zero h0 (sub_ne_zero.mpr h1))
    (Gammaℝ_ne_zero_of_re_pos hz)) two_ne_zero

private theorem xi_ne_zero_of_one_le_re {z : ℂ} (hz : 1 ≤ z.re) : riemannXi z ≠ 0 := by
  by_cases h1 : z = 1
  · simp [h1, riemannXi]
  have hpos : 0 < z.re := zero_lt_one.trans_le hz
  rw [xi_eq_zeta_mul hpos h1]
  exact mul_ne_zero (riemannZeta_ne_zero_of_one_le_re hz) (xi_prefactor_ne_zero hpos h1)

private theorem mem_nontrivialZeros_iff_xi_zero {z : ℂ} :
    z ∈ NontrivialZeros ↔ riemannXi z = 0 := by
  constructor
  · intro hz
    rw [xi_eq_zeta_mul hz.2.1 (ne_one_of_mem_nontrivialZeros hz), hz.1, zero_mul]
  · intro hz
    have hlt : z.re < 1 := lt_of_not_ge fun h => xi_ne_zero_of_one_le_re h hz
    have hpos : 0 < z.re := lt_of_not_ge fun h =>
      xi_ne_zero_of_one_le_re (z := 1 - z) (by simp; linarith) (by rwa [riemannXi_one_sub])
    have h1 : z ≠ 1 := by
      rintro rfl
      simp at hlt
    rw [xi_eq_zeta_mul hpos h1] at hz
    exact ⟨(mul_eq_zero.mp hz).resolve_right (xi_prefactor_ne_zero hpos h1), hpos, hlt⟩

private theorem xi_divisor_eq_zetaMult (ρ : NontrivialZeros) :
    MeromorphicOn.divisor riemannXi univ (ρ : ℂ) = (zetaMult (ρ : ℂ) : ℤ) := by
  let z : ℂ := ρ
  have hz : 0 < z.re := ρ.2.2.1
  have h1 : z ≠ 1 := ne_one_of_mem_nontrivialZeros ρ.2
  let g (w : ℂ) := w * (w - 1) * Gammaℝ w / 2
  have hgNe : g z ≠ 0 := xi_prefactor_ne_zero hz h1
  have hGamma : AnalyticAt ℂ Gammaℝ z := by
    have h := (differentiable_Gammaℝ_inv.analyticAt z).inv
      (inv_ne_zero (Gammaℝ_ne_zero_of_re_pos hz))
    simpa only [Pi.inv_def, inv_inv] using h
  have hg : AnalyticAt ℂ g z := by
    dsimp [g]
    fun_prop
  have heq : riemannXi =ᶠ[𝓝 z] fun w => riemannZeta w * g w := by
    filter_upwards [continuous_re.continuousAt.eventually_const_lt hz, eventually_ne_nhds h1]
      with w hw hw1
    exact xi_eq_zeta_mul hw hw1
  have hord := calc
    analyticOrderAt riemannXi z = analyticOrderAt (fun w => riemannZeta w * g w) z :=
      analyticOrderAt_congr heq
    _ = (zetaMult z : ℕ∞) := by
      change analyticOrderAt (riemannZeta * g) z = _
      rw [analyticOrderAt_mul (analyticOn_riemannZeta z h1) hg,
        hg.analyticOrderAt_eq_zero.mpr hgNe, add_zero, analyticOrderAt_riemannZeta_eq_zetaMult h1]
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply
    (fun w _ => differentiable_riemannXi.analyticAt w) (mem_univ z), hord]
  simp [z]

private abbrev XiIndex := divisorZeroIndex₀ riemannXi (univ : Set ℂ)

private theorem xiIndex_mem (p : XiIndex) : divisorZeroIndex₀_val p ∈ NontrivialZeros := by
  apply mem_nontrivialZeros_iff_xi_zero.mpr
  by_contra h
  have hn := divisorZeroIndex₀_val_mem_divisor_support p
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply
      (fun w _ => differentiable_riemannXi.analyticAt w) (mem_univ _),
    (differentiable_riemannXi.analyticAt _).analyticOrderAt_eq_zero.mpr h] at hn
  simp at hn

private def xiIndexEquiv : XiIndex ≃ Σ ρ : NontrivialZeros, Fin (zetaMult (ρ : ℂ)) where
  toFun p :=
    ⟨⟨divisorZeroIndex₀_val p, xiIndex_mem p⟩,
      Fin.cast (by rw [xi_divisor_eq_zetaMult ⟨_, xiIndex_mem p⟩]; simp) p.1.2⟩
  invFun p :=
    ⟨⟨p.1, Fin.cast (by rw [xi_divisor_eq_zetaMult p.1]; simp) p.2⟩,
      ne_zero_of_mem_nontrivialZeros p.1.2⟩
  left_inv p := by
    apply Subtype.ext
    exact Sigma.ext rfl (heq_of_eq (Fin.ext rfl))
  right_inv p := Sigma.ext rfl (heq_of_eq (Fin.ext rfl))

private theorem logDeriv_xi_diff :
    logDeriv riemannXi 1 - logDeriv riemannXi 0 = 2 * completedRiemannZeta₀ 1 := by
  have hder : HasDerivAt riemannXi (completedRiemannZeta₀ 1 / 2) 1 := by
    have hpoly := (hasDerivAt_id' (1 : ℂ)).mul ((hasDerivAt_id' (1 : ℂ)).sub_const 1)
    have h := ((hpoly.mul (differentiable_completedZeta₀ 1).hasDerivAt).add_const 1).div_const 2
    unfold riemannXi
    simpa [Pi.mul_def] using h
  have hsub : HasDerivAt (fun z : ℂ => 1 - z) (-1) 0 := by
    simpa [Pi.sub_def] using
      ((hasDerivAt_const (0 : ℂ) (1 : ℂ)).sub (hasDerivAt_id' (0 : ℂ)))
  have hder' : HasDerivAt riemannXi (completedRiemannZeta₀ (1 - 0) / 2) (1 - 0) := by
    simpa using hder
  have hder0 : HasDerivAt riemannXi (-(completedRiemannZeta₀ 1 / 2)) 0 := by
    simpa [Function.comp_def, riemannXi_one_sub] using hder'.comp 0 hsub
  rw [logDeriv_apply, logDeriv_apply, hder.deriv, hder0.deriv, riemannXi_zero,
    show riemannXi 1 = 1 / 2 by simp [riemannXi]]
  ring

private theorem hasSum_xi_at_one :
    HasSum (fun p : XiIndex =>
      1 / (1 - divisorZeroIndex₀_val p) + 1 / divisorZeroIndex₀_val p)
      (2 * completedRiemannZeta₀ 1) := by
  obtain ⟨P, hdeg, hfac⟩ := riemannXi_hadamard_factorization_no_monomial
  have hdegree : P.derivative.degree ≤ 0 := by
    apply Polynomial.degree_le_of_natDegree_le
    have hn : P.natDegree ≤ 1 := Polynomial.natDegree_le_of_degree_le hdeg
    have hd := P.natDegree_derivative_le
    omega
  have h0 (p : XiIndex) : (0 : ℂ) ≠ divisorZeroIndex₀_val p :=
    (divisorZeroIndex₀_val_ne_zero p).symm
  have h1 (p : XiIndex) : (1 : ℂ) ≠ divisorZeroIndex₀_val p :=
    (ne_one_of_mem_nontrivialZeros (xiIndex_mem p)).symm
  have hlog0 := logDeriv_riemannXi_eq_polynomial_derivative_add_tsum hfac h0
  have hlog1 := logDeriv_riemannXi_eq_polynomial_derivative_add_tsum hfac h1
  simp only [zero_sub, div_neg, neg_add_cancel, tsum_zero, add_zero] at hlog0
  rw [Polynomial.eq_C_of_degree_le_zero hdegree, Polynomial.eval_C] at hlog0 hlog1
  have hsum := (summable_riemannXi_logDerivTerms_divisorZeroIndex₀ h1).hasSum
  rw [← logDeriv_xi_diff, hlog0, hlog1, add_sub_cancel_left]
  exact hsum

private theorem xi_kernel_on_line (hRH : RiemannHypothesis) (ρ : NontrivialZeros) :
    1 / (1 - (ρ : ℂ)) + 1 / (ρ : ℂ) =
      ((1 / (1 / 4 + (ρ : ℂ).im ^ 2) : ℝ) : ℂ) := by
  have hre := sigmaFinite_re_eq_half hRH ρ.2
  have hconj : 1 - (ρ : ℂ) = conj (ρ : ℂ) := by
    apply Complex.ext
    · norm_num [hre]
    · simp
  have hρ := ne_zero_of_mem_nontrivialZeros ρ.2
  have hconjNe : conj (ρ : ℂ) ≠ 0 := by simpa using hρ
  rw [hconj, div_add_div _ _ hconjNe hρ, mul_one, one_mul, mul_comm (conj (ρ : ℂ)),
    Complex.add_conj, Complex.mul_conj, normSq_apply, hre]
  push_cast
  ring

/-- Under RH, the Hadamard zero sum converges to the difference of the logarithmic
derivatives of ξ at 1 and 0. -/
theorem d0_identity (hRH : RiemannHypothesis) :
    Summable (fun ρ : NontrivialZeros => (zetaMult (ρ : ℂ) : ℝ) / (1 / 4 + (ρ : ℂ).im ^ 2)) ∧
    (∑' ρ : NontrivialZeros, (zetaMult (ρ : ℂ) : ℝ) / (1 / 4 + (ρ : ℂ).im ^ 2)) =
      2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi) := by
  have h := xiIndexEquiv.symm.hasSum_iff.mpr hasSum_xi_at_one
  have hs : HasSum (fun p : Σ ρ : NontrivialZeros, Fin (zetaMult (ρ : ℂ)) =>
      (1 / (1 / 4 + (p.1 : ℂ).im ^ 2) : ℝ))
      (2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) := by
    apply Complex.hasSum_ofReal.mp
    rw [completedRiemannZeta₀_one, show (4 * (Real.pi : ℂ)) = ((4 * Real.pi : ℝ) : ℂ)
      by push_cast; rfl, ← Complex.ofReal_log (by positivity : 0 ≤ 4 * Real.pi)] at h
    convert h using 1
    · funext p
      exact (xi_kernel_on_line hRH p.1).symm
    · push_cast
      ring
  have hGrouped : HasSum
      (fun ρ : NontrivialZeros => (zetaMult (ρ : ℂ) : ℝ) / (1 / 4 + (ρ : ℂ).im ^ 2))
      (2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) := by
    apply hs.sigma
    intro ρ
    convert hasSum_fintype (fun _ : Fin (zetaMult (ρ : ℂ)) =>
      (1 / (1 / 4 + (ρ : ℂ).im ^ 2) : ℝ)) using 1
    simp [div_eq_mul_inv]

  exact ⟨hGrouped.summable, hGrouped.tsum_eq⟩

private theorem log_four_pi_gt : (5 / 2 : ℝ) < Real.log (4 * Real.pi) := by
  rw [Real.lt_log_iff_exp_lt (by positivity)]
  apply (sq_lt_sq₀ (Real.exp_pos _).le (by positivity)).mp
  calc
    Real.exp (5 / 2) ^ 2 = Real.exp 1 ^ 5 := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
      norm_num
    _ ≤ (2.7182818286 : ℝ) ^ 5 :=
      pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_one_lt_d9.le 5
    _ < (4 * 3.14 : ℝ) ^ 2 := by norm_num
    _ ≤ (4 * Real.pi) ^ 2 := by
      gcongr
      exact Real.pi_gt_d2.le

-- The quartic factor can grow by at most exp(4 * (t - 32) / 32) after the cutoff.
private theorem polynomial_mul_exp_le_at_32 {t : ℝ} (ht : 32 ≤ t) :
    (1 / 4 + t ^ 2) ^ 2 * Real.exp (-Real.pi * t) ≤
      (1 / 4 + 32 ^ 2) ^ 2 * Real.exp (-Real.pi * 32) := by
  let u := (t - 32) / 32
  have hu : 0 ≤ u := div_nonneg (sub_nonneg.mpr ht) (by norm_num)
  have hpoly : 1 / 4 + t ^ 2 ≤ (1 / 4 + 32 ^ 2) * (1 + u) ^ 2 := by
    have ht' : t = 32 * (1 + u) := by dsimp [u]; ring
    rw [ht']
    nlinarith [sq_nonneg u]
  have hexp : 1 + u ≤ Real.exp u := by simpa [add_comm] using Real.add_one_le_exp u
  calc
    _ ≤ ((1 / 4 + 32 ^ 2) * Real.exp u ^ 2) ^ 2 * Real.exp (-Real.pi * t) := by
      gcongr
      exact hpoly.trans (by gcongr)
    _ = (1 / 4 + 32 ^ 2) ^ 2 * Real.exp (4 * u - Real.pi * t) := by
      rw [mul_pow, ← pow_mul, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
      norm_num [sub_eq_add_neg]
    _ ≤ _ := by
      gcongr
      dsimp [u]
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ Real.pi - 4 / 32 by linarith [Real.pi_gt_d2])
        (sub_nonneg.mpr ht)]

private def d0Term (ρ : NontrivialZeros) : ℝ :=
  (zetaMult (ρ : ℂ) : ℝ) / (1 / 4 + (ρ : ℂ).im ^ 2)

private def tailFactor : ℝ :=
  2 * Real.pi * ((1 / 4 + 32 ^ 2) ^ 2 * Real.exp (-Real.pi * 32))

private theorem zeroWeight_le_d0_majorant (ρ : NontrivialZeros) (hρ : 32 ≤ |(ρ : ℂ).im|) :
    zeroWeight (ρ : ℂ) ≤ tailFactor * d0Term ρ ^ 2 := by
  let t := |(ρ : ℂ).im|
  have htSq : t ^ 2 = (ρ : ℂ).im ^ 2 := sq_abs _
  have hcosh : Real.cosh (Real.pi * (ρ : ℂ).im) = Real.cosh (Real.pi * t) := by
    have hAbs : |Real.pi * (ρ : ℂ).im| = Real.pi * t := by
      rw [abs_mul, abs_of_nonneg Real.pi_pos.le]
    rw [← hAbs, Real.cosh_abs]
  have hexp : Real.exp (Real.pi * t) / 2 ≤ Real.cosh (Real.pi * t) := by
    rw [Real.cosh_eq]
    linarith [Real.exp_pos (-(Real.pi * t))]
  unfold zeroWeight
  rw [hcosh]
  calc
    _ ≤ Real.pi * (zetaMult (ρ : ℂ) : ℝ) ^ 2 / (Real.exp (Real.pi * t) / 2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hexp
    _ = 2 * Real.pi * ((1 / 4 + t ^ 2) ^ 2 * Real.exp (-Real.pi * t)) * d0Term ρ ^ 2 := by
      rw [htSq, neg_mul, Real.exp_neg, d0Term]
      field_simp
    _ ≤ tailFactor * d0Term ρ ^ 2 := by
      unfold tailFactor
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (polynomial_mul_exp_le_at_32 hρ) (by positivity)) (by positivity)

private theorem d0_tail_factor_lt : tailFactor * (1 / 6) ^ 2 < 4.006e-39 := calc
  _ ≤ 2 * (3.141593 : ℝ) * ((1 / 4 + 32 ^ 2) ^ 2 * 2.1876e-44) * (1 / 6) ^ 2 := by
    unfold tailFactor
    gcongr
    · exact Real.pi_lt_d6.le
    · exact exp_neg_pi_mul_32_lt.le
  _ < _ := by norm_num

/-- Under RH, the absolute-ordinate tail of the mass is summable and less than 4.1e-39. -/
theorem tail_above_32_of_RH (hRH : RiemannHypothesis) :
    let tail := {ρ : NontrivialZeros | 32 < |(ρ : ℂ).im|}
    let f (ρ : tail) := zeroWeight (ρ.1 : ℂ)
    Summable f ∧ (∑' ρ, f ρ) < 4.1e-39 := by
  intro tail f
  obtain ⟨ha, hD⟩ := d0_identity hRH
  let D := ∑' ρ, d0Term ρ
  have ha' : Summable d0Term := ha
  have haNonneg (ρ : NontrivialZeros) : 0 ≤ d0Term ρ := by unfold d0Term; positivity
  have hDNonneg : 0 ≤ D := tsum_nonneg haNonneg
  have hDlt : D < 1 / 6 := by
    change (∑' ρ, d0Term ρ) < _
    change (∑' ρ, d0Term ρ) = _ at hD
    rw [hD]
    linarith [Real.eulerMascheroniConstant_lt_two_thirds, log_four_pi_gt]
  have hFactor : 0 ≤ tailFactor := by unfold tailFactor; positivity
  have hTail : Summable (fun ρ : tail => d0Term ρ.1) := ha'.subtype _
  let g (ρ : tail) := tailFactor * (D * d0Term ρ.1)
  have hg : Summable g := (hTail.mul_left D).mul_left tailFactor
  have hle (ρ : tail) : f ρ ≤ g ρ :=
    (zeroWeight_le_d0_majorant ρ.1 (show 32 < |(ρ.1 : ℂ).im| from ρ.2).le).trans
      (mul_le_mul_of_nonneg_left
        (by
          rw [sq]
          exact mul_le_mul_of_nonneg_right (ha'.le_tsum _ (fun j _ => haNonneg j)) (haNonneg _))
        hFactor)
  have hf : Summable f := hg.of_nonneg_of_le (fun _ => zeroWeight_nonneg _) hle
  refine ⟨hf, (hf.tsum_le_tsum hle hg).trans_lt ?_⟩
  calc
    (∑' ρ, g ρ) = tailFactor * (D * ∑' ρ : tail, d0Term ρ.1) := by
      simp only [g, tsum_mul_left]
    _ ≤ tailFactor * D ^ 2 := by
      rw [sq]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (ha'.tsum_subtype_le _ tail haNonneg) hDNonneg) hFactor
    _ ≤ tailFactor * (1 / 6) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hDNonneg hDlt.le 2) hFactor
    _ < _ := d0_tail_factor_lt.trans (by norm_num)

private theorem muZero_mem_of_RH (hRH : RiemannHypothesis) (hLow : ReleaseLowZeros) :
    muLo < muZero ∧ muZero < muHi := by
  obtain ⟨hsum, hbound⟩ := tail_above_32_of_RH hRH
  let posTail := {ρ : positiveZeros | 32 < (ρ.1 : ℂ).im}
  let tail := {ρ : NontrivialZeros | 32 < |(ρ : ℂ).im|}
  let incl (ρ : posTail) : tail :=
    ⟨ρ.1.1, by
      change 32 < |(ρ.1.1 : ℂ).im|
      exact lt_of_lt_of_le (show 32 < (ρ.1.1 : ℂ).im from ρ.2) (le_abs_self _)⟩
  have hinj : Function.Injective incl := by
    intro ρ σ h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : tail => z.1) h
  have hsum' : Summable (fun ρ : tail => zeroWeight (ρ.1 : ℂ)) := hsum
  have hcomp : Summable ((fun ρ : tail => zeroWeight (ρ.1 : ℂ)) ∘ incl) :=
    hsum'.comp_injective hinj
  have hpos : Summable (fun ρ : posTail => zeroWeight (ρ.1.1 : ℂ)) := by
    simpa only [Function.comp_def, incl] using hcomp
  have hDouble : (∑' ρ : tail, zeroWeight (ρ.1 : ℂ)) =
      2 * ∑' ρ : posTail, zeroWeight (ρ.1.1 : ℂ) :=
    tsum_zeroWeight_abs_tail_eq_two_mul_positive (T := 32) hsum'
  have hposBound : 2 * (∑' ρ : posTail, zeroWeight (ρ.1.1 : ℂ)) < (4.1e-39 : ℝ) := by
    rw [← hDouble]
    exact hbound
  have hcap : (4.1e-39 : ℝ) < 5.58e-39 := by norm_num
  exact muZero_mem_of_positive_tail hLow hpos (lt_trans hposBound hcap)

/-- The sign-change threshold lies strictly between gapN and gapN + 1. -/
theorem rStar_gap_RH (hRH : RiemannHypothesis) (hZ2 : Z2) (hLow : ReleaseLowZeros) :
    (gapN : ℝ) < 1 + 2 * Real.log (2 * Real.pi) / muZero ∧
      1 + 2 * Real.log (2 * Real.pi) / muZero < (gapN : ℝ) + 1 :=
  rStar_gap_of_muZero_mem (muZero_pos hRH hZ2) (muZero_mem_of_RH hRH hLow)

/-- The real limit is nonzero at every admissible integer arity, with sign given by the gap. -/
theorem phiR_real_limit_ne_zero_RH (hRH : RiemannHypothesis) (hZ2 : Z2)
    (hLow : ReleaseLowZeros) (r : ℕ) (hr : 2 ≤ r) :
    let value := ((r.choose 2 : ℝ) * muZero - (r : ℝ) * Real.log (2 * Real.pi)) /
      ((r - 2).factorial : ℝ)
    value ≠ 0 ∧ (r ≤ gapN → value < 0) ∧ (gapN + 1 ≤ r → 0 < value) :=
  phiR_real_limit_ne_zero_of_gap (muZero_pos hRH hZ2) (rStar_gap_RH hRH hZ2 hLow) r hr

/-- The radial real-point limit exists, is real and nonzero, and has sign given by the gap. -/
theorem phiR_tendsto_ne_zero_RH (hRH : RiemannHypothesis) (hZ2 : Z2) (hZ3 : Z3)
    (hLow : ReleaseLowZeros) {r : ℕ} (hr : 2 ≤ r) :
    ∃ L : ℝ, L ≠ 0 ∧ (r ≤ gapN → L < 0) ∧ (gapN + 1 ≤ r → 0 < L) ∧
      Tendsto (fun η : ℝ => (η : ℂ) * PhiRc r ((r : ℂ) - 1 + η)) (𝓝[>] 0) (𝓝 (L : ℂ)) := by
  obtain ⟨hne, hneg, hpos⟩ := phiR_real_limit_ne_zero_RH hRH hZ2 hLow r hr
  exact ⟨_, hne, hneg, hpos, phiR_real_limit hRH hZ2 hZ3 hr⟩

end GoldbachBoundaries.PhiRProof
