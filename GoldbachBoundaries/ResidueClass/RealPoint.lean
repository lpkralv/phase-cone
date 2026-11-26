import GoldbachBoundaries.ResidueClass.HigherReduction
import Batteries.Tactic.OpenPrivate

/-! # The regularized real limit for the class-one series -/

noncomputable section

open Complex ComplexConjugate Filter Set MeasureTheory Topology

namespace GoldbachBoundaries.ResidueClass

variable {q : ℕ} [NeZero q]

/-- The entire tail term `Ẽ_r` in the ordinary-GRH Mellin reduction. -/
def phiRMainTail (q r : ℕ) (s : ℂ) : ℂ :=
  tailMellin q r s -
    (r.choose 2 : ℂ) * principalWeight q ^ (r - 2) * tailMellin q 2 (s - r + 2) +
    ((r : ℂ) * (r - 2 : ℂ)) * principalWeight q ^ (r - 1) * tailMellin q 1 (s - r + 1)

/-- The subtraction `𝔐_r(s; q)` under ordinary GRH, including the tail
term. Here `principalWeight q = 1 / φ(q)` and the argument of `D` is `s - r + 1`. -/
def phiRMain (q r : ℕ) [NeZero q] (s : ℂ) : ℂ :=
  ((r : ℂ) * principalWeight q ^ (r - 1) * (Gamma (s - r + 1) * D q (s - r + 1)) -
    ((r : ℂ) - 1) * principalWeight q ^ r / (s - r) + phiRMainTail q r s) / Gamma s

-- Reuse the reduction's internal Mellin estimate without changing its source module.
open private higherRemainder higherCoefficient higherCorrection binaryFactor linearFactor
  constantFactor differentiableOn_higherRemainder from GoldbachBoundaries.ResidueClass.HigherReduction

private def higherSmallMellin (q r : ℕ) (s : ℂ) : ℂ :=
  ∫ x in Ioc (0 : ℝ) 1, higherTail q r x * (x : ℂ) ^ (s - 1)

private theorem linearFactor_eq (q r : ℕ) :
    linearFactor q r = -((r : ℂ) * ((r : ℂ) - 2)) * principalWeight q ^ (r - 1) := by
  unfold linearFactor
  rw [Nat.cast_choose_two]
  ring

omit [NeZero q] in
private theorem higherRemainder_eq (r : ℕ) (s : ℂ) :
    higherRemainder q r s = higherSmallMellin q r s + phiRMainTail q r s := by
  unfold higherRemainder higherSmallMellin phiRMainTail binaryFactor
  rw [linearFactor_eq]
  ring

private theorem analyticAt_higherSmallMellin (hGRH : GRH q) (hZ3 : Paper2.Z3)
    (hLocal : LogDerivPrimitiveLocal q) {r : ℕ} (hr : 2 ≤ r)
    {s : ℂ} (hs : (r : ℝ) - 3 / 2 < s.re) :
    AnalyticAt ℂ (higherSmallMellin q r) s := by
  have hTail : Differentiable ℂ (phiRMainTail q r) :=
    ((differentiable_tailMellin (by omega)).sub
      (((differentiable_tailMellin (by decide : 1 ≤ 2)).comp
        ((differentiable_id.sub_const (r : ℂ)).add_const 2)).const_mul _)).add
      (((differentiable_tailMellin le_rfl).comp
        ((differentiable_id.sub_const (r : ℂ)).add_const 1)).const_mul _)
  have h := (differentiableOn_higherRemainder hGRH hZ3 hLocal hr).analyticAt
    ((isOpen_halfPlane _).mem_nhds hs)
  exact (h.sub (hTail.analyticAt s)).congr
    (Eventually.of_forall fun z ↦ by simp [higherRemainder_eq r])

private theorem phiRContinuation_sub_main {r : ℕ} (hr : 2 ≤ r) {s : ℂ}
    (hs : (r : ℝ) - 1 < s.re) :
    phiRContinuation q r s - phiRMain q r s =
      ((r.choose 2 : ℂ) * principalWeight q ^ (r - 2) / Gamma s) *
        (cauchySquare q (s - r + 2) + holomorphicCorrection q (s - r + 2)) +
      higherSmallMellin q r s / Gamma s := by
  have hw : 0 < (s - r + 2).re := by simp; linarith
  have hΓ := Gamma_ne_zero_of_re_pos hw
  have h₁ : r - 1 = r - 2 + 1 := by omega
  have h₂ : r = r - 2 + 2 := by omega
  have hp₁ : principalWeight q ^ (r - 2) * principalWeight q = principalWeight q ^ (r - 1) := by
    rw [h₁, pow_succ]
  have hp₂ : principalWeight q ^ (r - 2) * principalWeight q ^ 2 = principalWeight q ^ r := by
    rw [← pow_add, ← h₂]
  have hW : W q (s - r + 2) =
      2 * principalWeight q * (Gamma (s - r + 1) * D q (s - r + 1)) -
        principalWeight q ^ 2 / (s - r) := by
    unfold W
    rw [show s - (r : ℂ) + 2 - 1 = s - r + 1 by ring,
      show s - (r : ℂ) + 2 - 2 = s - r by ring]
  have hbinary : Gamma (s - r + 2) * phi2Continuation q (s - r + 2) =
      W q (s - r + 2) + cauchySquare q (s - r + 2) + holomorphicCorrection q (s - r + 2) := by
    rw [phi2Continuation, ← mul_assoc, mul_inv_cancel₀ hΓ, one_mul]
  unfold phiRContinuation higherCorrection higherCoefficient phiRMain
  rw [mul_assoc (Gamma s)⁻¹, mul_assoc (binaryFactor q r), hbinary, higherRemainder_eq r, hW]
  unfold binaryFactor linearFactor constantFactor
  simp only [div_eq_mul_inv]
  linear_combination
    ((Gamma s)⁻¹ * (r.choose 2 : ℂ) * 2 *
      (Gamma (s - r + 1) * D q (s - r + 1))) * hp₁ -
    ((Gamma s)⁻¹ * (r.choose 2 : ℂ) * (s - r)⁻¹) * hp₂

private theorem lFunction_inv_eq_conj (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : s ≠ 1) :
    (χ⁻¹).LFunction s = conj (χ.LFunction (conj s)) := by
  have hconn : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected
  refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (𝕜 := ℂ)
    (f := (χ⁻¹).LFunction) (g := fun z : ℂ ↦ conj (χ.LFunction (conj z)))
    (U := ({1}ᶜ : Set ℂ)) (z₀ := (2 : ℂ)) ?_ ?_ hconn (by simp) ?_ hs
  · exact analyticOnNhd_lFunction _
  · apply DifferentiableOn.analyticOnNhd _ isOpen_compl_singleton
    intro z hz
    have hzc : conj z ≠ 1 := by
      intro h
      exact hz (by simpa using congrArg conj h)
    have hd : DifferentiableAt ℂ (conj ∘ χ.LFunction ∘ conj) z :=
      differentiableAt_conj_conj_iff.mpr (χ.differentiableAt_LFunction (conj z) (.inl hzc))
    exact hd.differentiableWithinAt
  · filter_upwards [(isOpen_halfPlane 1).mem_nhds (show (2 : ℂ) ∈ halfPlane 1 by norm_num [halfPlane])]
      with z hz
    have hz' : 1 < z.re := hz
    rw [DirichletCharacter.LFunction_eq_LSeries _ hz',
      DirichletCharacter.LFunction_eq_LSeries _ (by simpa : 1 < (conj z).re), LSeries, LSeries,
      Complex.conj_tsum]
    apply tsum_congr
    intro n
    by_cases hn : n = 0
    · simp [hn]
    · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, map_div₀,
        ← MulChar.star_apply', Complex.cpow_conj _ _ (by simp [Real.pi_ne_zero.symm])]
      simp

private theorem logDeriv_lFunction_inv_eq_conj (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : s ≠ 1) :
    logDeriv (χ⁻¹).LFunction s = conj (logDeriv χ.LFunction (conj s)) := by
  have hEq : (χ⁻¹).LFunction =ᶠ[𝓝 s] conj ∘ χ.LFunction ∘ conj := by
    filter_upwards [isOpen_compl_singleton.mem_nhds (show s ∈ ({1}ᶜ : Set ℂ) from hs)]
      with z hz using lFunction_inv_eq_conj χ hz
  rw [logDeriv_apply, logDeriv_apply, hEq.deriv_eq, deriv_conj_conj, lFunction_inv_eq_conj χ hs]
  simp

private theorem D_conj {s : ℂ} (hs : s ≠ 1) : D q (conj s) = conj (D q s) := by
  have hsc : conj s ≠ 1 := by
    intro h
    exact hs (by simpa using congrArg conj h)
  unfold D
  rw [map_mul, map_inv₀, conj_natCast, map_sum]
  congr 1
  calc
    _ = ∑ χ : DirichletCharacter ℂ q, -logDeriv (χ⁻¹).LFunction (conj s) :=
      (Equiv.sum_comp (Equiv.inv (DirichletCharacter ℂ q)) _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro χ _
      rw [logDeriv_lFunction_inv_eq_conj χ hsc, conj_conj, map_neg]

private theorem criticalPoint_neg (t : ℝ) : criticalPoint (-t) = conj (criticalPoint t) := by
  apply Complex.ext <;> simp [criticalPoint_re, criticalPoint_im]

private theorem ordinateWeight_neg (t : ℝ) : ordinateWeight q (-t) = ordinateWeight q t := by
  let z := criticalPoint t
  have hz : z ≠ 1 := by intro h; have := congrArg Complex.re h; norm_num [z, criticalPoint_re] at this
  have hzc : conj z ≠ 1 := by intro h; exact hz (by simpa using congrArg conj h)
  have hr := hasResidue_D (q := q) (s := z) (by norm_num [z, criticalPoint_re]) hz
  have hrc := hasResidue_D (q := q) (s := conj z) (by norm_num [z, criticalPoint_re]) hzc
  have hc : Tendsto (fun w : ℂ ↦ conj w) (𝓝[≠] (conj z)) (𝓝[≠] z) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · simpa using (continuous_conj.tendsto (conj z)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with w hw
      intro h
      exact hw (by simpa using congrArg conj h)
  have htransport : HasResidue (D q) (conj z)
      (conj (-(q.totient : ℂ)⁻¹ * (totalMult q z : ℂ))) := by
    refine ((continuous_conj.tendsto _).comp (hr.comp hc)).congr' ?_
    filter_upwards [(isOpen_compl_singleton.mem_nhds (show conj z ∈ ({1}ᶜ : Set ℂ) from hzc))
      |> eventually_nhdsWithin_of_eventually_nhds] with w hw
    simp only [Function.comp_apply, map_mul, map_sub, conj_conj, D_conj hw]
  have he := hrc.unique htransport
  simp only [map_mul, map_neg, map_inv₀, conj_natCast] at he
  have hφ : -(q.totient : ℂ)⁻¹ ≠ 0 :=
    neg_ne_zero.mpr (inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (NeZero.pos q)).ne'))
  rw [ordinateWeight, ordinateWeight, criticalPoint_neg]
  exact_mod_cast mul_left_cancel₀ hφ he

private theorem gammaWeight_neg (t : ℝ) : gammaWeight q (-t) = conj (gammaWeight q t) := by
  simp [gammaWeight, principalWeight, ordinateWeight_neg, criticalPoint_neg, Gamma_conj]

private def zeroPairEquiv (q : ℕ) [NeZero q] : Ordinates q ≃ pairFibre q 0 where
  toFun t := ⟨(t, ⟨-(t : ℝ), by simpa [Ordinates, ordinateWeight_neg] using t.2⟩), by
    change (t : ℝ) + -(t : ℝ) = 0
    exact add_neg_cancel _⟩
  invFun p := p.1.1
  left_inv _ := rfl
  right_inv p := by
    apply Subtype.ext
    refine Prod.ext rfl (Subtype.ext ?_)
    have hp : (p.1.1 : ℝ) + (p.1.2 : ℝ) = 0 := p.2
    change -(p.1.1 : ℝ) = (p.1.2 : ℝ)
    linarith

private theorem pairResidue_zero (hGRH : GRH q) :
    pairResidue q 0 = ((q.totient : ℂ)⁻¹ ^ 2) *
      ((∑' t : Ordinates q, (ordinateWeight q t : ℝ) ^ 2 * ‖Gamma (criticalPoint t)‖ ^ 2 : ℝ) : ℂ) ∧
    0 < ∑' t : Ordinates q, (ordinateWeight q t : ℝ) ^ 2 * ‖Gamma (criticalPoint t)‖ ^ 2 := by
  let weight (t : Ordinates q) : ℝ := (ordinateWeight q t : ℝ) ^ 2 * ‖Gamma (criticalPoint t)‖ ^ 2
  let scale : ℂ := (q.totient : ℂ)⁻¹ ^ 2
  have hterm (t : Ordinates q) : pairWeight q (zeroPairEquiv q t).1 = scale * (weight t : ℂ) := by
    change gammaWeight q t * gammaWeight q (-(t : ℝ)) = _
    rw [gammaWeight_neg]
    calc
      _ = scale * ((ordinateWeight q t : ℂ) ^ 2 *
          (Gamma (criticalPoint t) * conj (Gamma (criticalPoint t)))) := by
        simp only [gammaWeight, map_mul, conj_natCast, principalWeight, map_inv₀, scale]
        ring
      _ = _ := by
        rw [mul_conj, normSq_eq_norm_sq]
        simp only [weight, ofReal_mul, ofReal_pow, ofReal_natCast]
  constructor
  · unfold pairResidue
    rw [← (zeroPairEquiv q).tsum_eq (fun p : pairFibre q 0 ↦ pairWeight q p.1)]
    simp_rw [hterm]
    rw [tsum_mul_left, ofReal_tsum]
  · have hsum := ((zeroPairEquiv q).summable_iff.mpr
      ((summable_norm_pairWeight hGRH).of_norm.subtype (pairFibre q 0))).congr hterm
    have hscale : scale ≠ 0 :=
      pow_ne_zero _ (inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (NeZero.pos q)).ne'))
    have hsum' : Summable (fun t : Ordinates q ↦ (weight t : ℂ)) := by
      simpa only [← mul_assoc, inv_mul_cancel₀ hscale, one_mul] using hsum.mul_left scale⁻¹
    obtain ⟨ρ, hρ, -⟩ := exists_nontrivialZero_im_gt 0
    have hρ' : ρ.re = 1 / 2 := hGRH 1 ρ ((primitiveZeros_one (q := q)).symm ▸ hρ)
    let t : Ordinates q := ⟨ρ.im, mem_Ordinates_of_zetaZero hρ hρ'⟩
    have hm : 0 < (ordinateWeight q t : ℝ) := by
      exact_mod_cast (show 0 < ordinateWeight q t from t.2)
    have hΓ : 0 < ‖Gamma (criticalPoint t)‖ :=
      norm_pos_iff.mpr (Gamma_ne_zero_of_re_pos (by rw [criticalPoint_re]; norm_num))
    exact (Complex.summable_ofReal.mp hsum').tsum_pos (fun u ↦ by dsimp [weight]; positivity)
      t (by dsimp [weight]; positivity)

private theorem tendsto_sub_main_at_real (hGRH : GRH q) (hZ3 : Paper2.Z3)
    (hLocal : LogDerivPrimitiveLocal q) {r : ℕ} (hr : 2 ≤ r) :
    Tendsto (fun η : ℝ ↦ (η : ℂ) *
      (phiRContinuation q r ((r : ℂ) - 1 + η) - phiRMain q r ((r : ℂ) - 1 + η)))
      (𝓝[>] 0)
      (𝓝 ((r.choose 2 : ℂ) * principalWeight q ^ (r - 2) / Gamma ((r : ℂ) - 1) * pairResidue q 0)) := by
  let s₀ : ℂ := (r : ℂ) - 1
  have hre : s₀.re = (r : ℝ) - 1 := by simp [s₀]
  have hη : Tendsto (fun η : ℝ ↦ (η : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (continuous_ofReal.tendsto 0).mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have hs : Tendsto (fun η : ℝ ↦ s₀ + (η : ℂ)) (𝓝[>] 0) (𝓝 s₀) := by
    simpa using hη.const_add s₀
  have hcoef : ContinuousAt (fun s ↦ (r.choose 2 : ℂ) * principalWeight q ^ (r - 2) / Gamma s) s₀ := by
    simp only [div_eq_mul_inv]
    exact continuousAt_const.mul (PhiRProof.analyticAt_inv_Gamma s₀).continuousAt
  have hrest : ContinuousAt (fun s ↦ higherSmallMellin q r s / Gamma s) s₀ := by
    simp only [div_eq_mul_inv]
    exact (analyticAt_higherSmallMellin hGRH hZ3 hLocal hr (by rw [hre]; linarith)).continuousAt.mul
      (PhiRProof.analyticAt_inv_Gamma s₀).continuousAt
  have hbinary := tendsto_radial_regularPart hGRH hZ3 hLocal 0
  simp only [ofReal_zero, zero_mul, add_zero] at hbinary
  have h := (hcoef.tendsto.comp hs).mul hbinary |>.add (hη.mul (hrest.tendsto.comp hs))
  simp only [zero_mul, add_zero, Function.comp_apply] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0)] with η hηpos
  have hpoint : (r : ℝ) - 1 < (s₀ + (η : ℂ)).re := by
    simpa [hre] using (mem_Ioi.mp hηpos : 0 < η)
  change _ = (η : ℂ) * (phiRContinuation q r (s₀ + η) - phiRMain q r (s₀ + η))
  rw [phiRContinuation_sub_main hr hpoint, show s₀ + η - r + 2 = 1 + (η : ℂ) by dsimp [s₀]; ring]
  ring

/-- The right-hand real limit of the regularized class-one series
equals the strictly positive sum of the squared aggregate Gamma weights with
the stated totient and factorial normalization. -/
theorem phiR_sub_main_real_limit (_hq : 2 ≤ q) (hGRH : GRH q) (hZ3 : Paper2.Z3)
    (hLocal : LogDerivPrimitiveLocal q) {r : ℕ} (hr : 2 ≤ r) :
    Tendsto (fun η : ℝ ↦ (η : ℂ) *
      (phiRContinuation q r ((r : ℂ) - 1 + η) - phiRMain q r ((r : ℂ) - 1 + η))) (𝓝[>] 0)
      (𝓝 (((r.choose 2 : ℝ) / ((q.totient : ℝ) ^ r * ((r - 2).factorial : ℝ)) *
        ∑' t : Ordinates q, (ordinateWeight q t : ℝ) ^ 2 * ‖Gamma (criticalPoint t)‖ ^ 2 : ℝ) : ℂ)) ∧
    0 < (r.choose 2 : ℝ) / ((q.totient : ℝ) ^ r * ((r - 2).factorial : ℝ)) *
      ∑' t : Ordinates q, (ordinateWeight q t : ℝ) ^ 2 * ‖Gamma (criticalPoint t)‖ ^ 2 := by
  obtain ⟨hpair, hpos⟩ := pairResidue_zero hGRH
  have hΓ : Gamma ((r : ℂ) - 1) = ((r - 2).factorial : ℂ) := by
    rw [show (r : ℂ) - 1 = ((r - 2 : ℕ) : ℂ) + 1 by rw [Nat.cast_sub hr]; ring]
    exact Gamma_nat_eq_factorial (r - 2)
  constructor
  · have h := tendsto_sub_main_at_real hGRH hZ3 hLocal hr
    rw [hΓ, hpair] at h
    convert h using 2
    simp only [ofReal_mul, ofReal_div, ofReal_pow, ofReal_natCast, principalWeight]
    simp only [div_eq_mul_inv, mul_inv, ← inv_pow]
    have hp : ((q.totient : ℂ)⁻¹) ^ r =
        ((q.totient : ℂ)⁻¹) ^ (r - 2) * ((q.totient : ℂ)⁻¹) ^ 2 := by
      rw [← pow_add, show r - 2 + 2 = r by omega]
    rw [hp]
    ring
  · have hc : 0 < (r.choose 2 : ℝ) := by exact_mod_cast Nat.choose_pos hr
    have hφ : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
    exact mul_pos (div_pos hc (by positivity)) hpos

#print axioms phiR_sub_main_real_limit

end GoldbachBoundaries.ResidueClass
