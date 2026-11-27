import GoldbachBoundaries.ResidueClass.TwoEulerDeletion

/-! # The holomorphic Mellin remainder for the deletion at two -/

noncomputable section

open Complex Filter Set MeasureTheory Asymptotics
open scoped Topology

namespace GoldbachBoundaries.ResidueClass

open Phi2Proof (FL hL)
open Phi2Proof.FillA (FL_continuousOn_and_le_exp FL_nonneg' norm_hL_le')

local notation "f₂" => smoothed 2

/-- The difference of the two heat powers after removal of the term linear in
the deleted heat sum, with the other factors replaced by the leading heat term. -/
def twoHeatRemainder (r : ℕ) (x : ℝ) : ℝ :=
  FL x ^ r - f₂ x ^ r - (r : ℝ) * x⁻¹ ^ (r - 1) * deletedTwoHeat x

private theorem abs_sub_pow_linear_le {a b m D E : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hm : 0 ≤ m) (hba : b ≤ a)
    (haD : a ≤ D) (hmD : m ≤ D) (haE : |a - m| ≤ E) (hbE : |b - m| ≤ E)
    {r : ℕ} (hr : 2 ≤ r) :
    |a ^ r - b ^ r - (r : ℝ) * m ^ (r - 1) * (a - b)| ≤
      (a - b) * ((r : ℝ) * ((r : ℝ) - 1)) * D ^ (r - 2) * E := by
  have hD : 0 ≤ D := ha.trans haD
  have hE : 0 ≤ E := (abs_nonneg _).trans haE
  have hp : 0 ≤ a - b := sub_nonneg.mpr hba
  induction r, hr using Nat.le_induction with
  | base =>
    rw [show a ^ 2 - b ^ 2 - (2 : ℕ) * m ^ (2 - 1 : ℕ) * (a - b) =
      (a - b) * ((a - m) + (b - m)) by norm_num; ring, abs_mul, abs_of_nonneg hp]
    norm_num
    calc
      _ ≤ (a - b) * (|a - m| + |b - m|) :=
        mul_le_mul_of_nonneg_left (abs_add_le _ _) hp
      _ ≤ _ := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (by linarith) hp
  | succ n hn ih =>
    let R := a ^ n - b ^ n - (n : ℝ) * m ^ (n - 1) * (a - b)
    have hpred : n - 1 + 1 = n := by omega
    have hpred₂ : n - 2 + 1 = n - 1 := by omega
    have hmstep : m ^ n = m ^ (n - 1) * m := by
      conv_lhs => rw [← hpred, pow_succ]
    have hsplit : a ^ (n + 1) - b ^ (n + 1) -
          (↑(n + 1) : ℝ) * m ^ (n + 1 - 1) * (a - b) =
        a * R + (a - b) * (b ^ n - m ^ n) +
          (a - b) * (n : ℝ) * m ^ (n - 1) * (a - m) := by
      rw [Nat.add_sub_cancel, Nat.cast_succ, pow_succ a, pow_succ b, hmstep]
      dsimp [R]
      ring
    have hB : |b ^ n - m ^ n| ≤ E * (n : ℝ) * D ^ (n - 1) := by
      refine (abs_pow_sub_pow_le (a := b) (b := m) (n := n)).trans ?_
      rw [abs_of_nonneg hb, abs_of_nonneg hm]
      gcongr
      exact max_le (hba.trans haD) hmD
    have hM := pow_le_pow_left₀ hm hmD (n - 1)
    have hR : |R| ≤ (a - b) * ((n : ℝ) * ((n : ℝ) - 1)) * D ^ (n - 2) * E := ih
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    rw [hsplit]
    calc
      _ ≤ (|a * R| + |(a - b) * (b ^ n - m ^ n)|) +
          |(a - b) * (n : ℝ) * m ^ (n - 1) * (a - m)| :=
        (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
      _ ≤ (D * ((a - b) * ((n : ℝ) * ((n : ℝ) - 1)) * D ^ (n - 2) * E) +
          (a - b) * (E * (n : ℝ) * D ^ (n - 1))) +
          (a - b) * (n : ℝ) * D ^ (n - 1) * E := by
        simp only [abs_mul, abs_of_nonneg ha, abs_of_nonneg hp,
          abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n), abs_of_nonneg (pow_nonneg hm _)]
        gcongr
      _ = _ := by
        rw [Nat.cast_succ, show n + 1 - 2 = n - 1 by omega,
          ← hpred₂, pow_succ]
        ring

private theorem smoothed_two_le_FL {x : ℝ} (hx : 0 < x) : f₂ x ≤ FL x :=
  (summable_smoothed_terms 2 hx).tsum_le_tsum
    (fun n ↦ mul_le_mul_of_nonneg_right (mangoldtOne_le 2 n) (Real.exp_pos _).le)
    (Phi2Proof.FillA.summable_vonMangoldt_mul_exp_neg hx)

/-- An arbitrary positive power loss over the exponent in the paper suffices
to take the Mellin transform on the full open half-plane. -/
theorem abs_twoHeatRemainder_le (hRH : RiemannHypothesis) {r : ℕ} (hr : 2 ≤ r)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, ∀ x ∈ Ioc (0 : ℝ) 1,
      |twoHeatRemainder r x| ≤ C * x ^ (-((r : ℝ) - 3 / 2 + δ)) := by
  let ε := min (δ / 2) (1 / 4)
  let b := 1 / 2 + ε
  have hε : 0 < ε := lt_min (half_pos hδ) (by norm_num)
  have hε₄ : ε ≤ 1 / 4 := min_le_right _ _
  have hεδ : ε ≤ δ / 2 := min_le_left _ _
  have hb : 1 / 2 < b := by dsimp [b]; linarith
  have hb₁ : b < 1 := by dsimp [b]; linarith
  obtain ⟨K, hK⟩ := norm_hL_le' hRH hb hb₁
  obtain ⟨C, hC₀, hC⟩ := deletedTwoHeat_le_rpow hε (by linarith)
  let A := max K 0 + 1
  have hA : 1 ≤ A := by dsimp [A]; linarith [le_max_right K (0 : ℝ)]
  refine ⟨C * ((r : ℝ) * ((r : ℝ) - 1)) * A ^ (r - 2) * (max K 0 + C), ?_⟩
  intro x hx
  have hx₀ : 0 < x := hx.1
  have hx₁ : x ≤ 1 := hx.2
  have hpower : x ^ (-b) ≤ x⁻¹ := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_ge hx₀ hx₁ (by linarith)
  have hPpower : x ^ (-ε) ≤ x ^ (-b) :=
    Real.rpow_le_rpow_of_exponent_ge hx₀ hx₁ (by dsimp [b]; linarith)
  have hP := (hC x hx₀).trans (mul_le_mul_of_nonneg_left hPpower hC₀)
  have hF : |FL x - x⁻¹| ≤ max K 0 * x ^ (-b) := by
    have h := (hK x hx₀).trans (mul_le_mul_of_nonneg_right
      (le_max_left K 0) (Real.rpow_nonneg hx₀.le _))
    simpa only [hL, one_div] using h
  have hFx : FL x ≤ A * x⁻¹ := by
    have h := (le_abs_self (FL x - x⁻¹)).trans (hF.trans
      (mul_le_mul_of_nonneg_left hpower (le_max_right K 0)))
    dsimp [A]
    linarith [add_mul (max K 0) 1 x⁻¹]
  have hdiff := FL_sub_smoothed_two hx₀
  have hG : |f₂ x - x⁻¹| ≤ (max K 0 + C) * x ^ (-b) := by
    rw [show f₂ x - x⁻¹ = (FL x - x⁻¹) - deletedTwoHeat x by linarith, add_mul]
    have htri := abs_add_le (FL x - x⁻¹) (-deletedTwoHeat x)
    rw [← sub_eq_add_neg, abs_neg, abs_of_nonneg (deletedTwoHeat_nonneg x)] at htri
    exact htri.trans (add_le_add hF hP)
  have hF' := hF.trans (le_add_of_nonneg_right (mul_nonneg hC₀ (Real.rpow_nonneg hx₀.le _))
    : max K 0 * x ^ (-b) ≤ max K 0 * x ^ (-b) + C * x ^ (-b))
  rw [← add_mul] at hF'
  have h := abs_sub_pow_linear_le (FL_nonneg' x) (smoothed_nonneg 2 x) (inv_nonneg.mpr hx₀.le)
    (smoothed_two_le_FL hx₀) hFx
    (le_mul_of_one_le_left (inv_nonneg.mpr hx₀.le) hA) hF' hG hr
  rw [hdiff] at h
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hr₀ : 0 ≤ (r : ℝ) * ((r : ℝ) - 1) :=
    mul_nonneg (Nat.cast_nonneg _) (by linarith)
  have hA₀ : 0 ≤ A := zero_le_one.trans hA
  calc
    _ ≤ deletedTwoHeat x * ((r : ℝ) * ((r : ℝ) - 1)) *
          (A * x⁻¹) ^ (r - 2) * ((max K 0 + C) * x ^ (-b)) := h
    _ ≤ (C * x ^ (-ε)) * ((r : ℝ) * ((r : ℝ) - 1)) *
          (A * x⁻¹) ^ (r - 2) * ((max K 0 + C) * x ^ (-b)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right (hC x hx₀) hr₀
    _ = (C * ((r : ℝ) * ((r : ℝ) - 1)) * A ^ (r - 2) * (max K 0 + C)) *
          x ^ (-((r : ℝ) - 2 + b + ε)) := by
      rw [mul_pow, inv_pow, ← Real.rpow_natCast x (r - 2), ← Real.rpow_neg hx₀.le,
        Nat.cast_sub hr, Nat.cast_ofNat]
      rw [show -((r : ℝ) - 2 + b + ε) = -ε + (-((r : ℝ) - 2) + -b) by ring]
      rw [Real.rpow_add hx₀, Real.rpow_add hx₀]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge hx₀ hx₁ (by dsimp [b]; linarith)) (by positivity)

private def twoHeatRemainderC (r : ℕ) (x : ℝ) : ℂ := twoHeatRemainder r x

private theorem continuousOn_twoHeatRemainderC (r : ℕ) :
    ContinuousOn (twoHeatRemainderC r) (Ioi 0) := by
  have hF := FL_continuousOn_and_le_exp.1
  have hInv : ContinuousOn (fun x : ℝ ↦ x⁻¹) (Ioi 0) :=
    continuousOn_id.inv₀ (fun _ hx ↦ (mem_Ioi.mp hx).ne')
  exact continuous_ofReal.comp_continuousOn
    (((hF.pow r).sub ((continuousOn_smoothed 2).pow r)).sub
      ((continuousOn_const.mul (hInv.pow (r - 1))).mul continuousOn_deletedTwoHeat))

private theorem twoHeatRemainder_atTop {r : ℕ} (hr : 2 ≤ r) :
    twoHeatRemainderC r =O[atTop] fun x ↦ Real.exp (-(1 : ℝ) * x) := by
  obtain ⟨C, hC⟩ := FL_continuousOn_and_le_exp.2
  let K := max C 0
  have hK : 0 ≤ K := le_max_right _ _
  refine IsBigO.of_bound (K ^ r + (r : ℝ) * K) ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx₀ : 0 < x := zero_lt_one.trans_le hx
  have hG := smoothed_two_le_FL hx₀
  have hd := FL_sub_smoothed_two hx₀
  have hP₀ := deletedTwoHeat_nonneg x
  have hP : deletedTwoHeat x ≤ FL x := by rw [← hd]; linarith [smoothed_nonneg 2 x]
  have he₀ := (Real.exp_pos (-x)).le
  have he₁ := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx₀.le)
  have hFx : FL x ≤ K * Real.exp (-x) :=
    (hC x hx).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) he₀)
  have hpow : FL x ^ r ≤ K ^ r * Real.exp (-x) := by
    calc
      _ ≤ (K * Real.exp (-x)) ^ r := pow_le_pow_left₀ (FL_nonneg' x) hFx _
      _ = K ^ r * Real.exp (-x) ^ r := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (by simpa only [pow_one] using pow_le_pow_of_le_one he₀ he₁ (show 1 ≤ r by omega))
        (pow_nonneg hK _)
  have hInv : x⁻¹ ^ (r - 1) ≤ 1 :=
    pow_le_one₀ (inv_nonneg.mpr hx₀.le) (inv_le_one_of_one_le₀ hx)
  rw [twoHeatRemainderC, norm_real, Real.norm_eq_abs, twoHeatRemainder, neg_one_mul,
    Real.norm_of_nonneg he₀, add_mul]
  have htri := abs_add_le (FL x ^ r - f₂ x ^ r) (-(↑r * x⁻¹ ^ (r - 1) * deletedTwoHeat x))
  rw [← sub_eq_add_neg, abs_neg] at htri
  refine htri.trans (add_le_add ?_ ?_)
  · rw [abs_of_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ (smoothed_nonneg 2 x) hG r))]
    exact (sub_le_self _ (pow_nonneg (smoothed_nonneg 2 x) _)).trans hpow
  · rw [abs_of_nonneg (by positivity : 0 ≤ (r : ℝ) * x⁻¹ ^ (r - 1) * deletedTwoHeat x), mul_assoc]
    refine mul_le_mul_of_nonneg_left (?_ : _ ≤ K * Real.exp (-x)) (Nat.cast_nonneg _) |>.trans_eq ?_
    · exact (mul_le_of_le_one_left hP₀ hInv).trans (hP.trans hFx)
    · ring

private theorem twoHeatRemainder_atZero (hRH : RiemannHypothesis) {r : ℕ} (hr : 2 ≤ r)
    {δ : ℝ} (hδ : 0 < δ) :
    twoHeatRemainderC r =O[𝓝[>] 0] fun x ↦ x ^ (-((r : ℝ) - 3 / 2 + δ)) := by
  obtain ⟨C, hC⟩ := abs_twoHeatRemainder_le hRH hr hδ
  refine IsBigO.of_bound C ?_
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds]
    with x (hx : 0 < x) hx₁
  simpa only [twoHeatRemainderC, norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hx.le _)] using hC x ⟨hx, hx₁.le⟩

private theorem mellin_twoHeatRemainder (hRH : RiemannHypothesis) {r : ℕ} (hr : 2 ≤ r)
    {s : ℂ} (hs : (r : ℝ) - 3 / 2 < s.re) :
    MellinConvergent (twoHeatRemainderC r) s ∧
      DifferentiableAt ℂ (mellin (twoHeatRemainderC r)) s := by
  obtain ⟨a, ha, has⟩ := exists_between hs
  have hbot := twoHeatRemainder_atZero hRH hr (show 0 < a - ((r : ℝ) - 3 / 2) by linarith)
  rw [add_sub_cancel] at hbot
  have hlocal := (continuousOn_twoHeatRemainderC r).locallyIntegrableOn (μ := volume) measurableSet_Ioi
  have htop := twoHeatRemainder_atTop hr
  exact ⟨mellinConvergent_of_isBigO_rpow_exp one_pos hlocal htop hbot has,
    mellin_differentiableAt_of_isBigO_rpow_exp one_pos hlocal htop hbot has⟩

/-- The Euler-factor contribution after shifting the Mellin variable by r − 1
and dividing by the original Gamma factor. -/
def twoEulerCorrection (r : ℕ) (s : ℂ) : ℂ :=
  let z := s - r + 1
  (r : ℂ) * (Real.log 2 : ℂ) * Gamma z * (2 : ℂ) ^ (-z) /
    (Gamma s * (1 - (2 : ℂ) ^ (-z)))

/-- The Mellin remainder after dividing by Gamma. -/
def twoHolomorphicRemainder (r : ℕ) (s : ℂ) : ℂ :=
  mellin (twoHeatRemainderC r) s / Gamma s

theorem analyticOnNhd_twoHolomorphicRemainder (hRH : RiemannHypothesis) {r : ℕ} (hr : 2 ≤ r) :
    AnalyticOnNhd ℂ (twoHolomorphicRemainder r) (halfPlane ((r : ℝ) - 3 / 2)) := by
  refine DifferentiableOn.analyticOnNhd ?_ (isOpen_halfPlane _)
  intro s hs
  have h := ((mellin_twoHeatRemainder hRH hr hs).2.mul
    (differentiable_one_div_Gamma s)).differentiableWithinAt (s := halfPlane ((r : ℝ) - 3 / 2))
  change DifferentiableWithinAt ℂ (fun z ↦ mellin (twoHeatRemainderC r) z / Gamma z) _ s
  simpa only [div_eq_mul_inv, one_div, Pi.mul_def] using h

private def linearTwoHeat (r : ℕ) (x : ℝ) : ℂ :=
  (r : ℂ) • ((x : ℂ) ^ (-(↑(r - 1) : ℂ)) • (deletedTwoHeat x : ℂ))

private theorem heat_split (r : ℕ) (x : ℝ) :
    ((FL x ^ r : ℝ) : ℂ) = ((f₂ x ^ r : ℝ) : ℂ) + linearTwoHeat r x + twoHeatRemainderC r x := by
  simp only [linearTwoHeat, smul_eq_mul, cpow_neg, cpow_natCast, twoHeatRemainderC,
    twoHeatRemainder]
  push_cast
  rw [inv_pow]
  ring

/-- The corrected difference equals the holomorphic Mellin remainder on the
half-plane of absolute convergence. -/
theorem eqOn_twoHolomorphicRemainder (hRH : RiemannHypothesis) {r : ℕ} (hr : 2 ≤ r) :
    EqOn (twoHolomorphicRemainder r)
      (fun s ↦ GoldbachBoundaries.PhiR r s - PhiR 2 r s - twoEulerCorrection r s)
      (halfPlane r) := by
  intro s (hs : (r : ℝ) < s.re)
  have hr₁ : 1 ≤ r := by omega
  let z := s - r + 1
  have hz : 0 < z.re := by
    change 0 < (s - (r : ℂ) + 1).re
    simp only [add_re, sub_re, natCast_re, one_re]
    linarith
  have hshift : s + (-(↑(r - 1) : ℂ)) = z := by
    rw [Nat.cast_sub hr₁, Nat.cast_one]
    dsimp [z]
    ring
  obtain ⟨hp, hvp⟩ := mellin_deletedTwoHeat hz
  have hl : MellinConvergent (linearTwoHeat r) s :=
    ((MellinConvergent.cpow_smul).mpr (hshift.symm ▸ hp)).const_smul (r : ℂ)
  have hvl : mellin (linearTwoHeat r) s =
      (r : ℂ) * (Gamma z * (Real.log 2 : ℂ) * (2 : ℂ) ^ (-z) / (1 - (2 : ℂ) ^ (-z))) := by
    change mellin (fun x : ℝ ↦ (r : ℂ) • ((x : ℂ) ^ (-(↑(r - 1) : ℂ)) •
      (deletedTwoHeat x : ℂ))) s = _
    rw [mellin_const_smul, mellin_cpow_smul, hshift, hvp, smul_eq_mul]
  obtain ⟨hg, hvg⟩ := mellin_smoothed_pow 2 hr₁ hs
  have hrem := (mellin_twoHeatRemainder hRH hr (s := s) (by linarith)).1
  have hsum : Gamma s * GoldbachBoundaries.PhiR r s =
      Gamma s * PhiR 2 r s + mellin (linearTwoHeat r) s + mellin (twoHeatRemainderC r) s := by
    rw [← (PhiRProof.FillA.mellin_FL_pow' hr₁ hs).2, ← hvg]
    simp only [mellin, smul_eq_mul]
    unfold MellinConvergent at hg hl hrem
    simp only [smul_eq_mul] at hg hl hrem
    calc
      _ = ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) *
          (((f₂ x ^ r : ℝ) : ℂ) + linearTwoHeat r x + twoHeatRemainderC r x) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x _
        change ((FL x ^ r : ℝ) : ℂ) * _ = _ * (_ + _ + _)
        rw [← heat_split r, mul_comm]
      _ = _ := by
        simp only [mul_add]
        have hadd := integral_add (hg.add hl) hrem
        simp only [Pi.add_apply] at hadd
        rw [integral_add hg hl] at hadd
        exact hadd
  have hΓ := Gamma_ne_zero_of_re_pos ((Nat.cast_nonneg r).trans_lt hs)
  have hcorr : twoEulerCorrection r s = mellin (linearTwoHeat r) s / Gamma s := by
    rw [hvl, twoEulerCorrection]
    change _ * _ * Gamma z * _ / _ = _
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  change mellin (twoHeatRemainderC r) s / Gamma s =
    GoldbachBoundaries.PhiR r s - PhiR 2 r s - twoEulerCorrection r s
  rw [hcorr]
  apply (div_eq_iff hΓ).2
  calc
    mellin (twoHeatRemainderC r) s =
        Gamma s * GoldbachBoundaries.PhiR r s - Gamma s * PhiR 2 r s -
          mellin (linearTwoHeat r) s := by linear_combination -hsum
    _ = _ := by field_simp [hΓ]

end GoldbachBoundaries.ResidueClass
