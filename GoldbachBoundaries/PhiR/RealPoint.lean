import GoldbachBoundaries.PhiR.Proof.M2Continuation
import GoldbachBoundaries.Phi2.Proof.M3Radial

/-! # Radial limits after subtracting the main term -/

noncomputable section

open Complex ComplexConjugate Filter Set Topology

namespace GoldbachBoundaries.PhiRProof

open GoldbachBoundaries.Paper2 GoldbachBoundaries.Phi2Proof

/-- The main term of `Φ_r`, with `ψ = -ζ'/ζ` and `z = s - r + 1`. -/
def phiRMain (r : ℕ) (s : ℂ) : ℂ :=
  ((r : ℂ) * Gamma (s - r + 1) * negLogDerivZeta (s - r + 1) -
    ((r : ℂ) - 1) / (s - r)) / Gamma s

private theorem cast_cC (r : ℕ) : (cC r : ℂ) = (r.choose 2 : ℂ) := by
  rw [Nat.cast_choose_two, cC]
  push_cast
  ring

/-- In the RH Mellin decomposition, subtraction leaves the shifted binary remainder and
the holomorphic term `KR / Γ`. The identity also holds at the totalized pole values. -/
theorem PhiRc_sub_phiRMain {r : ℕ} {s : ℂ} (hs : (r : ℝ) - 1 < s.re) :
    PhiRc r s - phiRMain r s =
      phiRCoef r s * Hphi2 (s - r + 2) + KR r s * (Gamma s)⁻¹ := by
  let z : ℂ := s - r + 1
  let w : ℂ := s - r + 2
  have hzre : 0 < z.re := by simp [z]; linarith
  have hz : z ≠ 0 := fun h => (ne_of_gt hzre) (by simp [h])
  have hw : w = z + 1 := by dsimp [w, z]; ring
  have hΓ : Gamma w ≠ 0 := Gamma_ne_zero_of_re_pos (by rw [hw]; simp; linarith)
  have hmain : Gamma w * phi2Main w = 2 * Gamma z * negLogDerivZeta z - 1 / (s - r) := by
    have hw1 : w - 1 = z := by rw [hw, add_sub_cancel_right]
    have hw2 : w - 2 = s - r := by dsimp [w]; ring
    rw [phi2Main, hw1, hw2, mul_sub]
    congr 1
    · rw [hw, Gamma_add_one z hz, ← mul_div_assoc, mul_assoc, mul_div_cancel_left₀ _ hz]
      ring
    · rw [← div_div, ← mul_div_assoc, mul_one_div_cancel hΓ]
  change phiRCoef r s * Phi2c w + phiRRest r s - phiRMain r s =
    phiRCoef r s * Hphi2 w + KR r s * (Gamma s)⁻¹
  rw [Phi2c, mul_add]
  unfold phiRCoef phiRRest phiRMain
  change (cC r : ℂ) * Gamma w * (Gamma s)⁻¹ * phi2Main w +
      (cC r : ℂ) * Gamma w * (Gamma s)⁻¹ * Hphi2 w +
      ((cB r : ℂ) * Gamma z * negLogDerivZeta z + (cA r : ℂ) / (s - r) + KR r s) * (Gamma s)⁻¹ -
      ((r : ℂ) * Gamma z * negLogDerivZeta z - ((r : ℂ) - 1) / (s - r)) / Gamma s = _
  rw [show (cC r : ℂ) * Gamma w * (Gamma s)⁻¹ * phi2Main w =
    (cC r : ℂ) * (Gamma w * phi2Main w) * (Gamma s)⁻¹ by ring, hmain]
  unfold cA cB cC
  push_cast
  ring

private theorem analyticAt_KR_div_Gamma (hRH : RiemannHypothesis) {r : ℕ} (hr : 2 ≤ r)
    {s : ℂ} (hs : (r : ℝ) - 3 / 2 < s.re) :
    AnalyticAt ℂ (fun z => KR r z * (Gamma z)⁻¹) s :=
  ((differentiableOn_KR hRH hr).analyticOnNhd (isOpen_halfPlane _) s hs).mul
    (analyticAt_inv_Gamma s)

/-- The subtracted continuation is holomorphic on `Re s > r - 1` and has the
stated radial limit at every ordinate, including zero. -/
theorem phiR_sub_main_radial_limit (hRH : RiemannHypothesis) (hZ2 : Z2) (hZ3 : Z3)
    {r : ℕ} (hr : 2 ≤ r) :
    AnalyticOnNhd ℂ (fun s => PhiRc r s - phiRMain r s) (halfPlane ((r : ℝ) - 1)) ∧
    ∀ τ : ℝ, Tendsto (fun η : ℝ => (η : ℂ) *
      (PhiRc r ((r : ℂ) - 1 + τ * I + η) - phiRMain r ((r : ℂ) - 1 + τ * I + η)))
      (𝓝[>] 0) (𝓝 ((r.choose 2 : ℂ) * pairAtom τ / Gamma ((r : ℂ) - 1 + τ * I))) := by
  constructor
  · intro s hs
    change (r : ℝ) - 1 < s.re at hs
    have hw : s - r + 2 ∈ HH := by
      show 1 < (s - r + 2).re
      simp
      linarith
    have hH := (differentiableOn_Hphi2 hRH).analyticOnNhd (isOpen_halfPlane 1) _ hw
    have hshift : AnalyticAt ℂ (fun z : ℂ => Hphi2 (z - r + 2)) s :=
      hH.comp (f := fun z : ℂ => z - r + 2) (by fun_prop)
    have han := ((analyticAt_phiRCoef (by linarith)).mul hshift).add
      (analyticAt_KR_div_Gamma hRH hr (s := s) (by linarith))
    refine han.congr ?_
    filter_upwards [(isOpen_halfPlane ((r : ℝ) - 1)).mem_nhds hs] with z hz
    exact (PhiRc_sub_phiRMain hz).symm
  · intro τ
    let s₀ : ℂ := (r : ℂ) - 1 + τ * I
    have hre : s₀.re = (r : ℝ) - 1 := by simp [s₀]
    have hη : Tendsto (fun η : ℝ => (η : ℂ)) (𝓝[>] 0) (𝓝 0) := by
      simpa using (continuous_ofReal.tendsto 0).mono_left
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    have hs : Tendsto (fun η : ℝ => s₀ + η) (𝓝[>] 0) (𝓝 s₀) := by
      simpa using hη.const_add s₀
    have hCoefAt : AnalyticAt ℂ (phiRCoef r) s₀ :=
      analyticAt_phiRCoef (by rw [hre]; linarith)
    have hCoef := hCoefAt.continuousAt.tendsto.comp hs
    have hRest : Tendsto (fun η : ℝ => (η : ℂ) * (KR r (s₀ + η) * (Gamma (s₀ + η))⁻¹))
        (𝓝[>] 0) (𝓝 0) := by
      have han := analyticAt_KR_div_Gamma hRH hr (s := s₀) (by rw [hre]; linarith)
      have hc := han.continuousAt.tendsto.comp hs
      simpa using hη.mul hc
    have hsum := (hCoef.mul (tendsto_eta_Hphi2 hRH hZ2 hZ3 τ)).add hRest
    have hval : phiRCoef r s₀ * (pairAtom τ / Gamma (1 + τ * I)) + 0 =
        (r.choose 2 : ℂ) * pairAtom τ / Gamma s₀ := by
      have hw : s₀ - r + 2 = 1 + τ * I := by dsimp [s₀]; ring
      have hΓ : Gamma (1 + τ * I) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp)
      rw [add_zero, phiRCoef, hw, cast_cC]
      field_simp
    rw [hval] at hsum
    refine hsum.congr' ?_
    filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0)] with η hηpos
    have hpoint : (r : ℝ) - 1 < (s₀ + η).re := by
      simpa [hre] using (mem_Ioi.mp hηpos : 0 < η)
    have hw : s₀ + η - r + 2 = 1 + τ * I + η := by dsimp [s₀]; ring
    change _ = (η : ℂ) * (PhiRc r (s₀ + η) - phiRMain r (s₀ + η))
    rw [PhiRc_sub_phiRMain hpoint, hw]
    simp only [Function.comp_apply]
    ring

private def zeroPairEquiv (hRH : RiemannHypothesis) : NontrivialZeros ≃ pairIdx 0 where
  toFun ρ := ⟨(ρ, ⟨conj (ρ : ℂ), conj_mem_nontrivialZeros ρ.2⟩), by
    change (ρ : ℂ) + conj (ρ : ℂ) = 1 + ((0 : ℝ) : ℂ) * I
    rw [Complex.add_conj, sigmaFinite_re_eq_half hRH ρ.2]
    norm_num⟩
  invFun p := p.1.1
  left_inv _ := rfl
  right_inv p := by
    apply Subtype.ext
    refine Prod.ext rfl (Subtype.ext ?_)
    change conj (p.1.1 : ℂ) = (p.1.2 : ℂ)
    have hsum : (p.1.1 : ℂ) + (p.1.2 : ℂ) = 1 := by
      simpa using p.2
    have hconj : (p.1.1 : ℂ) + conj (p.1.1 : ℂ) = 1 := by
      rw [Complex.add_conj, sigmaFinite_re_eq_half hRH p.1.1.2]
      norm_num
    exact add_left_cancel (hconj.trans hsum.symm)

private theorem pairAtom_zero (hRH : RiemannHypothesis) (hZ2 : Z2) :
    pairAtom 0 = ((∑' ρ : NontrivialZeros, (zetaMult (ρ : ℂ) : ℝ) ^ 2 *
      ‖Gamma (ρ : ℂ)‖ ^ 2 : ℝ) : ℂ) ∧
    0 < ∑' ρ : NontrivialZeros, (zetaMult (ρ : ℂ) : ℝ) ^ 2 * ‖Gamma (ρ : ℂ)‖ ^ 2 := by
  let weight (ρ : NontrivialZeros) : ℝ := (zetaMult (ρ : ℂ) : ℝ) ^ 2 * ‖Gamma (ρ : ℂ)‖ ^ 2
  let term (p : pairIdx 0) : ℂ := zeroCoef p.1.1 * zeroCoef p.1.2
  have hterm (ρ : NontrivialZeros) : term (zeroPairEquiv hRH ρ) = (weight ρ : ℂ) := by
    change zeroCoef (ρ : ℂ) * zeroCoef (conj (ρ : ℂ)) = _
    rw [zeroCoef, zeroCoef, zetaMult_conj ρ.2, Gamma_conj]
    calc
      _ = (zetaMult (ρ : ℂ) : ℂ) ^ 2 * (Gamma (ρ : ℂ) * conj (Gamma (ρ : ℂ))) := by ring
      _ = _ := by rw [mul_conj, normSq_eq_norm_sq]; simp [weight]
  constructor
  · change (∑' p, term p) = ((∑' ρ, weight ρ : ℝ) : ℂ)
    rw [← (zeroPairEquiv hRH).tsum_eq term, Complex.ofReal_tsum]
    exact tsum_congr hterm
  · have hsum : Summable (fun ρ : NontrivialZeros => (weight ρ : ℂ)) :=
      ((zeroPairEquiv hRH).summable_iff.mpr (tendsto_eta_cauchyT hRH hZ2 0).1).congr hterm
    obtain ⟨ρ, hρ, -⟩ := exists_nontrivialZero_im_gt 0
    have hm : 0 < (zetaMult ρ : ℝ) := by exact_mod_cast (one_le_zetaMult hρ)
    have hΓ : 0 < ‖Gamma ρ‖ := norm_pos_iff.mpr (Gamma_ne_zero_of_re_pos hρ.2.1)
    exact (Complex.summable_ofReal.mp hsum).tsum_pos (fun i => by dsimp [weight]; positivity)
      ⟨ρ, hρ⟩ (by dsimp [weight]; positivity)

/-- At the real boundary point the limit is the strictly positive scaled sum
of `m(ρ)^2 |Γ(ρ)|^2` over the distinct nontrivial zeros. -/
theorem phiR_sub_main_real_limit (hRH : RiemannHypothesis) (hZ2 : Z2) (hZ3 : Z3)
    {r : ℕ} (hr : 2 ≤ r) :
    Tendsto (fun η : ℝ => (η : ℂ) *
      (PhiRc r ((r : ℂ) - 1 + η) - phiRMain r ((r : ℂ) - 1 + η))) (𝓝[>] 0)
      (𝓝 (((r.choose 2 : ℝ) / ((r - 2).factorial : ℝ) *
        ∑' ρ : NontrivialZeros, (zetaMult (ρ : ℂ) : ℝ) ^ 2 * ‖Gamma (ρ : ℂ)‖ ^ 2 : ℝ) : ℂ)) ∧
    0 < (r.choose 2 : ℝ) / ((r - 2).factorial : ℝ) *
      ∑' ρ : NontrivialZeros, (zetaMult (ρ : ℂ) : ℝ) ^ 2 * ‖Gamma (ρ : ℂ)‖ ^ 2 := by
  obtain ⟨hAtom, hpos⟩ := pairAtom_zero hRH hZ2
  have hΓ : Gamma ((r : ℂ) - 1) = ((r - 2).factorial : ℂ) := by
    rw [show (r : ℂ) - 1 = ((r - 2 : ℕ) : ℂ) + 1 by rw [Nat.cast_sub hr]; ring]
    exact Gamma_nat_eq_factorial (r - 2)
  constructor
  · have h := (phiR_sub_main_radial_limit hRH hZ2 hZ3 hr).2 0
    simp only [ofReal_zero, zero_mul, add_zero] at h
    rw [hΓ, hAtom] at h
    convert h using 2
    push_cast
    ring
  · have hc : 0 < (r.choose 2 : ℝ) := by exact_mod_cast Nat.choose_pos hr
    exact mul_pos (div_pos hc (by positivity)) hpos

#print axioms phiR_sub_main_radial_limit
#print axioms phiR_sub_main_real_limit

end GoldbachBoundaries.PhiRProof
