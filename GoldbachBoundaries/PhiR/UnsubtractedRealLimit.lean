import GoldbachBoundaries.PhiR.RealPoint
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.CriticalLineDecay

/-! # The unsubtracted real-point limit -/

noncomputable section

open Complex Filter Set Topology

namespace GoldbachBoundaries.PhiRProof

open GoldbachBoundaries.Paper2 GoldbachBoundaries.Phi2Proof

/-- The mass at ordinate zero, indexed by distinct nontrivial zeros. -/
def muZero : ℝ :=
  ∑' ρ : NontrivialZeros,
    Real.pi * (zetaMult (ρ : ℂ) : ℝ) ^ 2 / Real.cosh (Real.pi * (ρ : ℂ).im)

private theorem zero_weight_eq (hRH : RiemannHypothesis) (ρ : NontrivialZeros) :
    (zetaMult (ρ : ℂ) : ℝ) ^ 2 * ‖Gamma (ρ : ℂ)‖ ^ 2 =
      Real.pi * (zetaMult (ρ : ℂ) : ℝ) ^ 2 / Real.cosh (Real.pi * (ρ : ℂ).im) := by
  have hρ : (ρ : ℂ) = ((1 / 2 : ℝ) : ℂ) + ((ρ : ℂ).im : ℂ) * I := by
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im, sigmaFinite_re_eq_half hRH ρ.2]
  have hGamma : ‖Gamma (ρ : ℂ)‖ ^ 2 = Real.pi / Real.cosh (Real.pi * (ρ : ℂ).im) :=
    (congrArg (fun z => ‖Gamma z‖ ^ 2) hρ).trans (gamma_half_vertical_norm_sq _)
  rw [hGamma]
  ring

/-- Under RH and Z2 the mass at ordinate zero is strictly positive. -/
theorem muZero_pos (hRH : RiemannHypothesis) (hZ2 : Z2) : 0 < muZero := by
  have hsum := summable_norm_zeroCoef hRH hZ2
  have hsq : Summable (fun ρ : NontrivialZeros => ‖zeroCoef ρ‖ ^ 2) := by
    refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun ρ => ?_)
      (hsum.mul_left (∑' ρ : NontrivialZeros, ‖zeroCoef ρ‖))
    rw [sq]
    exact mul_le_mul_of_nonneg_right (hsum.le_tsum ρ (fun _ _ => norm_nonneg _)) (norm_nonneg _)
  have hsumWeight : Summable (fun ρ : NontrivialZeros =>
      Real.pi * (zetaMult (ρ : ℂ) : ℝ) ^ 2 / Real.cosh (Real.pi * (ρ : ℂ).im)) := by
    refine hsq.congr fun ρ => ?_
    rw [zeroCoef, norm_mul, Complex.norm_natCast, mul_pow, zero_weight_eq hRH]
  obtain ⟨ρ, hρ, -⟩ := exists_nontrivialZero_im_gt 0
  have hm : 0 < (zetaMult ρ : ℝ) := by exact_mod_cast (one_le_zetaMult hρ)
  exact hsumWeight.tsum_pos (fun _ => by positivity) ⟨ρ, hρ⟩ (by positivity)

private theorem negLogDerivZeta_at_zero :
    negLogDerivZeta 0 = -(Real.log (2 * Real.pi) : ℂ) := by
  rw [negLogDerivZeta, deriv_riemannZeta_zero, riemannZeta_zero,
    Complex.ofReal_log (by positivity : 0 ≤ 2 * Real.pi)]
  push_cast
  ring

private theorem tendsto_eta_phiRMain_real {r : ℕ} (hr : 2 ≤ r) :
    Tendsto (fun η : ℝ => (η : ℂ) * phiRMain r ((r : ℂ) - 1 + η)) (𝓝[>] 0)
      (𝓝 ((-(r : ℝ) * Real.log (2 * Real.pi) / ((r - 2).factorial : ℝ) : ℝ) : ℂ)) := by
  have hη : Tendsto (fun η : ℝ => (η : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (continuous_ofReal.tendsto 0).mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have hηne : Tendsto (fun η : ℝ => (η : ℂ)) (𝓝[>] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hη, ?_⟩
    filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0)] with η hηpos
    simpa using (ne_of_gt (mem_Ioi.mp hηpos) : η ≠ 0)
  have hηGamma := tendsto_self_mul_Gamma_nhds_zero.comp hηne
  have hψ := (analyticAt_negLogDerivZeta (z := 0) (by norm_num)
    (by rw [riemannZeta_zero]; norm_num)).continuousAt.tendsto.comp hη
  have hshift : Tendsto (fun η : ℝ => (η : ℂ) - 1) (𝓝[>] 0) (𝓝 (-1)) := by
    simpa using hη.sub_const (1 : ℂ)
  have hregular := hη.mul
    (tendsto_const_nhds (x := (r : ℂ) - 1) |>.div hshift (by norm_num))
  have hs : Tendsto (fun η : ℝ => (r : ℂ) - 1 + η) (𝓝[>] 0) (𝓝 ((r : ℂ) - 1)) := by
    simpa using hη.const_add ((r : ℂ) - 1)
  have hGammaAt : ContinuousAt Gamma ((r : ℂ) - 1) := by
    refine continuousAt_Gamma _ fun n hn => ?_
    have hre := congrArg Complex.re hn
    simp at hre
    have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hGamma := hGammaAt.tendsto.comp hs
  have hfactorial : Gamma ((r : ℂ) - 1) = ((r - 2).factorial : ℂ) := by
    rw [show (r : ℂ) - 1 = ((r - 2 : ℕ) : ℂ) + 1 by rw [Nat.cast_sub hr]; ring]
    exact Gamma_nat_eq_factorial (r - 2)
  rw [negLogDerivZeta_at_zero] at hψ
  rw [hfactorial] at hGamma
  have hlimit := (((hηGamma.const_mul (r : ℂ)).mul hψ).sub hregular).div hGamma
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  have hlimit' : Tendsto
      (fun η : ℝ => ((r : ℂ) * ((η : ℂ) * Gamma η) * negLogDerivZeta η -
        (η : ℂ) * (((r : ℂ) - 1) / ((η : ℂ) - 1))) / Gamma ((r : ℂ) - 1 + η))
      (𝓝[>] 0) (𝓝 ((-(r : ℝ) * Real.log (2 * Real.pi) / ((r - 2).factorial : ℝ) : ℝ) : ℂ)) := by
    simpa only [Pi.div_def, Function.comp_apply, mul_one, zero_mul, sub_zero, ofReal_div, ofReal_mul,
      ofReal_neg, ofReal_natCast, mul_neg, neg_mul] using hlimit
  refine hlimit'.congr fun η => ?_
  rw [phiRMain, show (r : ℂ) - 1 + η - r + 1 = η by ring,
    show (r : ℂ) - 1 + η - r = (η : ℂ) - 1 by ring, ← mul_div_assoc, mul_sub]
  ring

/-- The unsubtracted limit from the class-one paper, real-point limits. -/
theorem phiR_real_limit (hRH : RiemannHypothesis) (hZ2 : Z2) (hZ3 : Z3)
    {r : ℕ} (hr : 2 ≤ r) :
    Tendsto (fun η : ℝ => (η : ℂ) * PhiRc r ((r : ℂ) - 1 + η)) (𝓝[>] 0)
      (𝓝 ((((r.choose 2 : ℝ) * muZero - (r : ℝ) * Real.log (2 * Real.pi)) /
        ((r - 2).factorial : ℝ) : ℝ) : ℂ)) := by
  have hweight : (∑' ρ : NontrivialZeros, (zetaMult (ρ : ℂ) : ℝ) ^ 2 *
      ‖Gamma (ρ : ℂ)‖ ^ 2) = muZero := tsum_congr (zero_weight_eq hRH)
  have hsub := (phiR_sub_main_real_limit hRH hZ2 hZ3 hr).1
  rw [hweight] at hsub
  have hsum := hsub.add (tendsto_eta_phiRMain_real hr)
  have hvalue :
      (r.choose 2 : ℝ) / ((r - 2).factorial : ℝ) * muZero +
        (-(r : ℝ) * Real.log (2 * Real.pi) / ((r - 2).factorial : ℝ)) =
      ((r.choose 2 : ℝ) * muZero - (r : ℝ) * Real.log (2 * Real.pi)) /
        ((r - 2).factorial : ℝ) := by
    ring
  rw [← ofReal_add, hvalue] at hsum
  exact hsum.congr fun η => by rw [mul_sub, sub_add_cancel]

end GoldbachBoundaries.PhiRProof
