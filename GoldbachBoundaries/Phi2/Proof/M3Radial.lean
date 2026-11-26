import GoldbachBoundaries.Phi2.Proof.M3Base
import GoldbachBoundaries.Phi2.Fill.norm_zeroSum_le
import GoldbachBoundaries.Phi2.Fill.integral_zeroSum_sq
import GoldbachBoundaries.Phi2.Fill.RrL_eq_cauchyT_add_Kc
import GoldbachBoundaries.Phi2.Fill.norm_Kc_le
import GoldbachBoundaries.Phi2.Fill.tendsto_eta_cauchyT

/-!
Route (Sol's §1, with the remainder of M2):
* `hL = -Z + R` with `Z = zeroSum`, `|Z(t)| ≤ S t^{-1/2}`, `|R(t)| ≤ C t^{-2/5}`, so
  `hL² - Z² = R² - 2ZR = O(t^{-9/10})` on `(0, 1]` and `Kc` is bounded on `Re s ≥ 1` (`norm_Kc_le`);
* `∫_0^1 Z(t)² t^{s-1} dt = ∑_{(ρ,ρ')} a_ρ a_ρ' / (s - ρ - ρ') = cauchyT s` for `Re s > 1` (Fubini against
  `∑ |a_ρ a_ρ'| < ∞`; `∫_0^1 t^{s-1-ρ-ρ'} = 1/(s - ρ - ρ')` since `Re(ρ + ρ') = 1` under RH);
* `|η/(η + i(τ - γ - γ'))| ≤ 1` and dominated convergence (`tendsto_tsum_of_dominated_convergence`) pick out the atom
  `μ{τ}` (`tendsto_eta_cauchyT`);
* `E₂`, `e₁`, `1/Γ` are continuous, so they contribute `0` after multiplying by `η`.

At `τ = 0` the limit for `H` is `μ{0}/Γ(1)`; the `-2 log(2π)` of Sol's `C(0)` sits in `phi2Main`'s pole at `s = 1`.
The boundary argument never uses `τ = 0`.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics

namespace GoldbachBoundaries.Phi2Proof

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-! ## Lemmas proved in `Fill/`

One file per lemma, same name and statement, proved at the end of its file and imported above: `norm_zeroSum_le`, `integral_zeroSum_sq`, `RrL_eq_cauchyT_add_Kc`, `norm_Kc_le`, `tendsto_eta_cauchyT`. -/



theorem tendsto_eta_Hphi2 (hRH : RiemannHypothesis) (hZ2 : Z2) (hZ3 : Z3) (τ : ℝ) :
    Tendsto (fun η : ℝ => (η : ℂ) * Hphi2 (1 + τ * I + η)) (𝓝[>] 0)
      (𝓝 (pairAtom τ / Gamma (1 + τ * I))) := by
  obtain ⟨hd1, hd2⟩ := differentiable_e1L_E2L
  obtain ⟨B, hB⟩ := norm_Kc_le hRH hZ2 hZ3
  set s0 : ℂ := 1 + τ * I with hs0
  have hη : Tendsto (fun η : ℝ => (η : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have := (Complex.continuous_ofReal.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using this
  have hs : Tendsto (fun η : ℝ => s0 + η) (𝓝[>] 0) (𝓝 s0) := by
    simpa using (tendsto_const_nhds (x := s0)).add hη
  have hA : Tendsto (fun η : ℝ => (η : ℂ) * (E2L (s0 + η) - 2 * e1L (s0 + η - 1))) (𝓝[>] 0) (𝓝 0) := by
    have hc : Tendsto (fun η : ℝ => E2L (s0 + η) - 2 * e1L (s0 + η - 1)) (𝓝[>] 0)
        (𝓝 (E2L s0 - 2 * e1L (s0 - 1))) :=
      ((hd2.continuous.tendsto s0).comp hs).sub
        (((hd1.continuous.tendsto (s0 - 1)).comp (hs.sub_const 1)).const_mul 2)
    simpa using hη.mul hc
  have hC : Tendsto (fun η : ℝ => (η : ℂ) * Kc (s0 + η)) (𝓝[>] 0) (𝓝 0) := by
    have hev : ∀ᶠ η : ℝ in 𝓝[>] 0, ‖(η : ℂ) * Kc (s0 + η)‖ ≤ ‖(η : ℂ)‖ * B := by
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with η hη1
      rw [norm_mul]
      refine mul_le_mul_of_nonneg_left (hB _ ?_ ?_) (norm_nonneg _)
      · simp [hs0]; linarith [hη1.1]
      · simp [hs0]; linarith [hη1.2]
    have hlim : Tendsto (fun η : ℝ => ‖(η : ℂ)‖ * B) (𝓝[>] 0) (𝓝 0) := by
      simpa using hη.norm.mul_const B
    exact squeeze_zero_norm' hev hlim
  have hBt := (tendsto_eta_cauchyT hRH hZ2 τ).2
  have hG : Tendsto (fun η : ℝ => (Gamma (s0 + η))⁻¹) (𝓝[>] 0) (𝓝 (Gamma s0)⁻¹) := by
    have := (differentiable_one_div_Gamma.continuous.tendsto s0).comp hs
    simpa [one_div, Function.comp_def] using this
  have hsum := ((hA.add hBt).add hC).mul hG
  rw [zero_add, add_zero, ← div_eq_mul_inv] at hsum
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with η hη0
  have hre : 1 < (s0 + η).re := by
    simp only [hs0, add_re, one_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, add_zero]
    linarith [mem_Ioi.mp hη0]
  rw [Hphi2, RrL_eq_cauchyT_add_Kc hRH hZ2 hZ3 hre]
  ring

end GoldbachBoundaries.Phi2Proof
