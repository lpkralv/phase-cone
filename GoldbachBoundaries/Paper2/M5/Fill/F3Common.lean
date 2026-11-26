import GoldbachBoundaries.Paper2.M5.FilterI

/-!
# Fill, group F3: shared helpers

Helpers for Step 3 of Theorem F(ii) and the value `Λ₀` of (iv): limits along the real ray `η ↓ 0`, continuity of
`Γ` and `K_s(w)`, and continuity, differentiability and polynomial growth of `evalH`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- `η → 0` in `ℂ` along `η ↓ 0`. -/
lemma F3_tendsto_ofReal : Tendsto (fun η : ℝ => (η : ℂ)) (𝓝[>] 0) (𝓝 0) := by
  have : Tendsto (fun η : ℝ => (η : ℂ)) (𝓝 0) (𝓝 ((0 : ℝ) : ℂ)) := Complex.continuous_ofReal.tendsto 0
  simpa using this.mono_left nhdsWithin_le_nhds

/-- `w + η → w` in the punctured neighbourhood along `η ↓ 0`. -/
lemma F3_tendsto_add_ofReal (w : ℂ) : Tendsto (fun η : ℝ => w + (η : ℂ)) (𝓝[>] 0) (𝓝[≠] w) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · simpa using (tendsto_const_nhds (x := w)).add F3_tendsto_ofReal
  · filter_upwards [self_mem_nhdsWithin] with η hη
    have hη' : (0 : ℝ) < η := hη
    simp only [mem_compl_iff, mem_singleton_iff, add_eq_left, ofReal_eq_zero]
    exact ne_of_gt hη'

/-- A function continuous at `s₀`, along the ray `s₀ + η`. -/
lemma F3_tendsto_comp_shift {g : ℂ → ℂ} {s₀ : ℂ} (hg : ContinuousAt g s₀) :
    Tendsto (fun η : ℝ => g (s₀ + η)) (𝓝[>] 0) (𝓝 (g s₀)) :=
  hg.tendsto.comp ((F3_tendsto_add_ofReal s₀).mono_right nhdsWithin_le_nhds)

/-- At a point of `Σ_Q`, `η Qcont(w + η) → R_w` (M1's `hasResidue_Qcont_Rcoef` along the ray). -/
lemma F3_tendsto_eta_Qcont_pole {w : ℂ} (hw : w ∈ PoleSetQ) :
    Tendsto (fun η : ℝ => (η : ℂ) * Qcont (w + η)) (𝓝[>] 0) (𝓝 (Rcoef w)) := by
  have h := (hasResidue_Qcont_Rcoef hw).comp (F3_tendsto_add_ofReal w)
  refine h.congr fun η => ?_
  simp [Function.comp]

/-- Off `Σ_Q` (and `Re w > 0`), `η Qcont(w + η) → 0`. -/
lemma F3_tendsto_eta_Qcont_reg {w : ℂ} (hw0 : 0 < w.re) (hw : w ∉ PoleSetQ) :
    Tendsto (fun η : ℝ => (η : ℂ) * Qcont (w + η)) (𝓝[>] 0) (𝓝 0) := by
  have hc : ContinuousAt Qcont w := (M2.isQCont_Qcont.2.2 w ⟨hw0, hw⟩).continuousAt
  simpa using F3_tendsto_ofReal.mul (F3_tendsto_comp_shift hc)

/-- `Γ` is differentiable on `Re u > 0`. -/
lemma F3_differentiableAt_Gamma {u : ℂ} (hu : 0 < u.re) : DifferentiableAt ℂ Gamma u := by
  refine Complex.differentiableAt_Gamma u fun m hm => ?_
  have := congrArg Complex.re hm
  simp only [neg_re, natCast_re] at this
  have : (0 : ℝ) ≤ m := m.cast_nonneg
  linarith

/-- `s ↦ K_s(w)` is differentiable at `s` when `Re s > 0` and `Re(s - w) > 0`. -/
lemma F3_differentiableAt_KerS {s w : ℂ} (hs : 0 < s.re) (hw : 0 < (s - w).re) :
    DifferentiableAt ℂ (fun t => KerS t w) s := by
  unfold KerS
  have h1 : DifferentiableAt ℂ (fun t : ℂ => Gamma (t - w)) s :=
    (F3_differentiableAt_Gamma hw).comp s (differentiableAt_id.sub_const w)
  exact ((differentiableAt_const _).mul h1).div (F3_differentiableAt_Gamma hs)
    (Complex.Gamma_ne_zero_of_re_pos hs)

/-- Continuity of `x ↦ H(a x, b x)`. -/
lemma F3_continuous_evalH {X : Type*} [TopologicalSpace X] (H : MvPolynomial (Fin 2) ℂ) {a b : X → ℂ}
    (ha : Continuous a) (hb : Continuous b) : Continuous (fun x => evalH H (a x) (b x)) := by
  induction H using MvPolynomial.induction_on with
  | C c => simpa [evalH] using continuous_const
  | add p q hp hq =>
    simp only [evalH, map_add]
    exact hp.add hq
  | mul_X p n hp =>
    have : (fun x => evalH (p * MvPolynomial.X n) (a x) (b x)) =
        fun x => evalH p (a x) (b x) * ![a x, b x] n := by
      funext x; simp [evalH]
    rw [this]
    refine hp.mul ?_
    fin_cases n
    · simpa using ha
    · simpa using hb

/-- Differentiability of `s ↦ H(a s, b s)`. -/
lemma F3_differentiable_evalH (H : MvPolynomial (Fin 2) ℂ) {a b : ℂ → ℂ} (ha : Differentiable ℂ a)
    (hb : Differentiable ℂ b) : Differentiable ℂ (fun s => evalH H (a s) (b s)) := by
  induction H using MvPolynomial.induction_on with
  | C c => simp [evalH]
  | add p q hp hq =>
    simp only [evalH, map_add]
    exact hp.add hq
  | mul_X p n hp =>
    have : (fun x => evalH (p * MvPolynomial.X n) (a x) (b x)) =
        fun x => evalH p (a x) (b x) * ![a x, b x] n := by
      funext x; simp [evalH]
    rw [this]
    refine hp.mul ?_
    fin_cases n
    · simpa using ha
    · simpa using hb

/-- Polynomial growth: `|H(z, w)| ≤ C (1 + |z| + |w|)^d`. -/
lemma F3_norm_evalH_le (H : MvPolynomial (Fin 2) ℂ) :
    ∃ C : ℝ, ∃ d : ℕ, 0 ≤ C ∧ ∀ z w : ℂ, ‖evalH H z w‖ ≤ C * (1 + ‖z‖ + ‖w‖) ^ d := by
  induction H using MvPolynomial.induction_on with
  | C c => exact ⟨‖c‖, 0, norm_nonneg _, fun z w => by simp [evalH]⟩
  | add p q hp hq =>
    obtain ⟨C₁, d₁, hC₁, h₁⟩ := hp
    obtain ⟨C₂, d₂, hC₂, h₂⟩ := hq
    refine ⟨C₁ + C₂, max d₁ d₂, by positivity, fun z w => ?_⟩
    have hR : 1 ≤ 1 + ‖z‖ + ‖w‖ := by linarith [norm_nonneg z, norm_nonneg w]
    have e1 : (1 + ‖z‖ + ‖w‖) ^ d₁ ≤ (1 + ‖z‖ + ‖w‖) ^ max d₁ d₂ := pow_le_pow_right₀ hR (le_max_left _ _)
    have e2 : (1 + ‖z‖ + ‖w‖) ^ d₂ ≤ (1 + ‖z‖ + ‖w‖) ^ max d₁ d₂ := pow_le_pow_right₀ hR (le_max_right _ _)
    have : evalH (p + q) z w = evalH p z w + evalH q z w := by simp [evalH]
    rw [this]
    calc ‖evalH p z w + evalH q z w‖ ≤ ‖evalH p z w‖ + ‖evalH q z w‖ := norm_add_le _ _
      _ ≤ C₁ * (1 + ‖z‖ + ‖w‖) ^ d₁ + C₂ * (1 + ‖z‖ + ‖w‖) ^ d₂ := add_le_add (h₁ z w) (h₂ z w)
      _ ≤ C₁ * (1 + ‖z‖ + ‖w‖) ^ max d₁ d₂ + C₂ * (1 + ‖z‖ + ‖w‖) ^ max d₁ d₂ :=
          add_le_add (mul_le_mul_of_nonneg_left e1 hC₁) (mul_le_mul_of_nonneg_left e2 hC₂)
      _ = (C₁ + C₂) * (1 + ‖z‖ + ‖w‖) ^ max d₁ d₂ := by ring
  | mul_X p n hp =>
    obtain ⟨C, d, hC, h⟩ := hp
    refine ⟨C, d + 1, hC, fun z w => ?_⟩
    have : evalH (p * MvPolynomial.X n) z w = evalH p z w * ![z, w] n := by simp [evalH]
    rw [this, norm_mul, pow_succ, ← mul_assoc]
    have hx : ‖![z, w] n‖ ≤ 1 + ‖z‖ + ‖w‖ := by
      fin_cases n
      · simp; linarith [norm_nonneg w]
      · simp; linarith [norm_nonneg z]
    exact mul_le_mul (h z w) hx (norm_nonneg _) (by positivity)

/-- Under RH a non-trivial zero has real part `1/2`. -/
lemma F3_re_zero (hRH : RiemannHypothesis) {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) : ρ.re = 1 / 2 :=
  sigmaFinite_re_eq_half hRH hρ

/-- Under RH, a point with real part `1/2`, not `1/2` and not a zero, is not in `Σ_Q`. -/
lemma F3_not_mem_poleSetQ (hRH : RiemannHypothesis) {w : ℂ} (hre : w.re = 1 / 2) (hw : w ≠ 1 / 2)
    (hz : w ∉ NontrivialZeros) : w ∉ PoleSetQ := by
  intro hS
  rcases poleSetQ_re_cases hRH hS with h | ⟨_, h | h⟩ | h
  · rw [h] at hre; norm_num at hre
  · exact hw h
  · exact hz h
  · linarith

/-- Under RH, `R_ρ = -m(ρ)` at a non-trivial zero. -/
lemma F3_Rcoef_zero (hRH : RiemannHypothesis) {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) :
    Rcoef ρ = -(zetaMult ρ : ℂ) := by
  have h := M4a.Rcoef_div_of_RH hRH (n := 1) (le_refl 1) squarefree_one hρ
  simpa [mu, ArithmeticFunction.moebius_apply_one] using h

end GoldbachBoundaries.Paper2.M5
