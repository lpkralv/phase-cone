import GoldbachBoundaries.Paper2.M5.FilterI

/-!
# Fill, group F2: shared helpers

* `norm_evalH_le`: a polynomial `H ∈ ℂ[z, w]` grows at most polynomially, `|H(z, w)| ≤ C(1 + |z| + |w|)^d`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- Polynomial growth of `evalH`. -/
lemma norm_evalH_le (H : MvPolynomial (Fin 2) ℂ) :
    ∃ C : ℝ, ∃ d : ℕ, 0 ≤ C ∧ ∀ z w : ℂ, ‖evalH H z w‖ ≤ C * (1 + ‖z‖ + ‖w‖) ^ d := by
  induction H using MvPolynomial.induction_on with
  | C a =>
    refine ⟨‖a‖, 0, norm_nonneg _, fun z w => ?_⟩
    simp [evalH]
  | add p q hp hq =>
    obtain ⟨C₁, d₁, hC₁, h₁⟩ := hp
    obtain ⟨C₂, d₂, hC₂, h₂⟩ := hq
    refine ⟨C₁ + C₂, max d₁ d₂, add_nonneg hC₁ hC₂, fun z w => ?_⟩
    have hR : 1 ≤ 1 + ‖z‖ + ‖w‖ := by
      have := norm_nonneg z; have := norm_nonneg w; linarith
    have e1 : (1 + ‖z‖ + ‖w‖) ^ d₁ ≤ (1 + ‖z‖ + ‖w‖) ^ max d₁ d₂ :=
      pow_le_pow_right₀ hR (le_max_left _ _)
    have e2 : (1 + ‖z‖ + ‖w‖) ^ d₂ ≤ (1 + ‖z‖ + ‖w‖) ^ max d₁ d₂ :=
      pow_le_pow_right₀ hR (le_max_right _ _)
    have : evalH (p + q) z w = evalH p z w + evalH q z w := by simp [evalH]
    rw [this]
    calc ‖evalH p z w + evalH q z w‖ ≤ ‖evalH p z w‖ + ‖evalH q z w‖ := norm_add_le _ _
      _ ≤ C₁ * (1 + ‖z‖ + ‖w‖) ^ d₁ + C₂ * (1 + ‖z‖ + ‖w‖) ^ d₂ := add_le_add (h₁ z w) (h₂ z w)
      _ ≤ C₁ * (1 + ‖z‖ + ‖w‖) ^ max d₁ d₂ + C₂ * (1 + ‖z‖ + ‖w‖) ^ max d₁ d₂ := by
          gcongr
      _ = _ := by ring
  | mul_X p n hp =>
    obtain ⟨C₁, d₁, hC₁, h₁⟩ := hp
    refine ⟨C₁, d₁ + 1, hC₁, fun z w => ?_⟩
    have hR : ‖(![z, w] : Fin 2 → ℂ) n‖ ≤ 1 + ‖z‖ + ‖w‖ := by
      fin_cases n
      · simp; have := norm_nonneg w; linarith
      · simp; have := norm_nonneg z; linarith
    have : evalH (p * MvPolynomial.X n) z w = evalH p z w * (![z, w] : Fin 2 → ℂ) n := by
      simp [evalH]
    rw [this, norm_mul, pow_succ, ← mul_assoc]
    exact mul_le_mul (h₁ z w) hR (norm_nonneg _) (by positivity)

/-- `z ↦ H(f z, g z)` is differentiable when `f`, `g` are. -/
lemma differentiable_evalH (H : MvPolynomial (Fin 2) ℂ) {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) : Differentiable ℂ (fun z => evalH H (f z) (g z)) := by
  induction H using MvPolynomial.induction_on with
  | C a => simp [evalH]
  | add p q hp hq =>
    have : (fun z => evalH (p + q) (f z) (g z)) = fun z => evalH p (f z) (g z) + evalH q (f z) (g z) := by
      funext z; simp [evalH]
    rw [this]; exact hp.add hq
  | mul_X p n hp =>
    have : (fun z => evalH (p * MvPolynomial.X n) (f z) (g z)) =
        fun z => evalH p (f z) (g z) * (![f z, g z] : Fin 2 → ℂ) n := by
      funext z; simp [evalH]
    rw [this]
    fin_cases n
    · exact fun z => by simpa using (hp z).fun_mul (hf z)
    · exact fun z => by simpa using (hp z).fun_mul (hg z)

/-- **Decay of `k_H`** on a vertical strip, uniformly for `s` in a rectangle: `|k_H(z, s)| (1 + |Im z|)^m ≤ K`. -/
lemma norm_kH_mul_pow_le (H : MvPolynomial (Fin 2) ℂ) {x₁ x₂ σ₁ σ₂ τ : ℝ} (hx₁ : 0 < x₁) (hx : x₂ < σ₁)
    (m : ℕ) :
    ∃ K : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → |s.im| ≤ τ → ∀ z : ℂ, x₁ ≤ z.re → z.re ≤ x₂ →
      ‖kH H z s‖ * (1 + |z.im|) ^ m ≤ K := by
  obtain ⟨C, d, hC, hCb⟩ := norm_evalH_le H
  obtain ⟨C₃, hC₃⟩ := norm_KerS_mul_pow_le (x₁ := x₁) (x₂ := x₂) (σ₁ := σ₁) (σ₂ := σ₂) (τ₀ := τ) hx₁ hx (m + d)
  set A : ℝ := 1 + 2 * (|x₁| + |x₂|) + |σ₁| + |σ₂| + 2 * |τ| + 2 with hA
  have hA1 : 1 ≤ A := by
    have := abs_nonneg x₁; have := abs_nonneg x₂; have := abs_nonneg σ₁; have := abs_nonneg σ₂
    have := abs_nonneg τ; linarith
  refine ⟨C₃ * (C * A ^ d), fun s hs1 hs2 hsi z hz1 hz2 => ?_⟩
  have hzre : |z.re| ≤ |x₁| + |x₂| := by
    rw [abs_le]; constructor
    · have := neg_abs_le x₁; have := abs_nonneg x₂; linarith
    · have := le_abs_self x₂; have := abs_nonneg x₁; linarith
  have hsre : |s.re| ≤ |σ₁| + |σ₂| := by
    rw [abs_le]; constructor
    · have := neg_abs_le σ₁; have := abs_nonneg σ₂; linarith
    · have := le_abs_self σ₂; have := abs_nonneg σ₁; linarith
  have hnz : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
  have hns : ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
  have hnsz : ‖s - z‖ ≤ ‖s‖ + ‖z‖ := norm_sub_le _ _
  have hy0 : 0 ≤ |z.im| := abs_nonneg _
  have hR : 1 + ‖z‖ + ‖s - z‖ ≤ A * (1 + |z.im|) := by
    have h2 : 2 * |z.im| ≤ A * |z.im| := by
      have : (2 : ℝ) ≤ A := by
        have := abs_nonneg x₁; have := abs_nonneg x₂; have := abs_nonneg σ₁; have := abs_nonneg σ₂
        have := abs_nonneg τ; linarith
      exact mul_le_mul_of_nonneg_right this hy0
    have ht : |s.im| ≤ |τ| := hsi.trans (le_abs_self τ)
    have : A * (1 + |z.im|) = A + A * |z.im| := by ring
    rw [this]
    have := abs_nonneg τ
    linarith
  have hE : ‖evalH H z (s - z)‖ ≤ C * A ^ d * (1 + |z.im|) ^ d := by
    calc ‖evalH H z (s - z)‖ ≤ C * (1 + ‖z‖ + ‖s - z‖) ^ d := hCb z (s - z)
      _ ≤ C * (A * (1 + |z.im|)) ^ d := by
          gcongr
      _ = _ := by rw [mul_pow]; ring
  have hK := hC₃ s hs1 hs2 hsi z hz1 hz2
  have hpos : 0 < 1 + |z.im| := by linarith
  have hK0 : 0 ≤ ‖KerS s z‖ := norm_nonneg _
  calc ‖kH H z s‖ * (1 + |z.im|) ^ m = ‖KerS s z‖ * ‖evalH H z (s - z)‖ * (1 + |z.im|) ^ m := by
        rw [kH, norm_mul]
    _ ≤ ‖KerS s z‖ * (C * A ^ d * (1 + |z.im|) ^ d) * (1 + |z.im|) ^ m := by gcongr
    _ = (‖KerS s z‖ * (1 + |z.im|) ^ (m + d)) * (C * A ^ d) := by rw [pow_add]; ring
    _ ≤ C₃ * (C * A ^ d) := by gcongr

end GoldbachBoundaries.Paper2.M5
