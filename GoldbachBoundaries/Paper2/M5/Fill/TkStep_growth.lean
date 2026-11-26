import GoldbachBoundaries.Paper2.M5.Fill.TkStep_eq_upper

/-!
# M5 filler T3: `TkStep_growth`

On `[x₁, x₂] ⊂ (m + 1/2, ∞)`, region (b)'s formula with the fixed line `c = cPlusK m x₁` (`TkStep_eq_upper`,
`FillT3.TkLine_eq_of_lines`): `‖TkLine F c s‖ ≤ C(1 + |t|)^N` (`norm_TkLine_le`), `‖r_m K_s(m)‖ = ‖Γ(s - m)/Γ(s)‖ ≤ 2^m`
(the recurrence, each factor `|s - j| ≥ σ - j > 1/2`), and `‖Qcont(s - m)‖ ≤ C₂ log |t|` for `|t| ≥ 4`
(`norm_Qcont_le_log`). Exponent `N + 1`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- `‖Γ(s - n)‖ ≤ 2ⁿ‖Γ(s)‖` for `σ > n + 1/2`. -/
lemma FillT3.norm_Gamma_sub_nat_le : ∀ (n : ℕ) (s : ℂ), (n : ℝ) + 1 / 2 < s.re →
    ‖Gamma (s - n)‖ ≤ 2 ^ n * ‖Gamma s‖ := by
  intro n
  induction n with
  | zero => intro s _; simp
  | succ n ih =>
    intro s hs
    push_cast at hs
    have h1 := ih s (by linarith)
    have hz : s - ((n + 1 : ℕ) : ℂ) ≠ 0 := by
      intro h
      have : (s - ((n + 1 : ℕ) : ℂ)).re = 0 := by rw [h]; simp
      simp at this; linarith
    have hrec : Gamma (s - n) = (s - ((n + 1 : ℕ) : ℂ)) * Gamma (s - ((n + 1 : ℕ) : ℂ)) := by
      have := Complex.Gamma_add_one (s - ((n + 1 : ℕ) : ℂ)) hz
      rw [← this]; congr 1; push_cast; ring
    have hnorm : 1 / 2 ≤ ‖s - ((n + 1 : ℕ) : ℂ)‖ := by
      have hre : (s - ((n + 1 : ℕ) : ℂ)).re = s.re - n - 1 := by simp; ring
      have := Complex.abs_re_le_norm (s - ((n + 1 : ℕ) : ℂ))
      rw [hre] at this
      have h3 : s.re - n - 1 ≤ |s.re - n - 1| := le_abs_self _
      linarith
    rw [hrec, norm_mul] at h1
    have h0 : 0 ≤ ‖Gamma (s - ((n + 1 : ℕ) : ℂ))‖ := norm_nonneg _
    have h4 : (1 / 2) * ‖Gamma (s - ((n + 1 : ℕ) : ℂ))‖ ≤ 2 ^ n * ‖Gamma s‖ :=
      (mul_le_mul_of_nonneg_right hnorm h0).trans h1
    rw [pow_succ]
    linarith

/-- `‖r_m K_s(m)‖ ≤ 2^m` for `σ > m + 1/2`. -/
lemma FillT3.norm_rK_KerS_le {m : ℕ} (hm : 1 ≤ m) {s : ℂ} (hs : (m : ℝ) + 1 / 2 < s.re) :
    ‖rK m * KerS s m‖ ≤ 2 ^ m := by
  have hpos : 0 < s.re := by have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith
  have hG : 0 < ‖Gamma s‖ := norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos hpos)
  rw [FillT3.rK_mul_KerS hm, norm_div, div_le_iff₀ hG]
  exact FillT3.norm_Gamma_sub_nat_le m s hs

theorem TkStep_growth (hRH : RiemannHypothesis) (hZ6 : Z6) {m : ℕ} (hm : 1 ≤ m) {F H : ℂ → ℂ}
    (hP : TkPack m F H) :
    ∀ x₁ x₂ : ℝ, ((m + 1 : ℕ) : ℝ) - 1 / 2 < x₁ → x₁ ≤ x₂ → ∃ N C y₀ : ℝ, ∀ x ∈ Icc x₁ x₂, ∀ y : ℝ,
      y₀ ≤ |y| → ‖TkStep m F (x + y * I)‖ ≤ C * |y| ^ N := by
  intro x₁ x₂ hx₁ _
  have hx₁' : (m : ℝ) + 1 / 2 < x₁ := by push_cast at hx₁; linarith
  set c : ℝ := cPlusK m (x₁ : ℂ) with hc
  obtain ⟨hc1, hc2, hc3⟩ := FillT3.cPlusK_bounds m (s := (x₁ : ℂ)) (by simpa using hx₁')
  simp only [ofReal_re] at hc3
  obtain ⟨C, N, hC⟩ := norm_TkLine_le hRH hZ6 hm hP (c := c) hc1 (ne_of_lt hc2) (σ₁ := x₁) (σ₂ := x₂)
    (by linarith)
  obtain ⟨C₂, hC₂⟩ := TIdentity.norm_Qcont_le_log hRH (ε := x₁ - m - 1 / 2) (by linarith)
  refine ⟨(N : ℝ) + 1, |C| * 2 ^ N + 2 ^ m * |C₂|, 4, fun x hx y hy => ?_⟩
  set s : ℂ := (x : ℂ) + y * I with hs
  have hsre : s.re = x := by simp [hs]
  have hsim : s.im = y := by simp [hs]
  have hsx : (m : ℝ) + 1 / 2 < s.re := by rw [hsre]; linarith [hx.1]
  rw [TkStep_eq_upper hRH hm hP s hsx]
  obtain ⟨ha1, ha2, ha3⟩ := FillT3.cPlusK_bounds m hsx
  rw [FillT3.TkLine_eq_of_lines hRH hm hP ha1 hc1 (by linarith) (by rw [hsre]; linarith [hx.1]) ha2 hc2
    (Or.inl ⟨ha3, by rw [hsre]; linarith [hx.1]⟩)]
  have hy1 : 1 ≤ |y| := by linarith
  have hy0 : 0 < |y| := by linarith
  have hpow : |y| ^ ((N : ℝ) + 1) = |y| ^ N * |y| := by
    rw [Real.rpow_add_one (ne_of_gt hy0), Real.rpow_natCast]
  have hyN : 1 ≤ |y| ^ N := one_le_pow₀ hy1
  -- the line integral
  have hT : ‖TkLine F c s‖ ≤ |C| * 2 ^ N * (|y| ^ N * |y|) := by
    have h := hC s (by rw [hsre]; exact hx.1) (by rw [hsre]; exact hx.2)
    rw [hsim] at h
    have h1 : (1 + |y|) ^ N ≤ (2 * |y|) ^ N := pow_le_pow_left₀ (by positivity) (by linarith) N
    have h2 : (0 : ℝ) ≤ (1 + |y|) ^ N := by positivity
    calc ‖TkLine F c s‖ ≤ C * (1 + |y|) ^ N := h
      _ ≤ |C| * (1 + |y|) ^ N := mul_le_mul_of_nonneg_right (le_abs_self _) h2
      _ ≤ |C| * (2 * |y|) ^ N := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = |C| * 2 ^ N * (|y| ^ N * 1) := by rw [mul_pow]; ring
      _ ≤ |C| * 2 ^ N * (|y| ^ N * |y|) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left hy1 (by positivity)
  -- the pole term
  have hK := FillT3.norm_rK_KerS_le hm hsx
  have hQ : ‖Qcont (s - m)‖ ≤ |C₂| * |y| := by
    have hre : 1 / 2 + (x₁ - m - 1 / 2) ≤ (s - m).re := by
      simp only [sub_re, natCast_re]; rw [hsre]; linarith [hx.1]
    have him : (s - m).im = y := by simp [hsim]
    have h := hC₂ (s - m) hre (by rw [him]; exact hy)
    rw [him] at h
    have hlog0 : 0 ≤ Real.log |y| := Real.log_nonneg hy1
    have hlog : Real.log |y| ≤ |y| := (Real.log_le_sub_one_of_pos hy0).trans (by linarith)
    calc ‖Qcont (s - m)‖ ≤ C₂ * Real.log |y| := h
      _ ≤ |C₂| * Real.log |y| := mul_le_mul_of_nonneg_right (le_abs_self _) hlog0
      _ ≤ |C₂| * |y| := mul_le_mul_of_nonneg_left hlog (abs_nonneg _)
  have hR : ‖rK m * KerS s m * Qcont (s - m)‖ ≤ 2 ^ m * |C₂| * (|y| ^ N * |y|) := by
    rw [norm_mul]
    calc ‖rK m * KerS s m‖ * ‖Qcont (s - m)‖ ≤ 2 ^ m * (|C₂| * |y|) :=
          mul_le_mul hK hQ (norm_nonneg _) (by positivity)
      _ = 2 ^ m * |C₂| * (1 * |y|) := by ring
      _ ≤ 2 ^ m * |C₂| * (|y| ^ N * |y|) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_right hyN hy0.le
  rw [hpow]
  calc ‖TkLine F c s + rK m * KerS s m * Qcont (s - m)‖
      ≤ ‖TkLine F c s‖ + ‖rK m * KerS s m * Qcont (s - m)‖ := norm_add_le _ _
    _ ≤ |C| * 2 ^ N * (|y| ^ N * |y|) + 2 ^ m * |C₂| * (|y| ^ N * |y|) := add_le_add hT hR
    _ = (|C| * 2 ^ N + 2 ^ m * |C₂|) * (|y| ^ N * |y|) := by ring

end GoldbachBoundaries.Paper2.M5
