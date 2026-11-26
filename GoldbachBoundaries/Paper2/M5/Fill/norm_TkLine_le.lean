import GoldbachBoundaries.Paper2.M5.Fill.T2Common

/-!
# Fill: `norm_TkLine_le`

For `σ ∈ [σ₁, σ₂]`, `σ₁ > c + 1`: `Re(s - w) ≥ σ₁ - c > 1` on the line, so `|Qcont(s - w)| = |Q(s - w)|
≤ ∑_p log p · p^{-(σ₁ - c)}` (paper 1's `Qcont_eq_Q_of_one_lt`, M1's `norm_Q_le_re`, termwise monotonicity).
On the line `|F(c + iy)| ≤ C_F(1 + |y|)^{n₁}` (field 8 for large `|y|`, continuity on a compact interval otherwise).
M4a's `lem_kernelt_proof` (`x₁ = x₂ = c`) bounds the kernel by `C(1+|y|)^A(1+|t-y|)^A(1+|t|)^A e^{-π/2(...)}`; with
`A⁺ = max A 0` and `B = A⁺ + n₁` the integrand is `≤ K₀(1+|t|)^{A⁺} g_t(y)`, `g_t` the function of the second part of
`lem_kernelt_proof`, whose integral is `≤ C₂(1+|t|)^{2B+1}`. So `|TkLine F c s| ≤ (2π)⁻¹K₀C₂(1+|t|)^{A⁺+2B+1}`.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2

theorem norm_TkLine_le (hRH : RiemannHypothesis) (hZ6 : Z6) {m : ℕ} (hm : 1 ≤ m) {F H : ℂ → ℂ} (hP : TkPack m F H)
    {c : ℝ} (hc : (m : ℝ) - 1 / 2 < c) (hcm : c ≠ m) {σ₁ σ₂ : ℝ} (h1 : c + 1 < σ₁) :
    ∃ C : ℝ, ∃ N : ℕ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → ‖TkLine F c s‖ ≤ C * (1 + |s.im|) ^ N := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hc0 : 0 < c := by linarith
  by_cases hσ : σ₁ ≤ σ₂
  swap
  · exact ⟨0, 0, fun s h1' h2' => absurd (h1'.trans h2') hσ⟩
  obtain ⟨hK1, hK2⟩ := M4a.lem_kernelt_proof hRH hZ6
  obtain ⟨CK, A, hCK⟩ := hK1 c c σ₁ σ₂ hc0 le_rfl (by linarith) hσ
  -- `F` on the line
  obtain ⟨n₁, CF, hCF0, hF⟩ : ∃ n₁ : ℕ, ∃ CF : ℝ, 0 ≤ CF ∧
      ∀ y : ℝ, ‖F (c + y * I)‖ ≤ CF * (1 + |y|) ^ n₁ := by
    obtain ⟨N, C₀, y₀, hF8⟩ := hP.2.2.2.2.2.2.2 c c hc le_rfl
    set Y : ℝ := max y₀ 1 with hY
    have hcont : Continuous fun y : ℝ => F (c + y * I) := by
      rw [continuous_iff_continuousAt]
      intro y
      have hne : (c : ℂ) + y * I ≠ m := by
        intro h; have := congrArg Complex.re h; simp at this; exact hcm this
      exact ContinuousAt.comp (g := F) (f := fun y : ℝ => (c : ℂ) + y * I)
        ((hP.2.2.2.2.1 _ (by simpa using hc) hne).continuousAt) (by fun_prop)
    obtain ⟨B, hB⟩ := (isCompact_Icc (a := -Y) (b := Y)).exists_bound_of_continuousOn
      hcont.continuousOn
    refine ⟨⌈max N 0⌉₊, max C₀ 0 + max B 0, by positivity, fun y => ?_⟩
    have hu1 : 1 ≤ (1 + |y|) ^ ⌈max N 0⌉₊ := one_le_pow₀ (by linarith [abs_nonneg y])
    have hC0 : 0 ≤ max C₀ 0 := le_max_right _ _
    have hB0 : 0 ≤ max B 0 := le_max_right _ _
    by_cases hy : Y ≤ |y|
    · have hy0 : y₀ ≤ |y| := le_trans (le_max_left _ _) hy
      have hy1 : 1 ≤ |y| := le_trans (le_max_right _ _) hy
      have h := hF8 c ⟨le_rfl, le_rfl⟩ y hy0
      have hpow : |y| ^ N ≤ (1 + |y|) ^ ⌈max N 0⌉₊ := by
        calc |y| ^ N ≤ |y| ^ (max N 0) := Real.rpow_le_rpow_of_exponent_le hy1 (le_max_left _ _)
          _ ≤ |y| ^ ((⌈max N 0⌉₊ : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le hy1 (Nat.le_ceil _)
          _ = |y| ^ ⌈max N 0⌉₊ := Real.rpow_natCast _ _
          _ ≤ (1 + |y|) ^ ⌈max N 0⌉₊ := pow_le_pow_left₀ (abs_nonneg _) (by linarith) _
      have hpos : 0 ≤ |y| ^ N := Real.rpow_nonneg (abs_nonneg _) _
      calc ‖F (c + y * I)‖ ≤ C₀ * |y| ^ N := h
        _ ≤ max C₀ 0 * |y| ^ N := mul_le_mul_of_nonneg_right (le_max_left _ _) hpos
        _ ≤ max C₀ 0 * (1 + |y|) ^ ⌈max N 0⌉₊ := mul_le_mul_of_nonneg_left hpow hC0
        _ ≤ (max C₀ 0 + max B 0) * (1 + |y|) ^ ⌈max N 0⌉₊ :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    · have hyI : y ∈ Icc (-Y) Y := by
        rw [mem_Icc, ← abs_le]; exact (lt_of_not_ge hy).le
      have h : ‖F (c + y * I)‖ ≤ B := hB y hyI
      calc ‖F (c + y * I)‖ ≤ max B 0 := h.trans (le_max_left _ _)
        _ ≤ (max C₀ 0 + max B 0) * 1 := by linarith
        _ ≤ (max C₀ 0 + max B 0) * (1 + |y|) ^ ⌈max N 0⌉₊ :=
            mul_le_mul_of_nonneg_left hu1 (by positivity)
  -- `Qcont(s - w)` on the line
  set a : ℝ := σ₁ - c with ha_def
  have ha : 1 < a := by linarith
  set CQ : ℝ := ∑' p : Nat.Primes, ‖(Real.log (p : ℕ) : ℂ) * ((p : ℕ) : ℂ) ^ (-((a : ℝ) : ℂ))‖
    with hCQ_def
  have hCQ0 : 0 ≤ CQ := tsum_nonneg fun _ => norm_nonneg _
  have hQ : ∀ z : ℂ, a ≤ z.re → ‖Qcont z‖ ≤ CQ := by
    intro z hz
    have hz1 : 1 < z.re := by linarith
    rw [TIdentity.Qcont_eq_Q_of_one_lt hz1]
    refine (M1.norm_Q_le_re hz1).trans ?_
    refine Summable.tsum_le_tsum (fun p => ?_) (summable_norm_Q_terms (z := (z.re : ℂ)) (by simpa using hz1))
      (summable_norm_Q_terms (z := (a : ℂ)) (by simpa using ha))
    rw [norm_mul, norm_mul, norm_natCast_cpow_of_pos p.prop.pos, norm_natCast_cpow_of_pos p.prop.pos]
    simp only [neg_re, ofReal_re]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast p.prop.one_lt.le) (by linarith)
  -- exponents and constants
  set Ap : ℝ := max A 0 with hAp
  set B : ℝ := Ap + n₁ with hB
  have hAAp : A ≤ Ap := le_max_left _ _
  have hAp0 : 0 ≤ Ap := le_max_right _ _
  have hB0 : 0 ≤ B := by positivity
  have hApB : Ap ≤ B := by simp [hB]
  obtain ⟨C2, hC2⟩ := hK2 B hB0
  set CK' : ℝ := max CK 0 with hCK'
  have hCK'0 : 0 ≤ CK' := le_max_right _ _
  set K0 : ℝ := CK' * CF * CQ with hK0
  have hK00 : 0 ≤ K0 := by positivity
  set N : ℕ := ⌈Ap + (2 * B + 1)⌉₊ with hN
  refine ⟨1 / (2 * Real.pi) * K0 * max C2 0, N, ?_⟩
  intro s hs1 hs2
  set t : ℝ := s.im with ht
  set Z : ℝ := 1 + |t| with hZ
  have hZ1 : 1 ≤ Z := by linarith [abs_nonneg t]
  have hZ0 : 0 < Z := by linarith
  set g : ℝ → ℝ := fun y => (1 + |y|) ^ B * (1 + |t - y|) ^ B *
    Real.exp (-(Real.pi / 2 * (|y| + |t - y| - |t|))) with hg
  obtain ⟨hgi, hgint⟩ := hC2 t
  -- the pointwise bound
  have hpt : ∀ y : ℝ, ‖KerS s (c + y * I) * F (c + y * I) * Qcont (s - (c + y * I))‖ ≤
      K0 * Z ^ Ap * g y := by
    intro y
    set X : ℝ := 1 + |y| with hX
    set Y : ℝ := 1 + |t - y| with hY
    set E : ℝ := Real.exp (-(Real.pi / 2 * (|y| + |t - y| - |t|))) with hE
    have hX1 : 1 ≤ X := by linarith [abs_nonneg y]
    have hY1 : 1 ≤ Y := by linarith [abs_nonneg (t - y)]
    have hk := hCK c ⟨le_rfl, le_rfl⟩ y s.re ⟨hs1, hs2⟩ s.im
    rw [Complex.re_add_im] at hk
    have hk' : ‖KerS s (c + y * I)‖ ≤ CK' * X ^ A * Y ^ A * Z ^ A * E := by
      refine hk.trans ?_
      gcongr
      exact le_max_left _ _
    have hq := hQ (s - (c + y * I)) (by simp; linarith)
    have e1 : X ^ A * X ^ n₁ ≤ X ^ B := by
      rw [← Real.rpow_natCast, ← Real.rpow_add (by linarith), hB]
      exact Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
    have e2 : Y ^ A ≤ Y ^ B := Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)
    have e3 : Z ^ A ≤ Z ^ Ap := Real.rpow_le_rpow_of_exponent_le hZ1 hAAp
    rw [norm_mul, norm_mul]
    calc ‖KerS s (c + y * I)‖ * ‖F (c + y * I)‖ * ‖Qcont (s - (c + y * I))‖
        ≤ (CK' * X ^ A * Y ^ A * Z ^ A * E) * (CF * X ^ n₁) * CQ := by
          gcongr
          exact hF y
      _ = K0 * (X ^ A * X ^ n₁) * Y ^ A * Z ^ A * E := by rw [hK0]; ring
      _ ≤ K0 * X ^ B * Y ^ B * Z ^ Ap * E := by gcongr
      _ = K0 * Z ^ Ap * g y := by rw [hg]; ring
  have hI : ‖(1 / (2 * (Real.pi : ℂ) * I))‖ * ‖I‖ = 1 / (2 * Real.pi) := by
    simp [abs_of_pos Real.pi_pos]
  have hpow : Z ^ Ap * Z ^ (2 * B + 1) ≤ Z ^ N := by
    rw [← Real.rpow_add hZ0, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hZ1 (Nat.le_ceil _)
  have hgint' : ∫ y, g y ≤ max C2 0 * Z ^ (2 * B + 1) :=
    hgint.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  calc ‖TkLine F c s‖
      = ‖(1 / (2 * (Real.pi : ℂ) * I))‖ * ‖I‖ *
          ‖∫ y : ℝ, KerS s (c + y * I) * F (c + y * I) * Qcont (s - (c + y * I))‖ := by
        simp only [TkLine, VerticalIntegral', VerticalIntegral, norm_smul]; ring
    _ ≤ 1 / (2 * Real.pi) * ∫ y : ℝ, K0 * Z ^ Ap * g y := by
        rw [hI]
        refine mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans ?_) (by positivity)
        exact integral_mono_of_nonneg (ae_of_all _ fun y => norm_nonneg _) (hgi.const_mul _)
          (ae_of_all _ hpt)
    _ = 1 / (2 * Real.pi) * (K0 * Z ^ Ap * ∫ y : ℝ, g y) := by rw [integral_const_mul]
    _ ≤ 1 / (2 * Real.pi) * (K0 * Z ^ Ap * (max C2 0 * Z ^ (2 * B + 1))) := by
        gcongr
    _ = 1 / (2 * Real.pi) * K0 * max C2 0 * (Z ^ Ap * Z ^ (2 * B + 1)) := by ring
    _ ≤ 1 / (2 * Real.pi) * K0 * max C2 0 * Z ^ N := by
        gcongr

end GoldbachBoundaries.Paper2.M5
