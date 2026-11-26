import GoldbachBoundaries.Paper2.M4b.Fill.BCommon

/-!
# Fill: `norm_integrand_le_far`

(K2) on `C = K`, `[x₁, x₂] = [c₁, c₂]` gives `|k| ≤ M₀ (1+|y|)^{-2}`. Paper 1's `norm_Qcont_le_log` with
`ε = min(c₁ - 1/2, min_K Re L - c₂ - 1/2) > 0` (compactness) bounds both `Q` factors: `|Q(z)| ≤ C log |y|` and
`|Q(L(s) - z)| ≤ C log |Im(L(s) - z)| ≤ C (log(1 + ℓT) + log(1 + |y|))`, `T = max_K |Im s|`, once
`|y| ≥ ℓT + 4`. With `u = 1 + |y|`, `v = u^{1/4} ≥ 1` and `log u ≤ 4v` (`Real.log_le_rpow_div`), the product is
`≤ M₀ v^{-8} · C·4v · C(a + 4)v = M v^{-6} = M u^{-3/2}`.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M4b

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **The integrand far out on a strip** (RH, (K2)). `K` compact in `D_L` and `[c₁, c₂]` with `c₁ > 1/2` and
`c₂ + 1/2 < Re L(s)` on `K`. (K2) on `C = K`, `[x₁, x₂] = [c₁, c₂]` (`c₂ < Re L(s)` on `K`): `|k(z,s)| ≤ M₀(1+|y|)^{-2}`.
Paper 1's `norm_Qcont_le_log` with `ε = c₁ - 1/2`: `|Q(z)| ≤ C log |y|` for `|y| ≥ 4`. For the second factor,
`Re(L(s) - z) ≥ ε' := min_K Re L - c₂ > 1/2` (compactness; `K = ∅` is trivial) and
`|Im(L(s) - z)| ≥ |y| - ℓT` with `T = max_K |Im s|`; take `Y = ℓT + 4`, so `|Q(L(s) - z)| ≤ C' log(|y| + ℓT)`.
Then `log |y| · log(|y| + ℓT) ≤ C''(1 + |y|)^{1/2}` (`Real.log_le_rpow_div` or `isLittleO_log_rpow_atTop`) gives
`M(1+|y|)^{-3/2}`. Size: 150–250 lines. -/
theorem norm_integrand_le_far (hRH : RiemannHypothesis) (A : Aff) (k : ℂ → ℂ → ℂ) (hK2 : K2 A k)
    {K : Set ℂ} (hK : IsCompact K) (hKD : K ⊆ A.DL) {c₁ c₂ : ℝ} (hc₁ : 1 / 2 < c₁) (hc₁₂ : c₁ ≤ c₂)
    (hc₂ : ∀ s ∈ K, c₂ + 1 / 2 < (A.app s).re) :
    ∃ M Y : ℝ, ∀ s ∈ K, ∀ z : ℂ, c₁ ≤ z.re → z.re ≤ c₂ → Y ≤ |z.im| →
      ‖k z s * Qcont z * Qcont (A.app s - z)‖ ≤ M / (1 + |z.im|) ^ (3 / 2 : ℝ) := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, 0, fun s hs => absurd hs (Set.notMem_empty s)⟩
  obtain ⟨M₀, hM₀⟩ := hK2 K hK hKD c₁ c₂ (by linarith) hc₁₂ (fun s hs => by linarith [hc₂ s hs])
  obtain ⟨s₀, hs₀K, hs₀min⟩ := hK.exists_isMinOn hne (continuous_app_re' A).continuousOn
  set ε : ℝ := min (c₁ - 1 / 2) ((A.app s₀).re - c₂ - 1 / 2) with hε
  have hεpos : 0 < ε := lt_min (by linarith) (by linarith [hc₂ s₀ hs₀K])
  obtain ⟨C, hC⟩ := TIdentity.norm_Qcont_le_log hRH hεpos
  obtain ⟨T, hT⟩ := hK.exists_bound_of_continuousOn Complex.continuous_im.continuousOn
  set T' : ℝ := max T 0 with hT'
  set C' : ℝ := max C 0 with hC'
  set M₀' : ℝ := max M₀ 0 with hM₀'
  have hT'0 : 0 ≤ T' := le_max_right _ _
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hM₀'0 : 0 ≤ M₀' := le_max_right _ _
  have hell := A.ell_pos
  have hellT : 0 ≤ A.ell * T' := mul_nonneg hell.le hT'0
  set a : ℝ := Real.log (1 + A.ell * T') with ha
  have ha0 : 0 ≤ a := Real.log_nonneg (by linarith)
  refine ⟨4 * M₀' * C' ^ 2 * (a + 4), A.ell * T' + 4, ?_⟩
  intro s hs z hz1 hz2 hY
  set y : ℝ := z.im with hy
  have hT's : |s.im| ≤ T' := le_trans (by simpa using hT s hs) (le_max_left _ _)
  have hy4 : 4 ≤ |y| := by linarith
  have hy0 : 0 < |y| := by linarith
  -- the kernel
  have hk : ‖k z s‖ ≤ M₀' / (1 + |y|) ^ 2 := by
    have := hM₀ z.re ⟨hz1, hz2⟩ s hs z.im
    rw [Complex.re_add_im] at this
    exact this.trans (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity))
  -- the first `Q`
  have hQ1 : ‖Qcont z‖ ≤ C' * Real.log (1 + |y|) := by
    have h := hC z (by linarith [min_le_left (c₁ - 1 / 2) ((A.app s₀).re - c₂ - 1 / 2)]) hy4
    refine h.trans ?_
    have hl1 : 0 ≤ Real.log |y| := Real.log_nonneg (by linarith)
    have hl2 : Real.log |y| ≤ Real.log (1 + |y|) := Real.log_le_log hy0 (by linarith)
    calc C * Real.log |y| ≤ C' * Real.log |y| := mul_le_mul_of_nonneg_right (le_max_left _ _) hl1
      _ ≤ C' * Real.log (1 + |y|) := mul_le_mul_of_nonneg_left hl2 hC'0
  -- the second `Q`
  have hmin : (A.app s₀).re ≤ (A.app s).re := hs₀min hs
  have hre2 : 1 / 2 + ε ≤ (A.app s - z).re := by
    have : ε ≤ (A.app s₀).re - c₂ - 1 / 2 := min_le_right _ _
    rw [Complex.sub_re]; linarith
  have him2 : (A.app s - z).im = A.ell * s.im - y := by simp [Aff.app, hy]
  have hsim : |A.ell * s.im| ≤ A.ell * T' := by
    rw [abs_mul, abs_of_pos hell]; exact mul_le_mul_of_nonneg_left hT's hell.le
  have him_lo : 4 ≤ |(A.app s - z).im| := by
    rw [him2]
    have := abs_sub_abs_le_abs_sub y (A.ell * s.im)
    rw [abs_sub_comm y] at this
    linarith
  have him_hi : |(A.app s - z).im| ≤ (1 + A.ell * T') * (1 + |y|) := by
    rw [him2]
    have := abs_sub (A.ell * s.im) y
    nlinarith
  have hQ2 : ‖Qcont (A.app s - z)‖ ≤ C' * (a + Real.log (1 + |y|)) := by
    refine (hC _ hre2 him_lo).trans ?_
    have hl1 : 0 ≤ Real.log |(A.app s - z).im| := Real.log_nonneg (by linarith)
    have hl2 : Real.log |(A.app s - z).im| ≤ a + Real.log (1 + |y|) := by
      rw [ha, ← Real.log_mul (by linarith) (by linarith)]
      exact Real.log_le_log (by linarith) him_hi
    calc C * Real.log |(A.app s - z).im| ≤ C' * Real.log |(A.app s - z).im| :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hl1
      _ ≤ C' * (a + Real.log (1 + |y|)) := mul_le_mul_of_nonneg_left hl2 hC'0
  -- powers of `u = 1 + |y|`
  set u : ℝ := 1 + |y| with hu
  have hu1 : 1 ≤ u := by linarith
  set v : ℝ := u ^ (1 / 4 : ℝ) with hv
  have hv1 : 1 ≤ v := Real.one_le_rpow hu1 (by norm_num)
  have hlogu : Real.log u ≤ 4 * v := by
    have := Real.log_le_rpow_div (x := u) (ε := 1 / 4) (by linarith) (by norm_num)
    rw [hv]; linarith
  have hu2 : u ^ 2 = v ^ 8 := by
    rw [hv, ← Real.rpow_natCast (u ^ (1 / 4 : ℝ)) 8, ← Real.rpow_mul (by linarith)]
    norm_num
  have hu32 : u ^ (3 / 2 : ℝ) = v ^ 6 := by
    rw [hv, ← Real.rpow_natCast (u ^ (1 / 4 : ℝ)) 6, ← Real.rpow_mul (by linarith)]
    norm_num
  have hv0 : 0 < v := by linarith
  rw [norm_mul, norm_mul]
  calc ‖k z s‖ * ‖Qcont z‖ * ‖Qcont (A.app s - z)‖
      ≤ (M₀' / u ^ 2) * (C' * (4 * v)) * (C' * ((a + 4) * v)) := by
        have h1 : ‖Qcont z‖ ≤ C' * (4 * v) := hQ1.trans (mul_le_mul_of_nonneg_left hlogu hC'0)
        have h2 : ‖Qcont (A.app s - z)‖ ≤ C' * ((a + 4) * v) := by
          refine hQ2.trans (mul_le_mul_of_nonneg_left ?_ hC'0)
          nlinarith
        exact mul_le_mul (mul_le_mul hk h1 (norm_nonneg _) (by positivity)) h2 (norm_nonneg _)
          (by positivity)
    _ = 4 * M₀' * C' ^ 2 * (a + 4) / u ^ (3 / 2 : ℝ) := by
        rw [hu2, hu32]
        field_simp

end GoldbachBoundaries.Paper2.M4b
