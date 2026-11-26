import GoldbachBoundaries.Paper2.M4a.Fill.analyticOnNhd_bracket

/-!
# M4a filler E: `not_eventually_zero_of_eqOn_bracket`

If `f = 0` on a punctured disc about `s₀`, then at `s₁ = s₀ + η ∈ D_L` (small real `η > 0`) the bracket equals `f = 0`
on an open neighbourhood; `𝔟` is analytic on the convex set `D_L`, so `𝔟 ≡ 0` there (identity theorem), against `hb`.
-/

noncomputable section

open Complex Filter Topology Set Metric

namespace GoldbachBoundaries.Paper2.M4a

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **An extension of a non-zero bracket is not `≡ 0` at the line** ((K1)). If `f = 0` on a punctured disc about `s₀`,
pick `s₁ ∈ ball s₀ (min ε r) ∩ D_L` (e.g. `s₀ + η` with small `η > 0`: `Re L(s₀ + η) = 1 + ℓη`); `s₁ ≠ s₀`, and on the
open set `(ball s₀ (min ε r) ∩ D_L) ∖ {s₀}`, a neighbourhood of `s₁`, `𝔟 = f = 0`. `𝔟` is analytic on `D_L`
(`analyticOnNhd_bracket`) and `D_L` is convex, hence preconnected, so `𝔟 = 0` on `D_L`
(`AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero`), contradicting `hb`. Size: 80–150 lines. -/
theorem not_eventually_zero_of_eqOn_bracket (A : Aff) (k : ℂ → ℂ → ℂ) (hK1 : K1 A k)
    (hb : ∃ s ∈ A.DL, bracket A k s ≠ 0) {s₀ : ℂ} (hs₀ : s₀ ∈ A.lineL) {r : ℝ} (hr : 0 < r) {f : ℂ → ℂ}
    (hf : EqOn f (bracket A k) (ball s₀ r ∩ A.DL)) : ¬ ∀ᶠ s in 𝓝[≠] s₀, f s = 0 := by
  intro hev
  obtain ⟨ε, hε, hεf⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hev)
  set δ := min ε r with hδ
  have hδpos : 0 < δ := lt_min hε hr
  have hl := A.ell_pos
  set η : ℝ := min (δ / 2) (1 / A.ell) with hη
  have hηpos : 0 < η := lt_min (half_pos hδpos) (one_div_pos.mpr hl)
  have hηδ : η < δ := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hδpos)
  have hηl : A.ell * η ≤ 1 := by
    have := min_le_right (δ / 2) (1 / A.ell)
    calc A.ell * η ≤ A.ell * (1 / A.ell) := mul_le_mul_of_nonneg_left this hl.le
      _ = 1 := by field_simp
  set s₁ : ℂ := s₀ + η
  have hline : A.ell * s₀.re + A.ell0 = 1 := by
    have : (A.app s₀).re = 1 := hs₀
    rwa [app_re] at this
  have hs₁DL : s₁ ∈ A.DL := by
    simp only [Aff.DL, mem_ofPred_eq, app_re, s₁, add_re, ofReal_re]
    constructor <;> nlinarith
  have hs₁ball : s₁ ∈ ball s₀ δ := by
    rw [mem_ball, dist_eq_norm]
    simp only [s₁, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hηpos]
    exact hηδ
  -- on an open neighbourhood of `s₁`, the bracket vanishes
  set W : Set ℂ := (ball s₀ δ ∩ A.DL) ∩ {s₀}ᶜ
  have hWo : IsOpen W := (isOpen_ball.inter (isOpen_DL A)).inter isOpen_compl_singleton
  have hs₁ne : s₁ ≠ s₀ := by
    intro h
    have : (η : ℂ) = 0 := by simpa [s₁] using h
    exact hηpos.ne' (by exact_mod_cast this)
  have hs₁W : s₁ ∈ W := ⟨⟨hs₁ball, hs₁DL⟩, hs₁ne⟩
  have hzero : bracket A k =ᶠ[𝓝 s₁] 0 := by
    filter_upwards [hWo.mem_nhds hs₁W] with s hs
    have hsδ : dist s s₀ < δ := hs.1.1
    rw [Pi.zero_apply, ← hf ⟨ball_subset_ball (min_le_right ε r) hs.1.1, hs.1.2⟩]
    exact hεf (lt_of_lt_of_le hsδ (min_le_left ε r)) hs.2
  have hall := (analyticOnNhd_bracket A k hK1).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (FillE.convex_DL A).isPreconnected hs₁DL hzero
  obtain ⟨s, hs, hbs⟩ := hb
  exact hbs (hall hs)

end GoldbachBoundaries.Paper2.M4a
