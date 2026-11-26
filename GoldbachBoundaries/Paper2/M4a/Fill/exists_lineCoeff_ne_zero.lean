import GoldbachBoundaries.Paper2.M4a.Fill.ECommon

/-!
# M4a filler E: `exists_lineCoeff_ne_zero`

If every transverse coefficient vanished at every point of the line near `s₀`, each slice `z ↦ v(z, s)`
(`s ∈ ball s₀ δ`) would have infinite order at `c₀ + c₁s`, hence vanish on the disc `ball (c₀ + c₁s₀) r` (identity
theorem). Then `v = 0` on a product neighbourhood of `(c₀ + c₁s₀, s₀)`, hence on the whole (connected) ball.
-/

noncomputable section

open Complex Filter Topology Set Metric

namespace GoldbachBoundaries.Paper2.M4a

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **Some transverse coefficient of `v` is non-zero near `s₀`** (general). `v ≢ 0` on the (connected, convex) polydisc,
so `v` is not eventually `0` at `p = (c₀ + c₁s₀, s₀)` (`AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero`);
pick `q' = (z', s')` with `v q' ≠ 0`, `‖q' - p‖ < δ`, where `δ ≤ ε`, `δ ≤ r/2`, `‖c₁‖δ < r/2`. The `z`-slice of the
polydisc at `s'` is the disc `‖z - (c₀ + c₁s₀)‖ < r`, connected, containing `z'` and `c₀ + c₁s'`, and `z ↦ v(z, s')` is
analytic on it. If every `iteratedDeriv j` vanished at `c₀ + c₁s'`, the slice would vanish near that point (its Taylor
series, `AnalyticAt.hasFPowerSeriesAt` with `iteratedDeriv` coefficients) and hence on the disc (identity theorem), so
`v q' = 0`. Size: 100–200 lines. -/
theorem exists_lineCoeff_ne_zero {v : ℂ × ℂ → ℂ} {c₀ c₁ s₀ : ℂ} {r : ℝ}
    (hv : AnalyticOnNhd ℂ v (ball (c₀ + c₁ * s₀, s₀) r)) (hne : ∃ q ∈ ball (c₀ + c₁ * s₀, s₀) r, v q ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ s ∈ ball s₀ ε, (c₀ + c₁ * s, s) ∈ ball (c₀ + c₁ * s₀, s₀) r ∧ ∃ j, lineCoeff v c₀ c₁ j s ≠ 0 := by
  obtain ⟨q, hq, hvq⟩ := hne
  have hr : 0 < r := pos_of_mem_ball hq
  by_contra H
  simp only [not_exists, not_and, not_not] at H
  set δ := min ε r / (1 + ‖c₁‖) with hδ
  have hc1 : 0 < 1 + ‖c₁‖ := by positivity
  have hδpos : 0 < δ := div_pos (lt_min hε hr) hc1
  have hδε : δ ≤ min ε r := div_le_self (lt_min hε hr).le (by linarith [norm_nonneg c₁])
  have hc1δ : ‖c₁‖ * δ < r := by
    have : (1 + ‖c₁‖) * δ = min ε r := by rw [hδ]; field_simp
    have := min_le_right ε r
    nlinarith [norm_nonneg c₁]
  -- the slices vanish
  have hslice : ∀ s ∈ ball s₀ δ, ∀ z ∈ ball (c₀ + c₁ * s₀) r, v (z, s) = 0 := by
    intro s hs z hz
    have hsr : s ∈ ball s₀ r := ball_subset_ball (hδε.trans (min_le_right _ _)) hs
    have hmemP : ∀ w ∈ ball (c₀ + c₁ * s₀) r, (w, s) ∈ ball (c₀ + c₁ * s₀, s₀) r := by
      intro w hw
      rw [← ball_prod_same]; exact ⟨hw, hsr⟩
    have hline : c₀ + c₁ * s ∈ ball (c₀ + c₁ * s₀) r := by
      rw [mem_ball, dist_eq_norm] at hs ⊢
      have : c₀ + c₁ * s - (c₀ + c₁ * s₀) = c₁ * (s - s₀) := by ring
      rw [this, norm_mul]
      calc ‖c₁‖ * ‖s - s₀‖ ≤ ‖c₁‖ * δ := mul_le_mul_of_nonneg_left hs.le (norm_nonneg _)
        _ < r := hc1δ
    have hsε : s ∈ ball s₀ ε := ball_subset_ball (hδε.trans (min_le_left _ _)) hs
    have hzero := H s hsε (hmemP _ hline)
    have han : AnalyticOnNhd ℂ (fun w => v (w, s)) (ball (c₀ + c₁ * s₀) r) :=
      fun w hw => FillE.analyticAt_slice (hv _ (hmemP w hw))
    have htop : analyticOrderAt (fun w => v (w, s)) (c₀ + c₁ * s) = ⊤ := by
      rw [ENat.eq_top_iff_forall_ge]
      intro n
      exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (han _ hline)).mpr
        fun i _ => hzero i
    have hev : (fun w => v (w, s)) =ᶠ[𝓝 (c₀ + c₁ * s)] 0 := analyticOrderAt_eq_top.mp htop
    exact han.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball _ _).isPreconnected hline hev hz
  -- so `v` vanishes near the centre, hence on the ball
  have hev : v =ᶠ[𝓝 (c₀ + c₁ * s₀, s₀)] 0 := by
    have hmem : ball (c₀ + c₁ * s₀) r ×ˢ ball s₀ δ ∈ 𝓝 (c₀ + c₁ * s₀, s₀) :=
      prod_mem_nhds (ball_mem_nhds _ hr) (ball_mem_nhds _ hδpos)
    filter_upwards [hmem] with q hq
    exact hslice q.2 hq.2 q.1 hq.1
  exact hvq (hv.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball _ _).isPreconnected
    (mem_ball_self hr) hev hq)

end GoldbachBoundaries.Paper2.M4a
