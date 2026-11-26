import GoldbachBoundaries.Paper2.M4a.Fill.analyticOnNhd_lineCoeff
import GoldbachBoundaries.Paper2.M4a.Fill.eq_div_of_continuousAt
import GoldbachBoundaries.Paper2.M4a.Fill.exists_lineCoeff_ne_zero

/-!
# M4a filler E: `isMeromorphic₂_restrict_line`

Local quotient `k = u/v` on `ball p r_p`, `p = (c₀ + c₁s₀, s₀)`; `r = r_p/(1 + ‖c₁‖)` keeps the line inside the
polydisc. `a_j`, `b_j` are the transverse coefficients of `v`, `u` along the line; `m` is the least `j` with
`a_j ≢ 0` on `ball s₀ r` (it exists by `exists_lineCoeff_ne_zero`), and `g = b_m/a_m`. Zeros of `a_m` are isolated, and
off them `eq_div_of_continuousAt` gives `k(c₀ + c₁y, y) = b_m(y)/a_m(y)` wherever `k(·, y)` is continuous on the line.
No coprimality of `u, v` is used.
-/

noncomputable section

open Complex Filter Topology Set Metric

namespace GoldbachBoundaries.Paper2.M4a

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **The restriction of an `IsMeromorphic₂` function to a complex line** (general). Take `u, v`, `r_p` from `hk` at
`p = (c₀ + c₁s₀, s₀)` and `r = r_p/(1 + ‖c₁‖)`, so `(c₀ + c₁s, s) ∈ ball p r_p` for `s ∈ ball s₀ r`. Put
`a_j = lineCoeff v c₀ c₁ j`, `b_j = lineCoeff u c₀ c₁ j`, analytic on `ball s₀ r` (`analyticOnNhd_lineCoeff`). By
`exists_lineCoeff_ne_zero` (with `ε = r`) some `a_j` is not `0` on `ball s₀ r`; let `m` be the least such (`Nat.find`),
so `a_j = 0` on the ball for `j < m`. `g = b_m/a_m` is meromorphic on the ball (`AnalyticOnNhd.meromorphicOn`, `div`).
`a_m ≢ 0` on the connected ball, so its zeros are isolated: for `x` in the ball, eventually in `𝓝[≠] x`, `a_m y ≠ 0`.
At such `y`, if `z ↦ k(z, y)` is continuous at `c₀ + c₁y`, `eq_div_of_continuousAt` (with `U = u(·, y)`, `V = v(·, y)`,
`K = k(·, y)`; `k = u/v` where `v ≠ 0` on the polydisc) gives `k(c₀ + c₁y, y) = b_m(y)/a_m(y)`. Size: 150–250 lines. -/
theorem isMeromorphic₂_restrict_line {k : ℂ → ℂ → ℂ} (hk : IsMeromorphic₂ k) (c₀ c₁ s₀ : ℂ) :
    ∃ r > 0, ∃ g : ℂ → ℂ, MeromorphicOn g (ball s₀ r) ∧
      ∀ x ∈ ball s₀ r, ∀ᶠ y in 𝓝[≠] x, ContinuousAt (fun z => k z y) (c₀ + c₁ * y) →
        k (c₀ + c₁ * y) y = g y := by
  classical
  obtain ⟨rp, hrp, u, v, hu, hv, hne, hkuv⟩ := hk (c₀ + c₁ * s₀, s₀)
  have hc1 : 0 < 1 + ‖c₁‖ := by positivity
  set r := rp / (1 + ‖c₁‖) with hrdef
  have hr : 0 < r := div_pos hrp hc1
  have hrrp : r ≤ rp := div_le_self hrp.le (by linarith [norm_nonneg c₁])
  have hc1r : ‖c₁‖ * r < rp := by
    have : (1 + ‖c₁‖) * r = rp := by rw [hrdef]; field_simp
    nlinarith
  have hline : ∀ s ∈ ball s₀ r, (c₀ + c₁ * s, s) ∈ ball (c₀ + c₁ * s₀, s₀) rp := by
    intro s hs
    rw [← ball_prod_same]
    refine ⟨?_, ball_subset_ball hrrp hs⟩
    rw [mem_ball, dist_eq_norm] at hs ⊢
    have : c₀ + c₁ * s - (c₀ + c₁ * s₀) = c₁ * (s - s₀) := by ring
    rw [this, norm_mul]
    calc ‖c₁‖ * ‖s - s₀‖ ≤ ‖c₁‖ * r := mul_le_mul_of_nonneg_left hs.le (norm_nonneg _)
      _ < rp := hc1r
  set a : ℕ → ℂ → ℂ := fun j => lineCoeff v c₀ c₁ j
  set b : ℕ → ℂ → ℂ := fun j => lineCoeff u c₀ c₁ j
  have ha : ∀ j, AnalyticOnNhd ℂ (a j) (ball s₀ r) := fun j =>
    (analyticOnNhd_lineCoeff hv c₀ c₁ j).mono fun s hs => hline s hs
  have hb : ∀ j, AnalyticOnNhd ℂ (b j) (ball s₀ r) := fun j =>
    (analyticOnNhd_lineCoeff hu c₀ c₁ j).mono fun s hs => hline s hs
  have hex : ∃ j, ∃ s ∈ ball s₀ r, a j s ≠ 0 := by
    obtain ⟨s, hs, -, j, hj⟩ := exists_lineCoeff_ne_zero hv hne hr
    exact ⟨j, s, hs, hj⟩
  set m := Nat.find hex
  obtain ⟨s₁, hs₁, ham⟩ := Nat.find_spec hex
  have hlt : ∀ j < m, ∀ s ∈ ball s₀ r, a j s = 0 := by
    intro j hj s hs
    by_contra h
    exact Nat.find_min hex hj ⟨s, hs, h⟩
  refine ⟨r, hr, b m / a m, fun x hx => ((hb m x hx).meromorphicAt).div ((ha m x hx).meromorphicAt), ?_⟩
  intro x hx
  -- the zeros of `a m` are isolated
  have hne' : ∀ᶠ y in 𝓝[≠] x, a m y ≠ 0 := by
    rcases (ha m x hx).eventually_eq_zero_or_eventually_ne_zero with h | h
    · exfalso
      exact ham ((ha m).eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball _ _).isPreconnected hx
        h hs₁)
    · exact h
  filter_upwards [hne', nhdsWithin_le_nhds (isOpen_ball.mem_nhds hx)] with y hy hyb hcont
  have hP := hline y hyb
  have hnear : {z : ℂ | (z, y) ∈ ball (c₀ + c₁ * s₀, s₀) rp} ∈ 𝓝 (c₀ + c₁ * y) := by
    have hc : Continuous fun z : ℂ => (z, y) := by fun_prop
    exact (isOpen_ball.preimage hc).mem_nhds hP
  have key := eq_div_of_continuousAt (U := fun z => u (z, y)) (V := fun z => v (z, y))
    (K := fun z => k z y) (z₀ := c₀ + c₁ * y) (m := m) (FillE.analyticAt_slice (hu _ hP))
    (FillE.analyticAt_slice (hv _ hP)) (fun j hj => hlt j hj y hyb) hy hcont
    (by
      filter_upwards [nhdsWithin_le_nhds hnear] with z hz hvz
      exact hkuv (z, y) hz hvz)
  exact key

end GoldbachBoundaries.Paper2.M4a
