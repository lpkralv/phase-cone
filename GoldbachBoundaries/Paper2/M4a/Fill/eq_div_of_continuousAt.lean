import GoldbachBoundaries.Paper2.M4a.Fill.ECommon

/-!
# M4a filler E: `eq_div_of_continuousAt`

`V = (z - z₀)^m (a/m! + (z - z₀) G_V)` with `a = V^{(m)}(z₀) ≠ 0` (Taylor). `U = K V` off `z₀`, `K` bounded, forces
`m ≤ ord_{z₀} U` (an order `n < m` would give `U/(z - z₀)^n → 0`, against its non-zero limit), so
`U = (z - z₀)^m (b/m! + (z - z₀) G_U)` with `b = U^{(m)}(z₀)`. Off `z₀`, `K = U/V` is then a quotient of two functions
continuous at `z₀`, with limit `b/a`; continuity of `K` gives `K z₀ = b/a`.
-/

noncomputable section

open Complex Filter Topology Set Metric

namespace GoldbachBoundaries.Paper2.M4a

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **The value of a continuous quotient at a common zero** (one variable). `V` has order exactly `m` at `z₀`, so
`V = (z - z₀)^m V₁` with `V₁(z₀) = V^{(m)}(z₀)/m! ≠ 0` (`AnalyticAt.analyticOrderAt_eq_natCast` / the power series
`HasFPowerSeriesAt` with `iteratedDeriv` coefficients, `taylorSeries`), and `V ≠ 0` on a punctured neighbourhood. There
`U = K·V`; `K` is bounded near `z₀` (continuous), so `U = O(|z - z₀|^m)`, which forces `U^{(j)}(z₀) = 0` for `j < m`, and
`U(z)/(z - z₀)^m → U^{(m)}(z₀)/m!`. Also `U(z)/(z - z₀)^m = K(z)V₁(z) → K(z₀)V₁(z₀)`. Equate the limits (along
`𝓝[≠] z₀`, `tendsto_nhds_unique`). Size: 100–200 lines. -/
theorem eq_div_of_continuousAt {U V K : ℂ → ℂ} {z₀ : ℂ} {m : ℕ} (hU : AnalyticAt ℂ U z₀) (hV : AnalyticAt ℂ V z₀)
    (hVj : ∀ j < m, iteratedDeriv j V z₀ = 0) (hVm : iteratedDeriv m V z₀ ≠ 0) (hK : ContinuousAt K z₀)
    (hKUV : ∀ᶠ z in 𝓝[≠] z₀, V z ≠ 0 → K z = U z / V z) :
    K z₀ = iteratedDeriv m U z₀ / iteratedDeriv m V z₀ := by
  set a := iteratedDeriv m V z₀
  set b := iteratedDeriv m U z₀
  have hfac : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  obtain ⟨GV, hGV, hVeq⟩ := FillE.eq_pow_mul_of_iteratedDeriv hV hVj
  set φV : ℂ → ℂ := fun z => a / m.factorial + (z - z₀) * GV z
  have hφVc : ContinuousAt φV z₀ := by
    have := hGV.continuousAt; simp only [φV]; fun_prop
  have hφV0 : φV z₀ ≠ 0 := by simp [φV, hVm, hfac]
  have hφVne : ∀ᶠ z in 𝓝 z₀, φV z ≠ 0 := hφVc.eventually_ne hφV0
  -- off `z₀`, `V ≠ 0`
  have hVne : ∀ᶠ z in 𝓝[≠] z₀, V z ≠ 0 ∧ z ≠ z₀ := by
    filter_upwards [nhdsWithin_le_nhds hVeq, nhdsWithin_le_nhds hφVne, self_mem_nhdsWithin]
      with z hz hφ hz0
    refine ⟨?_, hz0⟩
    rw [hz]
    exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hz0)) hφ
  -- `U z = K z * V z` off `z₀`
  have hUKV : ∀ᶠ z in 𝓝[≠] z₀, U z = K z * ((z - z₀) ^ m * φV z) ∧ z ≠ z₀ := by
    filter_upwards [hVne, hKUV, nhdsWithin_le_nhds hVeq] with z hz hk hzV
    refine ⟨?_, hz.2⟩
    rw [hk hz.1, ← hzV, div_mul_cancel₀ _ hz.1]
  -- the order of `U` is at least `m`
  have hord : (m : ℕ∞) ≤ analyticOrderAt U z₀ := by
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨n, hn⟩ : ∃ n : ℕ, analyticOrderAt U z₀ = n :=
      ENat.ne_top_iff_exists.mp (ne_top_of_lt hlt) |>.imp fun _ h => h.symm
    have hnm : n < m := by rw [hn] at hlt; exact_mod_cast hlt
    obtain ⟨g, hg, hg0, hUg⟩ := (hU.analyticOrderAt_eq_natCast).mp hn
    -- `g = K (z - z₀)^{m-n} φV` off `z₀`
    have hgeq : ∀ᶠ z in 𝓝[≠] z₀, g z = K z * ((z - z₀) ^ (m - n) * φV z) := by
      filter_upwards [hUKV, nhdsWithin_le_nhds hUg] with z hz hzg
      have hzz : (z - z₀) ^ n ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hz.2)
      have : (z - z₀) ^ n * g z = (z - z₀) ^ n * (K z * ((z - z₀) ^ (m - n) * φV z)) := by
        rw [← smul_eq_mul, ← hzg, hz.1, ← Nat.sub_add_cancel hnm.le, pow_add]
        simp only [Nat.add_sub_cancel]
        ring
      exact mul_left_cancel₀ hzz this
    have hlim : Tendsto (fun z => K z * ((z - z₀) ^ (m - n) * φV z)) (𝓝[≠] z₀) (𝓝 0) := by
      have hc : ContinuousAt (fun z => K z * ((z - z₀) ^ (m - n) * φV z)) z₀ := by
        have := hK; fun_prop
      have h0 : K z₀ * ((z₀ - z₀) ^ (m - n) * φV z₀) = 0 := by
        rw [sub_self, zero_pow (Nat.sub_ne_zero_of_lt hnm)]; ring
      rw [← h0]
      exact hc.tendsto.mono_left nhdsWithin_le_nhds
    have hlim' : Tendsto g (𝓝[≠] z₀) (𝓝 (g z₀)) := hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    exact hg0 (tendsto_nhds_unique hlim' (hlim.congr' (hgeq.mono fun _ h => h.symm)))
  have hUj : ∀ j < m, iteratedDeriv j U z₀ = 0 :=
    (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hU).mp hord
  obtain ⟨GU, hGU, hUeq⟩ := FillE.eq_pow_mul_of_iteratedDeriv hU hUj
  set φU : ℂ → ℂ := fun z => b / m.factorial + (z - z₀) * GU z
  have hφUc : ContinuousAt φU z₀ := by
    have := hGU.continuousAt; simp only [φU]; fun_prop
  -- `K = φU/φV` off `z₀`
  have hKeq : ∀ᶠ z in 𝓝[≠] z₀, φU z / φV z = K z := by
    filter_upwards [hUKV, nhdsWithin_le_nhds hUeq, nhdsWithin_le_nhds hφVne] with z hz hzU hφ
    have hzz : (z - z₀) ^ m ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hz.2)
    rw [div_eq_iff hφ]
    have : (z - z₀) ^ m * φU z = (z - z₀) ^ m * (K z * φV z) := by
      rw [← hzU, hz.1]; ring
    exact mul_left_cancel₀ hzz this
  have hlimQ : Tendsto (fun z => φU z / φV z) (𝓝[≠] z₀) (𝓝 (φU z₀ / φV z₀)) :=
    (hφUc.div hφVc hφV0).tendsto.mono_left nhdsWithin_le_nhds
  have hlimK : Tendsto K (𝓝[≠] z₀) (𝓝 (K z₀)) := hK.tendsto.mono_left nhdsWithin_le_nhds
  rw [tendsto_nhds_unique hlimK (hlimQ.congr' hKeq)]
  simp only [φU, φV, sub_self, zero_mul, add_zero]
  field_simp

end GoldbachBoundaries.Paper2.M4a
