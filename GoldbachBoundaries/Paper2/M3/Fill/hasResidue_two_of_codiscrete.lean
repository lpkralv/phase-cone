import GoldbachBoundaries.Paper2.M3.Fill.tendsto_sub_two_mul_Gamma_T
import GoldbachBoundaries.Paper2.M3.Fill.order_residue_of_tendsto_ofReal

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
namespace GoldbachBoundaries.Paper2.M3
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **The residue at `2` is `1` for every continuation** (unconditional; the last sentence of `nr:lem:hsq`(ii)). `f` is
meromorphic at `2`, so analytic on `Δ(2, r') ∖ {2}` for some `r' ≤ r` (`MeromorphicAt.eventually_analyticAt`); `T` is
analytic on `σ > 2` (M1's `T_differentiableOn`). On the convex (so preconnected) open set
`V = Δ(2, r') ∩ {σ > 2}` both are analytic and `f = T` off a discrete subset of `V` (from the hypothesis, by
monotonicity of `codiscreteWithin`), so `f = T` on `V` (identity theorem: `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`,
the agreement set is not discrete in the non-empty open `V`). Then `(x-2)f(x) = (x-2)Γ(x)T(x)/Γ(x) → 1/Γ(2) = 1`
along real `x ↓ 2` (`tendsto_sub_two_mul_Gamma_T`, continuity of `1/Γ`, `Complex.Gamma_two`), and
`order_residue_of_tendsto_ofReal`. Size: 150–250 lines. -/
theorem hasResidue_two_of_codiscrete (f : ℂ → ℂ) (r : ℝ) (hr : 0 < r) (hf : MeromorphicOn f (ball 2 r))
    (hfT : f =ᶠ[codiscreteWithin (ball 2 r ∩ halfPlane 2)] T) :
    meromorphicOrderAt f 2 = -1 ∧ HasResidue f 2 1 := by
  have hf2 : MeromorphicAt f 2 := hf 2 (mem_ball_self hr)
  -- `f` is analytic on a punctured disc `Δ(2, ρ) ∖ {2}`
  obtain ⟨ρ, hρ, hρan⟩ : ∃ ρ > 0, ∀ z ∈ ball (2 : ℂ) ρ, z ≠ 2 → AnalyticAt ℂ f z := by
    have h := hf2.eventually_analyticAt
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff_ball] at h
    obtain ⟨ρ, hρ, h⟩ := h
    exact ⟨ρ, hρ, fun z hz hz2 => h z hz hz2⟩
  set δ : ℝ := min ρ r with hδ
  have hδpos : 0 < δ := lt_min hρ hr
  set V : Set ℂ := ball (2 : ℂ) δ ∩ halfPlane 2 with hV
  have hHo : IsOpen (halfPlane 2) := isOpen_lt continuous_const Complex.continuous_re
  have hVo : IsOpen V := isOpen_ball.inter hHo
  have hVsub : V ⊆ ball 2 r ∩ halfPlane 2 := fun z hz =>
    ⟨ball_subset_ball (min_le_right _ _) hz.1, hz.2⟩
  have hfV : AnalyticOnNhd ℂ f V := by
    intro z hz
    refine hρan z (ball_subset_ball (min_le_left _ _) hz.1) fun h => ?_
    have := hz.2
    rw [h] at this
    simp [halfPlane] at this
  have hTV : AnalyticOnNhd ℂ T V := fun z hz =>
    T_differentiableOn.analyticAt (hHo.mem_nhds hz.2)
  have hVc : IsPreconnected V := by
    refine (Convex.inter (convex_ball _ _) ?_).isPreconnected
    exact convex_halfSpace_gt (f := Complex.reLm) Complex.reLm.isLinear 2
  set z₀ : ℂ := ((2 + δ / 2 : ℝ) : ℂ) with hz₀
  have hz₀V : z₀ ∈ V := by
    refine ⟨?_, ?_⟩
    · rw [mem_ball, dist_eq, hz₀]
      have : ((2 + δ / 2 : ℝ) : ℂ) - 2 = ((δ / 2 : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      linarith
    · show 2 < z₀.re
      rw [hz₀, Complex.ofReal_re]; linarith
  have hfreq : ∃ᶠ z in 𝓝[≠] z₀, f z = T z :=
    (eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin hfT
      ((isOpen_ball.inter hHo).mem_nhds (hVsub hz₀V))).frequently
  have hEq : EqOn f T V := hfV.eqOn_of_preconnected_of_frequently_eq hTV hVc hz₀V hfreq
  -- `(x - 2) f(x) → 1` along real `x ↓ 2`
  have hlim : Tendsto (fun x : ℝ => ((x : ℂ) - ((2 : ℝ) : ℂ)) * f x) (𝓝[>] 2) (𝓝 1) := by
    have hG : Tendsto (fun x : ℝ => 1 / Gamma (x : ℂ)) (𝓝[>] 2) (𝓝 1) := by
      have hG2 : Gamma 2 = 1 := by
        have h := Complex.Gamma_add_one 1 one_ne_zero
        rw [Complex.Gamma_one, mul_one, one_add_one_eq_two] at h
        exact h
      have hc := (Complex.differentiable_one_div_Gamma.continuous.comp Complex.continuous_ofReal).tendsto 2
      have hc' : Tendsto (fun x : ℝ => (Gamma (x : ℂ))⁻¹) (𝓝 2) (𝓝 1) := by
        simpa [Function.comp_def, hG2] using hc
      simpa only [one_div] using hc'.mono_left nhdsWithin_le_nhds
    have hprod := tendsto_sub_two_mul_Gamma_T.mul hG
    rw [one_mul] at hprod
    refine hprod.congr' ?_
    have hmem : Ioo (2 : ℝ) (2 + δ) ∈ 𝓝[>] (2 : ℝ) := Ioo_mem_nhdsGT (by linarith)
    filter_upwards [hmem] with x hx
    have hxV : (x : ℂ) ∈ V := by
      refine ⟨?_, ?_⟩
      · rw [mem_ball, dist_eq]
        have : (x : ℂ) - 2 = ((x - 2 : ℝ) : ℂ) := by push_cast; ring
        rw [this, Complex.norm_real, Real.norm_of_nonneg (by linarith [hx.1])]
        linarith [hx.2]
      · show 2 < (x : ℂ).re
        rw [Complex.ofReal_re]; exact hx.1
    have hGx : Gamma (x : ℂ) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith [hx.1])
    rw [hEq hxV]
    push_cast
    field_simp
  have hf2' : MeromorphicAt f ((2 : ℝ) : ℂ) := by simpa using hf2
  have := order_residue_of_tendsto_ofReal hf2' one_ne_zero hlim
  simpa using this

end GoldbachBoundaries.Paper2.M3
