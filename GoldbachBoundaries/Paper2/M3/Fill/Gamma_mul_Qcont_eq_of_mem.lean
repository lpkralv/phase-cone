import GoldbachBoundaries.Paper2.M3.Fill.FCommon

/-!
# Fill: `Gamma_mul_Qcont_eq_of_mem` (filler group F)

On `H = {Re z > max(0, x/2)}` the difference `f = Γ·Qcont - (1/(z-1) + m₁ + e₁)` is meromorphic (`m₁` holomorphic
there by `differentiableOn_m1_of_mem`), and vanishes on `Re z > max(1, ·)` (paper 1's `Gamma_mul_Q_eq_split`), so it
has order `⊤` everywhere on the convex `H`; at `z ∉ Σ_Q` it is analytic, hence `f z = 0`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M3

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **Step 3, the identity for `Q`** (unconditional). On the half-plane `H = {Re z > max(x/2, 0)}` (convex):
`TIdentity.m1` is holomorphic (`integrableOn_hErr_mul_cpow_of_mem` locally uniformly in `z`: the bound at
`Re z = x₀` dominates on `Re z ≥ x₀`; paper 1's `TIdentity.differentiableOn_integral_Ioc_cpow` may apply directly, or
`hasDerivAt_integral_of_dominated_loc_of_deriv_le`), `e1` is entire, `Γ` is analytic and `Qcont` meromorphic. For
`Re z > 1`, `Γ(z)Qcont(z) = 1/(z - 1) + m₁(z) + e₁(z)` (`TIdentity.Gamma_mul_Q_eq_split`,
`TIdentity.Qcont_eq_Q_of_one_lt`). The difference of the two sides is meromorphic on `H` with order `⊤` at a point
`z₀ = max(x/2, 1) + 1` (it vanishes on the open set `{Re z > max(x/2, 1)}`), hence at every point (`MeromorphicOn.meromorphicOrderAt_eq_top_of_isPreconnected`); at `z ∉ Σ_Q` with `z ≠ 1` both sides
are analytic (`M2.isQCont_Qcont`), so they are equal at `z` (continuity on a punctured neighbourhood). Size:
200–350 lines. -/
theorem Gamma_mul_Qcont_eq_of_mem {x : ℝ} (hx : x ∈ mellinConvSet) {z : ℂ} (hz0 : 0 < z.re)
    (hzx : x / 2 < z.re) (hzP : z ∉ PoleSetQ) :
    Gamma z * Qcont z = 1 / (z - 1) + TIdentity.m1 z + TIdentity.e1 z := by
  set c : ℝ := max 0 (x / 2) with hc
  set f : ℂ → ℂ := fun w => Gamma w * Qcont w - (1 / (w - 1) + TIdentity.m1 w + TIdentity.e1 w) with hf
  have hm1 := differentiableOn_m1_of_mem hx
  have hm1a : ∀ w : ℂ, x / 2 < w.re → AnalyticAt ℂ TIdentity.m1 w := fun w hw =>
    hm1.analyticAt ((isOpen_lt continuous_const continuous_re).mem_nhds hw)
  have he1a : ∀ w : ℂ, AnalyticAt ℂ TIdentity.e1 w := fun w =>
    TIdentity.differentiable_e1.analyticAt w
  have hmer : MeromorphicOn f (halfPlane c) := by
    intro w hw
    have hw' : c < w.re := hw
    have hw0 : 0 < w.re := lt_of_le_of_lt (le_max_left _ _) hw'
    have hwx : x / 2 < w.re := lt_of_le_of_lt (le_max_right _ _) hw'
    have h1 : MeromorphicAt (fun w : ℂ => 1 / (w - 1)) w :=
      MeromorphicAt.div (MeromorphicAt.const 1 w) (analyticAt_id.sub analyticAt_const).meromorphicAt
    exact ((analyticAt_Gamma_of_re_pos_F hw0).meromorphicAt.mul (meromorphicAt_Qcont hw0)).sub
      ((h1.add (hm1a w hwx).meromorphicAt).add (he1a w).meromorphicAt)
  -- `f = 0` on `Re w > max c 1`
  set z₀ : ℂ := ((max c 1 + 1 : ℝ) : ℂ) with hz₀
  have hz₀mem : z₀ ∈ halfPlane c := by
    show c < z₀.re
    rw [hz₀, ofReal_re]; linarith [le_max_left c 1]
  have hzmem : z ∈ halfPlane c := by
    show c < z.re
    exact max_lt hz0 hzx
  have hf0 : f =ᶠ[𝓝 z₀] 0 := by
    have hopen : IsOpen {w : ℂ | max c 1 < w.re} := isOpen_lt continuous_const continuous_re
    have hmem : z₀ ∈ {w : ℂ | max c 1 < w.re} := by
      show max c 1 < z₀.re
      rw [hz₀, ofReal_re]; linarith
    filter_upwards [hopen.mem_nhds hmem] with w hw
    have hw1 : 1 < w.re := lt_of_le_of_lt (le_max_right _ _) hw
    simp only [hf, Pi.zero_apply]
    rw [TIdentity.Qcont_eq_Q_of_one_lt hw1, TIdentity.Gamma_mul_Q_eq_split hw1, sub_self]
  have htop₀ : meromorphicOrderAt f z₀ = ⊤ :=
    meromorphicOrderAt_eq_top_iff.mpr (hf0.filter_mono nhdsWithin_le_nhds)
  have htop : meromorphicOrderAt f z = ⊤ :=
    hmer.meromorphicOrderAt_eq_top_of_isPreconnected (convex_halfSpace_re_gt c).isPreconnected
      hz₀mem hzmem htop₀
  -- `f` is analytic at `z`
  have hz1 : z ≠ 1 := fun h => hzP (by rw [h]; exact Or.inl (Or.inl rfl))
  have hQ : AnalyticAt ℂ Qcont z := M2.isQCont_Qcont.2.2 z ⟨hz0, hzP⟩
  have hfa : AnalyticAt ℂ f z := by
    have h1 : AnalyticAt ℂ (fun w : ℂ => 1 / (w - 1)) z :=
      analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hz1)
    exact ((analyticAt_Gamma_of_re_pos_F hz0).mul hQ).sub ((h1.add (hm1a z hzx)).add (he1a z))
  have hev : f =ᶠ[𝓝[≠] z] 0 := meromorphicOrderAt_eq_top_iff.mp htop
  have hev' : f =ᶠ[𝓝 z] 0 :=
    (hfa.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE continuousAt_const).mp hev
  have := hev'.eq_of_nhds
  simp only [hf, Pi.zero_apply] at this
  exact sub_eq_zero.mp this

end GoldbachBoundaries.Paper2.M3
