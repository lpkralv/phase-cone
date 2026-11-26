import GoldbachBoundaries.Paper2.M3.Landau

/-!
# Fill: `exists_differentiableOn_balls` (filler group F)

Removable singularities on discs centred at real points. `Mt = toMeromorphicNFOn F W` is in normal form on `W`
with the orders of `F`; on each disc `F` is analytic off the centre, so every point of the union has order `≥ 0`
and `Mt` is analytic there.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M3

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **Removable singularities on discs centred at real points** (general complex analysis). For each `x ∈ (a, b]`,
`F` is meromorphic at `x` (`x ∈ W`), so analytic on a punctured disc about `x` (`MeromorphicAt.eventually_analyticAt`);
take `r x > 0` with `Δ(x, r x) ⊆ W` and `F` analytic on `Δ(x, r x) ∖ {x}`. Put `Mt = toMeromorphicNFOn F W`
(`Mathlib/Analysis/Meromorphic/NormalForm.lean`): it is in normal form on `W`, equals `F` at every point where `F` is
analytic (normal form at such points), and has the same orders as `F`. On `Δ(x, r x)`: at `x`,
`meromorphicOrderAt Mt x = meromorphicOrderAt F x ≥ 0`, so `Mt` is analytic at `x` (normal form with non-negative
order); at other points `F` is analytic, so `Mt` is. Hence `Mt` is differentiable on the union. Size: 150–250 lines. -/
theorem exists_differentiableOn_balls {a b : ℝ} {F : ℂ → ℂ} {W : Set ℂ} (hW : IsOpen W)
    (hF : MeromorphicOn F W)
    (hI : ∀ x ∈ Ioc a b, (x : ℂ) ∈ W) (hord : ∀ x ∈ Ioc a b, 0 ≤ meromorphicOrderAt F x) :
    ∃ r : ℝ → ℝ, (∀ x ∈ Ioc a b, 0 < r x) ∧ ballsU a b r ⊆ W ∧
      ∃ Mt : ℂ → ℂ, DifferentiableOn ℂ Mt (ballsU a b r) ∧
        ∀ s ∈ ballsU a b r, AnalyticAt ℂ F s → Mt s = F s := by
  -- radii: a disc inside `W` on which `F` is analytic off the centre
  have hex : ∀ x : ℝ, ∃ ρ : ℝ, x ∈ Ioc a b →
      0 < ρ ∧ ball (x : ℂ) ρ ⊆ W ∧ ∀ z ∈ ball (x : ℂ) ρ, z ≠ x → AnalyticAt ℂ F z := by
    intro x
    by_cases hx : x ∈ Ioc a b
    · have hxW := hI x hx
      have h1 : ∀ᶠ z in 𝓝[≠] (x : ℂ), AnalyticAt ℂ F z := (hF _ hxW).eventually_analyticAt
      have h2 : ∀ᶠ z in 𝓝[≠] (x : ℂ), z ∈ W :=
        nhdsWithin_le_nhds (hW.mem_nhds hxW)
      have h3 := h1.and h2
      rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff_ball] at h3
      obtain ⟨ρ, hρ, hρ'⟩ := h3
      refine ⟨ρ, fun _ => ⟨hρ, fun z hz => ?_, fun z hz hzx => (hρ' z hz hzx).1⟩⟩
      by_cases hzx : z = x
      · rw [hzx]; exact hxW
      · exact (hρ' z hz hzx).2
    · exact ⟨1, fun h => absurd h hx⟩
  choose r hr using hex
  have hsub : ballsU a b r ⊆ W := by
    intro z hz
    simp only [ballsU, mem_iUnion] at hz
    obtain ⟨x, hx, hz⟩ := hz
    exact (hr x hx).2.1 hz
  -- every point of the union has order `≥ 0` and `F` is meromorphic there
  have hord' : ∀ s ∈ ballsU a b r, 0 ≤ meromorphicOrderAt F s := by
    intro s hs
    simp only [ballsU, mem_iUnion] at hs
    obtain ⟨x, hx, hs⟩ := hs
    by_cases hsx : s = x
    · rw [hsx]; exact hord x hx
    · exact ((hr x hx).2.2 s hs hsx).meromorphicOrderAt_nonneg
  refine ⟨r, fun x hx => (hr x hx).1, hsub, toMeromorphicNFOn F W, ?_, ?_⟩
  · intro s hs
    have hsW := hsub hs
    have hNF : MeromorphicNFAt (toMeromorphicNFOn F W) s := meromorphicNFOn_toMeromorphicNFOn F W hsW
    have h0 : 0 ≤ meromorphicOrderAt (toMeromorphicNFOn F W) s := by
      rw [meromorphicOrderAt_toMeromorphicNFOn hF hsW]; exact hord' s hs
    exact (hNF.meromorphicOrderAt_nonneg_iff_analyticAt.mp h0).differentiableAt.differentiableWithinAt
  · intro s hs hFs
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hF (hsub hs), toMeromorphicNFAt_eq_self.mpr hFs.meromorphicNFAt]

end GoldbachBoundaries.Paper2.M3
