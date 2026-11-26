import GoldbachBoundaries.Paper2.M4b.Fill.meromorphicOn_Fmero

/-!
# M4b filler C1: `eventuallyEq_Fmero`

Identity theorem on the connected `ℍ_L`: at one point of `R_L` both `F` and `Fmero` equal the series near it, so they
agree off a discrete subset of `ℍ_L`, hence on a punctured neighbourhood of every point of the open `ℍ_L`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M4b

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **Every admissible continuation is `Fmero`** (RH, (K1), (K2), (R)). Take `s₀ = L⁻¹(3) ∈ R_L` (open):
`F =ᶠ[𝓝[≠] s₀] Dser W` (`eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin`) and `Dser W = Fmero` on `R_L`
(`Fmero_of_RL`). Both are meromorphic on the preconnected `ℍ_L` (`isPreconnected_HL`, `meromorphicOn_Fmero`), so
M2's `eventuallyEq_codiscreteWithin_of_nhdsNE` gives `F = Fmero` off a discrete subset of `ℍ_L`, and then
`eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin` at each point of the open `ℍ_L`. -/
theorem eventuallyEq_Fmero (hRH : RiemannHypothesis) (A : Aff) (k : ℂ → ℂ → ℂ) (W : ℂ → ℕ → ℕ → ℂ)
    (hK1 : K1 A k) (hK2 : K2 A k) (hR : HypR A k W Q) {F : ℂ → ℂ} (hF : MeromorphicOn F A.HL)
    (hFW : F =ᶠ[codiscreteWithin A.RL] Dser W) : ∀ s ∈ A.HL, F =ᶠ[𝓝[≠] s] Fmero A k W := by
  -- a point of `R_L`
  set s₀ : ℂ := (((3 - A.ell0) / A.ell : ℝ) : ℂ) with hs₀
  have hs₀re : (A.app s₀).re = 3 := by
    rw [app_re', hs₀, ofReal_re]
    field_simp [A.ell_pos.ne']
    ring
  have hs₀RL : s₀ ∈ A.RL := by show 2 < (A.app s₀).re; rw [hs₀re]; norm_num
  have hs₀HL : s₀ ∈ A.HL := by show 1 < (A.app s₀).re; rw [hs₀re]; norm_num
  have hn : A.RL ∈ 𝓝 s₀ := (isOpen_RL A).mem_nhds hs₀RL
  have h1 : F =ᶠ[𝓝[≠] s₀] Dser W := eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin hFW hn
  have h2 : Dser W =ᶠ[𝓝[≠] s₀] Fmero A k W := by
    filter_upwards [nhdsWithin_le_nhds hn] with t ht
    exact (Fmero_of_RL A k W ht).symm
  have hcod : F =ᶠ[codiscreteWithin A.HL] Fmero A k W :=
    M2.eventuallyEq_codiscreteWithin_of_nhdsNE (isPreconnected_HL A) hF
      (meromorphicOn_Fmero hRH A k W hK1 hK2 hR) hs₀HL (h1.trans h2)
  intro s hs
  exact eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin hcod ((M4a.isOpen_HL A).mem_nhds hs)

end GoldbachBoundaries.Paper2.M4b
