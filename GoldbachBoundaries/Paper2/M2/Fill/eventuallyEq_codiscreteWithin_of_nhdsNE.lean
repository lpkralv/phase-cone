import GoldbachBoundaries.Paper2.M2.Single

/-!
# Filler (Group D): `eventuallyEq_codiscreteWithin_of_nhdsNE`

Meromorphic identity theorem applied to `f - g`: order `⊤` at `z₁` propagates over the preconnected `U`
(`MeromorphicOn.meromorphicOrderAt_eq_top_of_isPreconnected`), so `f = g` on a punctured neighbourhood of every point
of `U`, which is agreement off a discrete subset of `U` (`mem_codiscreteWithin`).
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M2

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **Identity theorem off a discrete set** (general). `f - g` is meromorphic on `U` with order `⊤` at `z₁`
(`meromorphicOrderAt_eq_top_iff`), hence order `⊤` at every point of the preconnected `U`
(`MeromorphicOn.meromorphicOrderAt_eq_top_of_isPreconnected`, as in paper 1's
`eventuallyEq_nhdsNE_of_agree_halfPlane_two`), i.e. `f = g` on a punctured neighbourhood of every point of `U`; that
is agreement off a discrete subset of `U` (`mem_codiscreteWithin`). Size: 60–120 lines. -/
theorem eventuallyEq_codiscreteWithin_of_nhdsNE {f g : ℂ → ℂ} {U : Set ℂ} (hUc : IsPreconnected U)
    (hf : MeromorphicOn f U) (hg : MeromorphicOn g U) {z₁ : ℂ} (hz₁ : z₁ ∈ U) (h : f =ᶠ[𝓝[≠] z₁] g) :
    f =ᶠ[codiscreteWithin U] g := by
  have htop1 : meromorphicOrderAt (f - g) z₁ = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    filter_upwards [h] with z hz
    simp [hz]
  have hloc : ∀ x ∈ U, f =ᶠ[𝓝[≠] x] g := by
    intro x hx
    have htop := (hf.sub hg).meromorphicOrderAt_eq_top_of_isPreconnected hUc hz₁ hx htop1
    rw [meromorphicOrderAt_eq_top_iff] at htop
    filter_upwards [htop] with s hs
    exact sub_eq_zero.mp hs
  rw [Filter.EventuallyEq, Filter.Eventually, mem_codiscreteWithin]
  intro x hx
  rw [disjoint_principal_right]
  filter_upwards [hloc x hx] with y hy
  intro hy'
  exact hy'.2 hy

end GoldbachBoundaries.Paper2.M2
