import GoldbachBoundaries.Paper2.M2.Single
import GoldbachBoundaries.Paper2.M2.Fill.eventuallyEq_codiscreteWithin_of_nhdsNE
import GoldbachBoundaries.Paper2.M2.Fill.neg_deriv_eventuallyEq_Qcont_of_isPBranch
import GoldbachBoundaries.Paper2.M2.Fill.singleRep_points_infinite

/-!
# Filler (Group D): `cor_LW_branch` (part 3 of `nr:cor:LW`)

A meromorphic extension `f` of a branch `g` of `P` to `D = Δ(iy, r)` gives the meromorphic `-f'` on `D`, equal to
`-g' = Qcont` near `z₁`, hence to `Qcont` off a discrete subset of the convex set `D ∩ {Re z > 0}`: a meromorphic
extension of `Qcont` across `iy`, which `noMeromorphicExtensionAt_Qcont` forbids.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M2

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **Part 3 of `cor_LW`** (Z1, Z2, Z4, Z5). Suppose `f` is meromorphic on `D = Δ(iy, r)` with `f = g` on a
punctured neighbourhood of `z₁ ∈ D`. Then `h = -f'` is meromorphic on `D` (`MeromorphicOn.deriv`, `.neg`), and
`h = -g'` on a punctured neighbourhood of `z₁` (at each point of the open punctured neighbourhood `f = g` near the
point, `Filter.EventuallyEq.deriv_eq`), so `h = Qcont` on a punctured neighbourhood of `z₁`
(`neg_deriv_eventuallyEq_Qcont_of_isPBranch`). `V = D ∩ {Re z > 0}` is convex, contains `z₁`, and `h`, `Qcont` are
meromorphic on `V`, so `h = Qcont` off a discrete subset of `V` (`eventuallyEq_codiscreteWithin_of_nhdsNE`). This is a
meromorphic extension of `Qcont` across `iy` on `Δ(iy, r)`, contradicting `noMeromorphicExtensionAt_Qcont`.
Size: 100–200 lines. -/
theorem cor_LW_branch (hZ1 : Z1) (hZ2 : Z2) (hZ4 : Z4) (hZ5 : Z5) :
    ∀ (g : ℂ → ℂ) (z₁ : ℂ), IsPBranch g z₁ → ∀ y r : ℝ, 0 < r → z₁ ∈ ball ((y : ℂ) * I) r →
      ¬ GermExtendsMeromorphically g z₁ (ball ((y : ℂ) * I) r) := by
  rintro g z₁ hg y r hr hz₁ ⟨-, f, hf, hfg⟩
  obtain ⟨hz₁mem, hderiv⟩ := neg_deriv_eventuallyEq_Qcont_of_isPBranch hg
  set D := ball ((y : ℂ) * I) r with hD
  have hh : MeromorphicOn (fun z => -deriv f z) D := hf.deriv.neg
  have hloc : (fun z => -deriv f z) =ᶠ[𝓝[≠] z₁] Qcont := by
    filter_upwards [hfg.nhdsNE_deriv, nhdsWithin_le_nhds hderiv] with z hz hz'
    rw [hz]
    exact hz'
  have hVc : IsPreconnected (D ∩ halfPlane 0) :=
    ((convex_ball _ _).inter (convex_halfSpace_re_gt 0)).isPreconnected
  have hcod : (fun z => -deriv f z) =ᶠ[codiscreteWithin (D ∩ halfPlane 0)] Qcont :=
    eventuallyEq_codiscreteWithin_of_nhdsNE hVc (hh.mono_set inter_subset_left)
      (isQCont_Qcont.1.mono_set inter_subset_right) ⟨hz₁, hz₁mem.1⟩ hloc
  exact noMeromorphicExtensionAt_Qcont hZ1 hZ2 hZ4 hZ5 y r hr ⟨_, hh, hcod⟩

end GoldbachBoundaries.Paper2.M2
