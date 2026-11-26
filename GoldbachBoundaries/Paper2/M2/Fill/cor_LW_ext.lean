import GoldbachBoundaries.Paper2.M2.Single
import GoldbachBoundaries.Paper2.M2.Fill.eventuallyEq_codiscreteWithin_of_nhdsNE
import GoldbachBoundaries.Paper2.M2.Fill.exists_imagAxis_mem
import GoldbachBoundaries.Paper2.M2.Fill.singleRep_points_infinite

/-!
# Filler (Group D): `cor_LW_ext` (part 2 of `nr:cor:LW`)

A meromorphic `f` on `W ⊋ {Re z > 0}` agreeing with `Q` off a discrete subset of `{Re z > 1}` agrees with `Qcont`
near `2`, hence off a discrete subset of `{Re z > 0}` (identity theorem), and `W` contains a disc about some `iy`:
a meromorphic extension of `Qcont` across `iy`, which `noMeromorphicExtensionAt_Qcont` forbids.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M2

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **Part 2 of `cor_LW`** (Z1, Z2, Z4, Z5). Suppose `f` is meromorphic on `W` and `f = Q` off a discrete subset of
`{Re z > 1}`. `Qcont = Q` on `{Re z > 1}` (`isQCont_Qcont`), so `f = Qcont` on a punctured neighbourhood of `2`
(paper 1's `eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin`); both are meromorphic on `{Re z > 0} ⊆ W`, so
`f = Qcont` off a discrete subset of `{Re z > 0}` (`eventuallyEq_codiscreteWithin_of_nhdsNE`, half-planes are
convex). Take `iy ∈ W` (`exists_imagAxis_mem`) and `r > 0` with `Δ(iy, r) ⊆ W`; then `f` is meromorphic on
`Δ(iy, r)` and agrees with `Qcont` off a discrete subset of `Δ(iy, r) ∩ {Re z > 0}` (`Filter.codiscreteWithin.mono`),
contradicting `noMeromorphicExtensionAt_Qcont`. Size: 80–150 lines. -/
theorem cor_LW_ext (hZ1 : Z1) (hZ2 : Z2) (hZ4 : Z4) (hZ5 : Z5) :
    ∀ W : Set ℂ, IsOpen W → IsConnected W → halfPlane 0 ⊂ W →
      ¬ ∃ f : ℂ → ℂ, MeromorphicOn f W ∧ f =ᶠ[codiscreteWithin (halfPlane 1)] Q := by
  rintro W hWo hWc hsub ⟨f, hf, hfQ⟩
  have h2 : (2 : ℂ) ∈ halfPlane 1 := by norm_num [halfPlane]
  have hn2 : halfPlane 1 ∈ 𝓝 (2 : ℂ) := (isOpen_halfPlane 1).mem_nhds h2
  have hfQ2 : f =ᶠ[𝓝[≠] (2 : ℂ)] Q := eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin hfQ hn2
  have hQQ2 : Qcont =ᶠ[𝓝[≠] (2 : ℂ)] Q :=
    Filter.mem_of_superset (nhdsWithin_le_nhds hn2) fun s hs => isQCont_Qcont.2.1 hs
  have hfQc2 : f =ᶠ[𝓝[≠] (2 : ℂ)] Qcont := hfQ2.trans hQQ2.symm
  have h2' : (2 : ℂ) ∈ halfPlane 0 := by norm_num [halfPlane]
  have hcod : f =ᶠ[codiscreteWithin (halfPlane 0)] Qcont :=
    eventuallyEq_codiscreteWithin_of_nhdsNE (convex_halfSpace_re_gt 0).isPreconnected
      (hf.mono_set hsub.1) isQCont_Qcont.1 h2' hfQc2
  obtain ⟨y, hy⟩ := exists_imagAxis_mem hWc hsub
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hWo _ hy
  exact noMeromorphicExtensionAt_Qcont hZ1 hZ2 hZ4 hZ5 y r hr
    ⟨f, hf.mono_set hball, Filter.codiscreteWithin_mono inter_subset_right hcod⟩

end GoldbachBoundaries.Paper2.M2
