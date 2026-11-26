import GoldbachBoundaries.Paper2.M4a.Fill.BCommon

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
open scoped Interval
namespace GoldbachBoundaries.Paper2.M4a
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **`J_{ab}` is holomorphic where `k` is** (general `U`; used with `U = D_L` under (K1) and `U = ℍ_L` under (H2a)).
The set `W = {(z, s) : s ∈ U, z ∈ Str(s)}` is open in `ℂ²`, so `k` is (jointly) `DifferentiableAt`, hence continuous,
at its points. Put `f s t = k(a + t(L(s) - a - b), s)`: for `s ∈ U` and `t ∈ [0, 1]` the point lies on the segment,
in `Str(s)` (`segment_subset_Str`, `U ⊆ ℍ_L`), so `(s, t) ↦ f s t` is continuous on `U ×ˢ [0, 1]` and holomorphic in
`s` for fixed `t` (chain rule, the inner map is affine in `s`). Paper 1's
`ThmA.differentiableOn_intervalIntegral_of_continuousOn` gives the integral; multiply by `L(s) - a - b`.
Size: 150–250 lines. -/
theorem differentiableOn_Jseg (A : Aff) (k : ℂ → ℂ → ℂ) {U : Set ℂ} (hU : IsOpen U) (hUH : U ⊆ A.HL)
    (hk : DifferentiableOn ℂ (fun p : ℂ × ℂ => k p.1 p.2) {p | p.2 ∈ U ∧ p.1 ∈ A.Str p.2})
    {a b : ℂ} (ha : a ∈ PoleSetQ) (hb : b ∈ PoleSetQ) :
    DifferentiableOn ℂ (Jseg A k a b) U := by
  exact (by unfold Aff.app; fun_prop :
    DifferentiableOn ℂ (fun s => A.app s - a - b) U).mul
    (GroupB.differentiableOn_integral A k hU hUH hk ha hb)

end GoldbachBoundaries.Paper2.M4a
