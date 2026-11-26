import GoldbachBoundaries.Paper2.M3.Fill.LandauCommon

/-! Fill of `differentiableOn_laplace` (Paper2/M3/Landau.lean): `LandauFill.hasDerivAt_lapN` with `n = 0`
(differentiation under the integral, dominated on a ball). -/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M3

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **Holomorphy right of the abscissa** (general). The set is open (a union of open half-planes). Near `s₀` with
`x < x' < Re s₀`, `x ∈ S`: for `Re s > x'` the `s`-derivative `-u φ(u)e^{-su}` is dominated by
`u φ(u) e^{-x'u} ≤ C φ(u)e^{-xu}` (`u e^{-(x'-x)u}` is bounded on `u > 0`). `hasDerivAt_integral_of_dominated_loc_of_deriv_le`
on a ball about `s₀`, then `DifferentiableAt.differentiableWithinAt`. Size: 150–300 lines. -/
theorem differentiableOn_laplace (φ : ℝ → ℝ) (hφm : Measurable ((Ioi (0 : ℝ)).domRestrict φ))
    (hφ0 : ∀ u, 0 < u → 0 ≤ φ u) :
    DifferentiableOn ℂ (laplace φ) {s | ∃ x ∈ laplaceConvSet φ, x < s.re} := by
  rintro s ⟨x, hx, hxs⟩
  rw [LandauFill.laplace_eq_lapN]
  exact (LandauFill.hasDerivAt_lapN hφ0 hx hxs 0).differentiableAt.differentiableWithinAt

end GoldbachBoundaries.Paper2.M3
