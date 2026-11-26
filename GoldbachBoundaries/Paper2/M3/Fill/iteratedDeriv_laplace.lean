import GoldbachBoundaries.Paper2.M3.Fill.LandauCommon

/-! Fill of `iteratedDeriv_laplace` (Paper2/M3/Landau.lean): `LandauFill.iteratedDeriv_laplace_eq` (induction on
`n`, local agreement on the open set right of a point of `S`). -/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M3

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **Derivatives at real points** (general). For real `a` with some `x ∈ S`, `x < a`:
`𝓛^{(n)}(a) = ∫_0^∞ (-u)^n φ(u)e^{-au} du`, by induction on `n` with the same domination as in
`differentiableOn_laplace` (`u^n e^{-(a'-x)u}` bounded for `x < a' < a`), applied on a neighbourhood of `a`
(`iteratedDeriv_succ`, `HasDerivAt.deriv`, and `Filter.EventuallyEq.deriv_eq` for the induction on a neighbourhood).
Size: 150–250 lines. -/
theorem iteratedDeriv_laplace (φ : ℝ → ℝ) (hφm : Measurable ((Ioi (0 : ℝ)).domRestrict φ))
    (hφ0 : ∀ u, 0 < u → 0 ≤ φ u) {a : ℝ} (ha : ∃ x ∈ laplaceConvSet φ, x < a) (n : ℕ) :
    iteratedDeriv n (laplace φ) (a : ℂ) =
      ∫ u in Ioi (0 : ℝ), ((-(u : ℂ)) ^ n * (φ u : ℂ)) * exp (-((a : ℂ) * u)) := by
  rw [LandauFill.iteratedDeriv_laplace_eq hφ0 n (a : ℂ) (by simpa using ha)]
  rfl

end GoldbachBoundaries.Paper2.M3
