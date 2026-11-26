import GoldbachBoundaries.Paper2.M4a.Jseg

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
open scoped Interval
namespace GoldbachBoundaries.Paper2.M4a
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **The (H2b) right side is meromorphic on `ℂ`.** Each of `s ↦ g(L(s) - b - θs) = g((ℓ - θ)s + ℓ₀ - b)` and
`s ↦ g(a - θs)` is `g` composed with an affine (analytic) map, so meromorphic at every point
(`MeromorphicAt.comp_analyticAt`, from `hg` at the image point); constants, products and sums of meromorphic functions
are meromorphic. Size: 30–80 lines. -/
theorem meromorphicOn_H2b_rhs (A : Aff) {g : ℂ → ℂ} {θ : ℝ} (hg : MeromorphicOn g univ) (a b : ℂ) :
    MeromorphicOn (fun s => ((A.ell : ℂ) - θ) * g (A.app s - b - θ * s) + θ * g (a - θ * s)) univ := by
  intro s hs
  have h₁ : MeromorphicAt (fun s => g (A.app s - b - θ * s)) s :=
    (hg _ (mem_univ _)).comp_analyticAt (by unfold Aff.app; fun_prop)
  have h₂ : MeromorphicAt (fun s => g (a - θ * s)) s :=
    (hg _ (mem_univ _)).comp_analyticAt (by fun_prop)
  exact (MeromorphicAt.const _ s |>.mul h₁).add (MeromorphicAt.const _ s |>.mul h₂)

end GoldbachBoundaries.Paper2.M4a
