import GoldbachBoundaries.Paper2.M4b.Rising

/-!
# M4b filler C1: `exists_differentiableOn_of_order_nonneg`

Removable singularities: `toMeromorphicNFOn f U` is in normal form on `U` with the orders of `f`, so it is analytic at
every point of `U` where the order is `≥ 0`; where `f` is already analytic it agrees with `f`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M4b

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **Removable singularities** (general). `g = toMeromorphicNFOn f U` is in meromorphic normal form on `U`
(`meromorphicNFOn_toMeromorphicNFOn`) with the same orders as `f` (`meromorphicOrderAt_toMeromorphicNFOn`); normal form
with order `≥ 0` is analyticity (`MeromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt`). Where `f` is analytic,
`g x = toMeromorphicNFAt f x x = f x` (`toMeromorphicNFOn_eq_toMeromorphicNFAt`, `toMeromorphicNFAt_eq_self`). -/
theorem exists_differentiableOn_of_order_nonneg {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : MeromorphicOn f U) (h : ∀ x ∈ U, 0 ≤ meromorphicOrderAt f x) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧ ∀ x ∈ U, AnalyticAt ℂ f x → g x = f x := by
  have _ := hU
  refine ⟨toMeromorphicNFOn f U, fun x hx => ?_, fun x hx hfx => ?_⟩
  · have hNF := meromorphicNFOn_toMeromorphicNFOn f U hx
    have hord : 0 ≤ meromorphicOrderAt (toMeromorphicNFOn f U) x := by
      rw [meromorphicOrderAt_toMeromorphicNFOn hf hx]
      exact h x hx
    exact (hNF.meromorphicOrderAt_nonneg_iff_analyticAt.mp hord).differentiableAt.differentiableWithinAt
  · rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hf hx, toMeromorphicNFAt_eq_self.2 hfx.meromorphicNFAt]

end GoldbachBoundaries.Paper2.M4b
