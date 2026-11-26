import GoldbachBoundaries.Paper2.M1.Cont

/-!
# M1: the residue at a pinch point (`nr:thm:residue`) and `nr:cor:1+u`

The residue of `𝒯_c` at `s₀` is read off `(nr:eq:cont)` (`hasResidue_Tc`), and the indicator bookkeeping of the paper's
three cases turns the sum over `x ∈ F_δ` into the sum over ordered pairs (`finsum_nu_eq_pairSum`). An arbitrary
meromorphic `F` agreeing with the series off a discrete subset of `σ > 2` equals `Tcont` near every point of
`σ > 2B_∞` (`eventuallyEq_Tcont_of_codiscrete`, the generalisation of paper 1's
`eventuallyEq_nhdsNE_of_agree_halfPlane_two` in `TBoundary.lean`).

**Integrated layout.** The seven lemmas this file stated with `sorry` (`pinchPairs_finite`, `hasResidue_Tc`,
`finsum_nu_eq_pairSum`, `hasResidue_Tcont`, `eventuallyEq_Tcont_of_codiscrete`, `pairSum_one_add`,
`pinchPairs_one_add_subset`) are proved in `Fill/<name>.lean`, statements unchanged, each with its sketch as
docstring; `Assembly.lean` imports them. This file keeps the statements' context and the real lemmas that use none of
them.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M1

open GoldbachBoundaries GoldbachBoundaries.Paper2

end GoldbachBoundaries.Paper2.M1
