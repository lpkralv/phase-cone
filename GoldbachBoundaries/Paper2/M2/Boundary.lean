import GoldbachBoundaries.Paper2.M2.Lambda
import GoldbachBoundaries.Paper2.M2.Fill.Binf_eq_half_of_Hinf

/-!
# M2: `(H_∞)` and the number `B_∞` (input of `nr:thm:boundary`)

`thm_boundary_proof` (`Skeleton.lean`) needs `2B_∞ = 1` under `(H_∞)`, so that the half-plane `σ > 2B_∞` of M1's
continuation `Tcont` is `ℍ`, and `B < 1` (M1's `Bsup_lt_one_of_Hinf`). The paper states the first as
"Under `(H_∞)`, `2B_∞ = 1`"; with the Lean definitions (`Hinf` is the finiteness gloss, `Binf` an infimum of
suprema) it needs `B_∞ ≥ 1/2`, i.e. (Z1) (`half_le_Binf`).

**Integrated layout.** The lemma this file stated with `sorry` (`Binf_eq_half_of_Hinf`) is proved in
`Fill/<name>.lean`, statement unchanged, with its filler's docstring; the fill file imports `Lambda.lean`, and this
file imports it.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M2

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

end GoldbachBoundaries.Paper2.M2
