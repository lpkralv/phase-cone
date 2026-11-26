import GoldbachBoundaries.Paper2.M5.Qleft
import GoldbachBoundaries.Paper2.M5.Fill.«tsum_add_prime_eq_verticalIntegral'»
import GoldbachBoundaries.Paper2.M5.Fill.«Tk_succ_eq_verticalIntegral'»
import GoldbachBoundaries.Paper2.M5.Fill.norm_TkIntegrand_le_far
import GoldbachBoundaries.Paper2.M5.Fill.TkLine_differentiableOn
import GoldbachBoundaries.Paper2.M5.Fill.norm_TkLine_le
import GoldbachBoundaries.Paper2.M5.Fill.TkLine_eq_of_no_pole
import GoldbachBoundaries.Paper2.M5.Fill.TkLine_step_pole
import GoldbachBoundaries.Paper2.M5.Fill.TkLine_step_sub_one

/-!
# M5: the line integrals of `cl:thm:Tk` (Theorem G)

The iterated Mellin–Barnes identity `(cl:eq:Tk)` and the three facts about the line integrals that the induction step
uses ("Line integrals" in the paper's proof): holomorphy in `s`, polynomial growth in `Im s` (through `cl:lem:kernelt`,
so (Z6)), and the line moves (none, across the pole `w = m` of `T_m`, across the pole `w = s - 1` of `Q(s - w)`).

Every lemma about `TkLine F` takes the package `TkPack m F H` of the previous level and uses only its analytic parts:
`F` analytic on `Re w > m - 1/2` except at `m`, a simple pole at `m` with residue `r_m = 1/(m-1)!`, and polynomial growth
on vertical strips (fields 5-8). Under RH the second factor `Q(s - w)` is paper 1's `Qcont`, analytic on
`Re > 1/2` except at `1` (`analyticAt_Qcont_of_RH`) and `≪ log` there (`norm_Qcont_le_log`); the kernel is bounded by
M1's polynomial `Γ` decay (`norm_KerS_mul_pow_le`) when `s` stays in a compact set, and by `cl:lem:kernelt` (M4a's
`lem_kernelt_proof`) when the height of `s` grows.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-! ## Lemmas: the iterated Mellin–Barnes identity

Proved in `Fill/`, one file per lemma (same name, same statement): `tsum_add_prime_eq_verticalIntegral'`, `Tk_succ_eq_verticalIntegral'`. -/

/-! ## Lemmas: bounds and holomorphy of the line integrals

Proved in `Fill/`, one file per lemma (same name, same statement): `norm_TkIntegrand_le_far`, `TkLine_differentiableOn`, `norm_TkLine_le`. -/

/-! ## Lemmas: line moves

Proved in `Fill/`, one file per lemma (same name, same statement): `TkLine_eq_of_no_pole`, `TkLine_step_pole`, `TkLine_step_sub_one`. -/

end GoldbachBoundaries.Paper2.M5
