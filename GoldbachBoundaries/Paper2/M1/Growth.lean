import GoldbachBoundaries.Paper2.M1.Kernel

/-!
# M1: growth of `Q` to the right of the zeros (`nr:lem:growthQ`)

`Qcont = A + ∑_{k ≥ 2} μ(k) A(k ·)` (`Qcont_eq_sum_add_tail` with `N = 2`; the `n = 0` term is `0`, the `n = 1` term
is `A = negLogDerivZeta`). The tail is bounded on `Re w ≥ 1/2 + 2δ` (`norm_sigmaTerm_le`); `A` is bounded on
`Re w ≥ 2` (`norm_negLogDerivZeta_le`); on `B_∞ + 2δ ≤ Re w ≤ 2`, `|Im w| ≥ H`, (Z3) and the (Z2) count of zeros in
unit windows give `|A(w)| ≪_δ log |Im w|`.

Paper 1's RH bound (`norm_Qcont_le_log`, `TIdentity/G7d_QcontBound.lean`) goes through Borel–Carathéodory, not (Z3);
it is not used here.

**Integrated layout.** The five lemmas this file stated with `sorry` (`sum_zetaMult_window_le`,
`norm_negLogDerivZeta_le_strip`, `norm_sigmaTail_two_le`, `not_mem_poleSetQ_of_goodHeight`, `norm_Qcont_le_growth`)
are proved in `Fill/<name>.lean`, statements unchanged, each with its sketch as docstring; `Assembly.lean` imports
them. This file keeps the statements' context and the real lemmas that use none of them.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M1

open GoldbachBoundaries GoldbachBoundaries.Paper2

end GoldbachBoundaries.Paper2.M1
