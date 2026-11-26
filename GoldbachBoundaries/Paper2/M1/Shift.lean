import GoldbachBoundaries.Paper2.M1.Growth

/-!
# M1: general contour tools (reusable beyond M1)

Two general lemmas about PNT+'s `VerticalIntegral'` (which includes the factor `1/(2πi)`), used by `nr:thm:cont`
and again by `cl:thm:mero`, `cl:thm:Tk` and `cl:thm:filter` in later milestones:

* moving a vertical line of integration past finitely many simple poles (paper 1's
  `verticalIntegral'_eq_add_of_simplePole`, `TIdentity/Basic.lean`, does one pole; its proof is a port of PNT+'s
  `tendsto_truncated_vertical_shift_with_simple_pole` through `ResidueTheoremOnRectangleWithSimplePole'`);
* holomorphy of a vertical integral depending holomorphically on a parameter, under local uniform domination.

**Integrated layout.** The two lemmas this file stated with `sorry` (`verticalIntegral'_eq_add_sum_of_simplePoles`,
`differentiableOn_verticalIntegral'`) are proved in `Fill/<name>.lean`, statements unchanged, each with its sketch as
docstring; `Assembly.lean` imports them. This file keeps the statements' context and the real lemmas that use none of
them.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M1

open GoldbachBoundaries GoldbachBoundaries.Paper2

end GoldbachBoundaries.Paper2.M1
