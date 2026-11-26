import GoldbachBoundaries.Paper2.M1.Shift

/-!
# M1: the continuation of `T` to `σ > 2B_∞` (`nr:thm:cont`)

The paper's proof has four steps: (1) the representation `(nr:eq:cont)` for `σ > 2` by one contour shift from
`Re w = c₀ ∈ (1, σ - 1)` to `Re w = c`; (2) `I_c` is holomorphic on the region `(nr:eq:region)`; (3) the right side
`𝒯_c` continues across each line `σ = c + Re b₁` (an indented contour); (4) assembly over `c` and `δ`.

Change of proof (statement unchanged): Step 3 is replaced by the **independence of `𝒯_c` from `(δ, c)`**
(`Tc_indep`). For two admissible lines `c' < c` and `s` in both regions and off the pinch set, one contour shift
between the two lines (`Ic_sub_Ic`) gives `I_c - I_{c'}` as residues at the left points `a ∈ F_δ`, `c' < Re a < c`,
minus residues at the right points `s - b`, `c' < σ - Re b < c`; the indicators of `(nr:eq:cont)` change by exactly
these terms. Then `Tcont` (one formula per point, `Defs.lean`) agrees near every point with a single `𝒯_c` whose region
contains that point, which gives meromorphy, the simple poles in `Π` and the representation at once. No indented
contour, and no patching of local expressions.

**Integrated layout.** The 17 lemmas this file stated with `sorry` (`norm_gs_le_far`, `isOpen_RegC`,
`Ic_differentiableOn`, `Tc_eq_T`, `Ic_sub_Ic`, `Tc_mono_delta`, `Tc_indep`, `exists_adm_reg`, `Tc_analyticAt`,
`Tc_meromorphicAt`, `pinch_locallyFinite`, `T_differentiableOn`, `Tcont_props`, `Tcont_conj`, `IcQ_congr`,
`TcQ_congr`, `meromorphicOn_term`) are proved in `Fill/<name>.lean`, statements unchanged, each with its sketch as
docstring; `Assembly.lean` imports them. The real lemmas that use them moved to the fill file of the lemma they use:
`conj_mem_Pinch` to `Fill/conj_mem_poleSetQ.lean`, `Tcont_eq_Tc` to `Fill/Tc_indep.lean`, `Tcont_eqOn_T` to
`Fill/Tc_eq_T.lean`, `halfPlane_two_Binf_subset` to `Fill/half_le_Binf.lean`. This file keeps the statements' context
and the real lemmas that use none of them.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M1

open GoldbachBoundaries GoldbachBoundaries.Paper2

end GoldbachBoundaries.Paper2.M1
