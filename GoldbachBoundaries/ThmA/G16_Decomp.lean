import GoldbachBoundaries.ThmA.G15_Kernel

/-!
# G16–G17. `lem:F0split`, `prop:decomp`, `prop:principal`

**Deviation from the paper's proof (not its statements).** `lem:F0split` is proved without the
hairpin contour: write `P_v = E_b + ∫_𝒮 dx/(z-x)` (`Pv_eq_Eb_add`, where `E_b = E - Log_v(z - w_b)` is
holomorphic on `Re z > b`), shift the `E_b` part from `Re z = c` to `Re z = b` (no singularity in
between; the log singularity of `E_b` at `w_b` sits on the line `Re z = b` and is integrable), and
shift the Cauchy part by Fubini plus the residue at `z = x` for each `x ∈ 𝒮` (the residue is
`Γ(x)t^{-x}`; summed over `𝒮` it is `L(t)`). This gives `F₀ = L + h₀` with the paper's `h₀`, and
replaces the hairpin, its small circle and the line-crossing argument by two standard shifts.

**Integrated layout.** The 11 lemmas this file stated with `sorry` (`norm_Eaux_le`, `F0_mellin`,
`verticalIntegral_Eb_shift`, `verticalIntegral_CauchyS_shift`, `F0_split`, `Pv_eq_Eb_add`,
`M0_identity`, `decomp_exists`, `analyticOn_Dc`, `Gb_spec`, `Gnat_spec`) are proved in
`Fill/<name>.lean`, statements unchanged, each with its sketch as docstring. This file keeps only
the definitions and real proofs that do not use them; `Htil_spec` moved to
`Fill/decomp_exists.lean`. `Assembly.lean` imports all of it.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open scoped Interval

namespace GoldbachBoundaries.ThmA

/-! ### Real proofs -/

end GoldbachBoundaries.ThmA
