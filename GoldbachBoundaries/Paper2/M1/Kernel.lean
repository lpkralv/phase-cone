import GoldbachBoundaries.Paper2.M1.BNumbers

/-!
# M1: the Mellin–Barnes kernel and `nr:lem:MB`

The paper bounds `K_s(w) = Γ(w)Γ(s-w)/Γ(s)` with Stirling (Z6, exponential decay). Every use in M1 is against
`Q ≪ log`, so polynomial decay of any order suffices, and paper 1's `norm_Gamma_mul_one_add_abs_im_pow_le`
(`TIdentity/Basic.lean`, no Stirling) gives it. The M1 lemmas therefore do not take (Z6); the target `lem_MB` keeps
its (Z6) premise (a premise that is not needed only strengthens the statement).

Mathlib provides the Beta integral (`Complex.betaIntegral`, `Complex.Gamma_mul_Gamma_eq_betaIntegral`) and Mellin
inversion (`mellin_inversion`, `Mathlib/Analysis/MellinInversion.lean`); paper 1's `Fw_eq_verticalIntegral'`
(`TIdentity/G9d_MellinInversion.lean`) is a worked example of the inversion in this library's `VerticalIntegral'` form.

**Integrated layout.** The five lemmas this file stated with `sorry` (`norm_KerS_mul_pow_le`,
`mellin_one_add_cpow_neg`, `one_add_cpow_neg_eq_verticalIntegral'`, `integrable_KerS_Q_line`,
`T_eq_verticalIntegral'_KerS`) are proved in `Fill/<name>.lean`, statements unchanged, each with its sketch as
docstring; `Assembly.lean` imports them. This file keeps the statements' context and the real lemmas that use none of
them.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M1

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- The symmetry `K_s(s - w) = K_s(w)`. -/
lemma KerS_sub_symm (s w : ℂ) : KerS s (s - w) = KerS s w := by
  simp only [KerS, sub_sub_cancel]
  ring

end GoldbachBoundaries.Paper2.M1
