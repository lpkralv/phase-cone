import GoldbachBoundaries.Paper2.M4b.T0
import GoldbachBoundaries.Paper2.M4b.Fill.hypR_kerSq

/-!
# M4b: the hypotheses for `∑(p²+q²)^{-s}` (`cl:ex:squares`)

`L(s) = 2s`, `k(z,s) = ½Γ(z/2)Γ(s - z/2)/Γ(s) = kMB 2 0 s z`. (R) is `MB.lean` with `f(t) = (1 + t²)^{-s}`
(`(p² + q²)^{-s} = q^{-2s}(1 + (p/q)²)^{-s}`); the bracket is `kerSq_bracket` (Defs); (H3) is M4a's
`thm_class_H3_of_K4_proof` with `𝔟(1) ≠ 0`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M4b

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-! ## Lemmas

Proved in `Fill/`, one file per lemma (same name, same statement): `hypR_kerSq`. -/

/-! ## Target -/

/-- `ex_squares_hyp` of `Paper2/Statements.lean`, statement verbatim. -/
theorem ex_squares_hyp_proof (hRH : RiemannHypothesis) (hZ1 : Z1) (hZ6 : Z6) :
    K1 Aff.twoL kerSq ∧ H2a Aff.twoL kerSq ∧ K2 Aff.twoL kerSq ∧ K3 Aff.twoL kerSq ∧ K4 kerSq ∧
      HypR Aff.twoL kerSq WSq P ∧
      (∀ s : ℂ, 1 / 2 < s.re →
        bracket Aff.twoL kerSq s = (Real.sqrt Real.pi : ℂ) * Gamma (s - 1 / 2) / Gamma s ∧
          bracket Aff.twoL kerSq s ≠ 0) ∧
      H3 Aff.twoL kerSq := by
  obtain ⟨hK1, hH2a, hK3⟩ := kerSq_basic
  refine ⟨hK1, hH2a, K2_kerSq hZ6, hK3, K4_kernels.2.1, hypR_kerSq, fun s hs => kerSq_bracket hs, ?_⟩
  exact M4a.thm_class_H3_of_K4_proof hRH hZ1 Aff.twoL kerSq hK1 K4_kernels.2.1
    ⟨1, one_mem_DL_twoL, (kerSq_bracket (by norm_num)).2⟩

end GoldbachBoundaries.Paper2.M4b
