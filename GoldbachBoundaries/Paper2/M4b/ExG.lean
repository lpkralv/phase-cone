import GoldbachBoundaries.Paper2.M4b.Kernels
import GoldbachBoundaries.Paper2.M4b.Fill.hypR_kerG_WG
import GoldbachBoundaries.Paper2.M4b.Fill.hypR_kerG_WT

/-!
# M4b: the hypotheses for `T` and `G` (`ex_T_hyp`, `cl:ex:G`)

`L(s) = s`, `k = K_s(z)`. (K1), (H2a), (K3), (K2) and the bracket `2/(s - 1)` are in `Defs.lean` and `Kernels.lean`;
(K4) is `K4_kernels`. (R) for `G` (with `P`) and for `T` (with `Q`) is the rising-factorial lemma of `Rising.lean` with
`N = 1`, `c = 1` (`WG_eq_Wrise`, `kerG_eq_krise`). (H3) is M4a's `thm_class_H3_of_K4_proof` with `𝔟(2) = 2 ≠ 0`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M4b

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-! ## Lemmas

Proved in `Fill/`, one file per lemma (same name, same statement): `hypR_kerG_WG`, `hypR_kerG_WT`. -/

/-! ## Targets -/

/-- `ex_T_hyp` of `Paper2/Statements.lean`, statement verbatim. -/
theorem ex_T_hyp_proof (hRH : RiemannHypothesis) (hZ6 : Z6) :
    K1 Aff.idL kerG ∧ K2 Aff.idL kerG ∧ HypR Aff.idL kerG WT Q := by
  have _ := hRH  -- RH (choice 1) is not used
  exact ⟨kerG_K1, kerG_K2 hZ6, hypR_kerG_WT⟩

/-- `ex_G_hyp` of `Paper2/Statements.lean`, statement verbatim. -/
theorem ex_G_hyp_proof (hRH : RiemannHypothesis) (hZ1 : Z1) (hZ6 : Z6) :
    K1 Aff.idL kerG ∧ H2a Aff.idL kerG ∧ K2 Aff.idL kerG ∧ K3 Aff.idL kerG ∧ K4 kerG ∧
      HypR Aff.idL kerG WG P ∧ H3 Aff.idL kerG := by
  refine ⟨kerG_K1, kerG_H2a, kerG_K2 hZ6, kerG_K3, K4_kernels.1, hypR_kerG_WG, ?_⟩
  refine M4a.thm_class_H3_of_K4_proof hRH hZ1 Aff.idL kerG kerG_K1 K4_kernels.1
    ⟨2, two_mem_DL_idL, ?_⟩
  rw [kerG_bracket (by norm_num)]
  norm_num

end GoldbachBoundaries.Paper2.M4b
