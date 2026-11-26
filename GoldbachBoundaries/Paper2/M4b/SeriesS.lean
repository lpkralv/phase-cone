import GoldbachBoundaries.Paper2.M4b.Squares
import GoldbachBoundaries.Paper2.M4b.Fill.hypR_kerS

/-!
# M4b: the hypotheses for `S(s) = ∑ p^{1-s}q^{2-s}(p²+q²)^{-2}` (`cl:ex:S`)

`L(s) = 2s + 1`, `k(z,s) = ½K((z - s + 1)/2) = kMB 2 (1 - s) 2 z` (`K_2(w) = Γ(w)Γ(2-w)/Γ(2)`, `Γ(2) = 1`). (R) is
`MB.lean` with `f(t) = t^{1-s}(1 + t²)^{-2}`. The plan's risk "`ex_S`'s Fubini with a free `θ`" does not arise: the
paper's AM-GM choice of `θ` proves absolute convergence, which `tsum_eq_verticalIntegral'_of_mellin` gives directly
from the convergence of `∑_p p^{-c}` and `∑_q q^{-(2σ+1-c)}` on a line `c`. (K1), (H2b), (K3), the bracket identity and
the values `𝔟(0)`, `𝔟(½) ≠ 0` are `kerS_basic`; (H3) is M4a's `thm_class_H3_of_K4_proof` at `s = ½ ∈ D_L` (the paper's
`𝔟(0)` is on the boundary line, not in `D_L`).
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M4b

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-! ## Lemmas

Proved in `Fill/`, one file per lemma (same name, same statement): `hypR_kerS`. -/

/-! ## Target -/

/-- `ex_S_hyp` of `Paper2/Statements.lean`, statement verbatim. -/
theorem ex_S_hyp_proof (hRH : RiemannHypothesis) (hZ1 : Z1) (hZ6 : Z6) :
    K1 Aff.twoOneL kerS ∧ H2b kerS ∧ K2 Aff.twoOneL kerS ∧ K3 Aff.twoOneL kerS ∧ K4 kerS ∧
      HypR Aff.twoOneL kerS WS P ∧
      (∀ s : ℂ, bracket Aff.twoOneL kerS s = 1 / 2 * (KS (1 - s / 2) + KS ((s + 1) / 2))) ∧
      bracket Aff.twoOneL kerS 0 = 1 / 2 * (1 + Real.pi / 2) ∧
      H3 Aff.twoOneL kerS := by
  obtain ⟨hK1, hH2b, hK3, hbr, hb0, hbhalf⟩ := kerS_basic
  refine ⟨hK1, hH2b, K2_kerS hZ6, hK3, K4_kernels.2.2.1, hypR_kerS, hbr, hb0, ?_⟩
  exact M4a.thm_class_H3_of_K4_proof hRH hZ1 Aff.twoOneL kerS hK1 K4_kernels.2.2.1
    ⟨1 / 2, half_mem_DL_twoOneL, hbhalf⟩

end GoldbachBoundaries.Paper2.M4b
