import GoldbachBoundaries.Paper2.M4b.Boundary
import GoldbachBoundaries.Paper2.M4b.Fill.K2_kerSq
import GoldbachBoundaries.Paper2.M4b.Fill.K2_kerS
import GoldbachBoundaries.Paper2.M4b.Fill.K4_kernels
import GoldbachBoundaries.Paper2.M4b.Fill.kerSq_basic
import GoldbachBoundaries.Paper2.M4b.Fill.kerS_basic

/-!
# M4b: the kernel hypotheses (K1)-(K4), (H2a)/(H2b) of the examples

`cl:ex:G`, `cl:prop:T0`: `K_s(z)` and `k₀ = K_s(z)(z-1)(s-1-z)` with `L(s) = s`; (K1), (H2a), (K3) and the brackets are
the real lemmas of `Defs.lean`, and (K2) is M4a's `K2_kr` at `r = 0` and `r = 1` (real lemmas below).
`cl:ex:squares`: `kerSq = ½Γ(z/2)Γ(s - z/2)/Γ(s)`, `L(s) = 2s`. `cl:ex:S`: `kerS = ½K((z - s + 1)/2)`,
`K(w) = Γ(w)Γ(2 - w)`, `L(s) = 2s + 1`. (K4) for all four: each kernel is a global quotient of entire functions of two
variables built from `1/Γ` (`isMeromorphic₂_of_global`, Defs).
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M4b

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-! ## Lemmas

Proved in `Fill/`, one file per lemma (same name, same statement): `K2_kerSq`, `K2_kerS`, `K4_kernels`, `kerSq_basic`, `kerS_basic`. -/

/-! ## Real lemmas -/

/-- (K2) for `K_s`: M4a's `K2_kr` at `r = 0`. -/
lemma kerG_K2 (hZ6 : Z6) : K2 Aff.idL kerG := kerG_eq_kr ▸ M4a.K2_kr hZ6 0

/-- (K2) for `k₀`: M4a's `K2_kr` at `r = 1`. -/
lemma k0_K2 (hZ6 : Z6) : K2 Aff.idL k0 := M4a.kr_one' ▸ M4a.K2_kr hZ6 1

/-- `½ ∈ D_L` for `L(s) = 2s + 1`. -/
lemma half_mem_DL_twoOneL : (1 / 2 : ℂ) ∈ Aff.twoOneL.DL := by
  simp only [Aff.DL, mem_ofPred_eq, twoOneL_app]; norm_num

/-- `1 ∈ D_L` for `L(s) = 2s`. -/
lemma one_mem_DL_twoL : (1 : ℂ) ∈ Aff.twoL.DL := by
  simp only [Aff.DL, mem_ofPred_eq, twoL_app]; norm_num

/-- `2 ∈ D_L` for `L(s) = s`. -/
lemma two_mem_DL_idL : (2 : ℂ) ∈ Aff.idL.DL := by
  simp only [Aff.DL, mem_ofPred_eq, M4a.app_idL]; norm_num

end GoldbachBoundaries.Paper2.M4b
