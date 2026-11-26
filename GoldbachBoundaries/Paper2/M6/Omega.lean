import GoldbachBoundaries.Paper2.M6.Defs
import GoldbachBoundaries.Paper2.M6.Fill.OmegaP_subset
import GoldbachBoundaries.Paper2.M6.Fill.halfPlane_one_subset_OmegaP
import GoldbachBoundaries.Paper2.M6.Fill.add_real_mem_OmegaP
import GoldbachBoundaries.Paper2.M6.Fill.conj_mem_OmegaP
import GoldbachBoundaries.Paper2.M6.Fill.isOpen_OmegaP
import GoldbachBoundaries.Paper2.M6.Fill.isPathConnected_OmegaP
import GoldbachBoundaries.Paper2.M6.Fill.contractibleSpace_OmegaP
import GoldbachBoundaries.Paper2.M6.Fill.eqOn_OmegaP_of_eqOn_halfPlane_one

/-!
# M6: the region `Ω` (`cl:lem:P`(i))

`Ω = {Re z > 0} ∖ ⋃_{a ∈ Σ} (a - [0, ∞))`. The paper's proof, made explicit:

* every point of `Σ` has `0 < Re a ≤ 1` (M1's `poleSetQ_re_bounds`), so every cut lies in `Re z ≤ 1` and
  `{Re z > 1} ⊆ Ω`; each `a ∈ Σ ∩ {Re z > 0}` lies on its own cut, so `Ω ⊆ {Re z > 0} ∖ Σ`;
* a cut meets a small disc about `z₀` (`Re z₀ > 0`) only if its point lies in a compact subset of `{Re z > 0}`, which
  meets `Σ` in a finite set (M1's `poleSetQ_locallyFinite`); so near `z₀` the union of the cuts is a finite union of
  closed sets and `Ω` is open;
* eastward rays stay in `Ω` (`add_real_mem_OmegaP`); so every point is joined to the convex set `{Re z ≥ 2} ⊆ Ω`
  (path connected), and `z ↦ z + t max(0, 2 - Re z)` followed by the straight-line contraction of `{Re z ≥ 2}` to
  `2` contracts `Ω` (contractible, hence simply connected by Mathlib's `SimplyConnectedSpace.ofContractible`).

None of this uses RH: the statement carries it by choice 1 (RH throughout Section 4). The identity theorem on `Ω`
(`eqOn_OmegaP_of_eqOn_halfPlane_one`) and the conjugation symmetry of `Ω` are used by `cl:lem:P`(ii).
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M6

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-! ## Lemmas

Proved in `Fill/`, one file per lemma (same name, same statement): `OmegaP_subset`, `halfPlane_one_subset_OmegaP`, `add_real_mem_OmegaP`, `conj_mem_OmegaP`, `isOpen_OmegaP`, `isPathConnected_OmegaP`, `contractibleSpace_OmegaP`, `eqOn_OmegaP_of_eqOn_halfPlane_one`. -/

/-! ## Target -/

/-- `lem_P_i` of `Paper2/Statements.lean`, statement verbatim. -/
theorem lem_P_i_proof (hRH : RiemannHypothesis) :
    IsOpen OmegaP ∧ IsConnected OmegaP ∧ SimplyConnectedSpace OmegaP ∧ halfPlane 1 ⊆ OmegaP := by
  have _ := hRH  -- RH is not used: `Σ` lies in `0 < Re ≤ 1` and is locally finite unconditionally
  have := contractibleSpace_OmegaP
  exact ⟨isOpen_OmegaP, isPathConnected_OmegaP.isConnected, SimplyConnectedSpace.ofContractible _,
    halfPlane_one_subset_OmegaP⟩

end GoldbachBoundaries.Paper2.M6
