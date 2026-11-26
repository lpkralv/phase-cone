import GoldbachBoundaries.Paper2.M6.Omega
import GoldbachBoundaries.Paper2.M6.Fill.hasDerivAt_Ptil
import GoldbachBoundaries.Paper2.M6.Fill.Ptil_eqOn_P
import GoldbachBoundaries.Paper2.M6.Fill.P_conj
import GoldbachBoundaries.Paper2.M6.Fill.Ptil_conj

/-!
# M6: the principal sheet `P̃` (`cl:lem:P`(ii))

`P̃ = Ptil`, `P̃(z) = P(z + 2) + ∫_0^2 Q(z + t) dt` (`Defs.lean`). The paper defines `P̃(z) = P(2) - ∫_2^z Q` along any
path in the simply connected `Ω`; the explicit formula uses only that eastward rays stay in `Ω`
(`add_real_mem_OmegaP`), so the monodromy theorem is not needed. Uniqueness is the identity theorem on the connected
`Ω` (`eqOn_OmegaP_of_eqOn_halfPlane_one`); `P̃' = -Q` holds for every continuation `Qc` of `Q`, since `Qc = Qcont` off
`Σ` (M1's `isQCont_eventuallyEq`) and `Ω ⊆ {Re z > 0} ∖ Σ`; the symmetry comes from `P(z̄) = conj P(z)` and M1's
`Qcont_conj`. No RH and no (Z1): the statement carries them (choice 1; the paper's "symmetry of `Ω`" through
`nr:lem:Q`(i)), but `Σ̄ = Σ` is unconditional (paper 1's `conj_mem_nontrivialZeros`).
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M6

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-! ## Lemmas

Proved in `Fill/`, one file per lemma (same name, same statement): `hasDerivAt_Ptil`, `Ptil_eqOn_P`, `P_conj`, `Ptil_conj`. -/

/-! ## Target -/

/-- `lem_P_ii` of `Paper2/Statements.lean`, statement verbatim. -/
theorem lem_P_ii_proof (hRH : RiemannHypothesis) (hZ1 : Z1) :
    ∃ Pt : ℂ → ℂ, DifferentiableOn ℂ Pt OmegaP ∧ EqOn Pt P (halfPlane 1) ∧
      (∀ Pt' : ℂ → ℂ, DifferentiableOn ℂ Pt' OmegaP → EqOn Pt' P (halfPlane 1) → EqOn Pt' Pt OmegaP) ∧
      (∀ Qc : ℂ → ℂ, IsQCont Qc → ∀ z ∈ OmegaP, HasDerivAt Pt (-Qc z) z) ∧
      ∀ z ∈ OmegaP, Pt (conj z) = conj (Pt z) := by
  have _ := hRH  -- RH is not used (choice 1 puts it on every Section 4 statement)
  have _ := hZ1  -- (Z1) is not used: `Σ̄ = Σ` and `Qcont(z̄) = conj Qcont(z)` are unconditional
  have hd : DifferentiableOn ℂ Ptil OmegaP := fun z hz =>
    (hasDerivAt_Ptil hz).differentiableAt.differentiableWithinAt
  refine ⟨Ptil, hd, Ptil_eqOn_P, fun Pt' hPt' hEq => ?_, fun Qc hQc z hz => ?_, fun z hz => Ptil_conj hz⟩
  · exact eqOn_OmegaP_of_eqOn_halfPlane_one hPt' hd fun z hz => (hEq hz).trans (Ptil_eqOn_P hz).symm
  · rw [(M1.isQCont_eventuallyEq hQc).1 z (OmegaP_subset hz)]
    exact hasDerivAt_Ptil hz

end GoldbachBoundaries.Paper2.M6
