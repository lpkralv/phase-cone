import GoldbachBoundaries.Paper2.M6.Ptil
import GoldbachBoundaries.Paper2.M6.Fill.isOpen_halfPlane_diff_poleSetQ
import GoldbachBoundaries.Paper2.M6.Fill.uniformFamily_PBranchFam

/-!
# M6: branches of `P` (`cl:lem:P`(iii))

The paper's proof ("the germs `g_t = g_0 - ∫_{γ|[0,t]} Q` form a continuation, since near each `γ(t)` they are germs of a
local primitive of `-Q`") is paper 1's G13 machinery: the family `PBranchFam` (analytic, `-f' = Q` near the point) is
uniform on `U = {Re z > 0} ∖ Σ` (`uniformFamily_PBranchFam`: on a disc in `U`, a member differs from a fixed primitive of
`-Q` by a constant near its point, so it extends to the whole disc), and `ThmA.exists_continuationAlong_of_uniform`
continues every member along every path in `U`. Germs of branches of `P` are members (`pBranchFam_of_isPBranch`,
from M2's `neg_deriv_eventuallyEq_Qcont_of_isPBranch`), which is also the derivative clause. No RH.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M6

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-! ## Lemmas

Proved in `Fill/`, one file per lemma (same name, same statement): `isOpen_halfPlane_diff_poleSetQ`, `uniformFamily_PBranchFam`. -/

/-! ## Target -/

/-- `lem_P_iii` of `Paper2/Statements.lean`, statement verbatim. -/
theorem lem_P_iii_proof (hRH : RiemannHypothesis) :
    (∀ (g : ℂ → ℂ) (z₁ : ℂ), IsPBranch g z₁ → ∀ γ : C(unitInterval, ℂ),
      (∀ t, γ t ∈ halfPlane 0 \ PoleSetQ) → γ 0 = z₁ → ContinuesAlong g γ) ∧
    ∀ (g : ℂ → ℂ) (z₁ : ℂ), IsPBranch g z₁ → ∀ Qc : ℂ → ℂ, IsQCont Qc →
      ∀ᶠ z in 𝓝 z₁, HasDerivAt g (-Qc z) z := by
  have _ := hRH  -- RH is not used (choice 1 puts it on every Section 4 statement)
  refine ⟨fun g z₁ hg γ hγ h0 => ?_, fun g z₁ hg Qc hQc => ?_⟩
  · have hB : PBranchFam (γ 0) g := by rw [h0]; exact pBranchFam_of_isPBranch hg
    obtain ⟨f, hf, hf0, -⟩ := ThmA.exists_continuationAlong_of_uniform uniformFamily_PBranchFam hγ hB
    exact ⟨f, hf, hf0⟩
  · obtain ⟨han, hd⟩ := pBranchFam_of_isPBranch hg
    have hz₁ := (M2.neg_deriv_eventuallyEq_Qcont_of_isPBranch hg).1
    filter_upwards [han.eventually_analyticAt, hd, isOpen_halfPlane_diff_poleSetQ.mem_nhds hz₁]
      with z hza hzd hzU
    have h1 : Qc z = Qcont z := (M1.isQCont_eventuallyEq hQc).1 z hzU
    have h2 : deriv g z = -Qc z := by rw [h1, ← hzd]; ring
    exact h2 ▸ hza.differentiableAt.hasDerivAt

end GoldbachBoundaries.Paper2.M6
