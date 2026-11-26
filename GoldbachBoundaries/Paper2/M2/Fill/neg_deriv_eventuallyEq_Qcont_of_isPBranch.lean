import GoldbachBoundaries.Paper2.M2.Single
import GoldbachBoundaries.ThmA.Fill.germ_unique

/-!
# Filler (Group D): `neg_deriv_eventuallyEq_Qcont_of_isPBranch`

Unfold `IsPBranch`: a path `γ` in `{Re z > 0} ∖ Σ_Q` from `{Re z > 1}` to `z₁` and a continuation `f` of `P` along it.
`t ↦ -deriv (f t)` is a continuation along `γ` starting with `-P' = Q = Qcont` near `γ 0`; the constant family
`t ↦ Qcont` is another (`Qcont` is analytic on `{Re z > 0} ∖ Σ_Q`). Paper 1's `ThmA.germ_unique` makes their germs
at `γ 1 = z₁` equal.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M2

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **Germs of branches of `P` differentiate to `Qcont`** (unconditional). Unfold `IsPBranch`: a path `γ` in
`{Re z > 0} ∖ Σ_Q` from `γ 0 ∈ {Re z > 1}` to `z₁` and a continuation `f` along `γ` with `f 0 = P` near `γ 0` and
`g = f 1` near `z₁`. Then `t ↦ -deriv (f t)` is a continuation along `γ` (`AnalyticAt.deriv`,
`Filter.EventuallyEq.deriv`), starting with `-deriv P = Q = Qcont` near `γ 0` (paper 1's `hasDerivAt_P`,
`Qcont_eq_Q_of_one_lt`, on the open half-plane). The constant family `t ↦ Qcont` is a continuation along `γ` because
`Qcont` is analytic on `{Re z > 0} ∖ Σ_Q` (`isQCont_Qcont`). Paper 1's `ThmA.germ_unique` gives
`-deriv (f 1) = Qcont` near `z₁`, and `-deriv g = -deriv (f 1)` near `z₁`. Size: 150–250 lines. -/
theorem neg_deriv_eventuallyEq_Qcont_of_isPBranch {g : ℂ → ℂ} {z₁ : ℂ} (hg : IsPBranch g z₁) :
    z₁ ∈ halfPlane 0 \ PoleSetQ ∧ (fun z => -deriv g z) =ᶠ[𝓝 z₁] Qcont := by
  obtain ⟨γ, hγ, hγ0, hγ1, f, hf, hf0, hg1⟩ := hg
  subst hγ1
  refine ⟨hγ 1, ?_⟩
  -- the differentiated family
  have hF : IsContinuationAlong γ (fun t z => -deriv (f t) z) := by
    refine ⟨fun t => (hf.analyticAt t).deriv.neg, fun t => ?_⟩
    filter_upwards [hf.locallyEq t] with t' ht'
    filter_upwards [ht'.deriv] with z hz
    simp only [hz]
  -- the constant family `Qcont`
  have hC : IsContinuationAlong γ (fun _ => Qcont) :=
    ⟨fun t => isQCont_Qcont.2.2 _ (hγ t), fun t => Filter.Eventually.of_forall fun _ => EventuallyEq.rfl⟩
  -- initial germs agree
  have hn0 : halfPlane 1 ∈ 𝓝 (γ 0) := (isOpen_halfPlane 1).mem_nhds hγ0
  have h0 : (fun z => -deriv (f 0) z) =ᶠ[𝓝 (γ 0)] Qcont := by
    filter_upwards [hf0.deriv, hn0] with z hz hzH
    rw [hz, (hasDerivAt_P hzH).deriv, neg_neg]
    exact (isQCont_Qcont.2.1 hzH).symm
  have h1 := ThmA.germ_unique hF hC h0 1
  filter_upwards [hg1.deriv, h1] with z hz hz'
  rw [hz]
  exact hz'

end GoldbachBoundaries.Paper2.M2
