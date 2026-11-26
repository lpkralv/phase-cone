import GoldbachBoundaries.Paper2.M4a.Fill.BCommon

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
open scoped Interval
namespace GoldbachBoundaries.Paper2.M4a
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **`J'_{ab}` at a point `α` with `L(α) = a + b`** ((K1)). Write `J_{ab}(s) = (L(s) - a - b) I(s)` with
`I(s) = ∫_0^1 k(a + t(L(s) - a - b), s) dt`. `I` is differentiable at `α` (the proof of `differentiableOn_Jseg` with
`U = D_L`, or `differentiableOn_Jseg` itself and `J = (L - a - b)·I` off the zero set; simplest: rerun the
`ThmA.differentiableOn_intervalIntegral_of_continuousOn` step for `I`), and `L(s) - a - b` has derivative `ℓ` and value
`0` at `α`; the product rule gives `ℓ I(α) = ℓ ∫_0^1 k(a, α) dt = ℓ k(a, α)`. Size: 60–120 lines. -/
theorem hasDerivAt_Jseg_of_app_eq (A : Aff) (k : ℂ → ℂ → ℂ) (hK1 : K1 A k) {a b : ℂ} (ha : a ∈ PoleSetQ)
    (hb : b ∈ PoleSetQ) {α : ℂ} (hα : α ∈ A.DL) (h : A.app α = a + b) :
    HasDerivAt (Jseg A k a b) ((A.ell : ℂ) * k a α) α := by
  have hI := (GroupB.differentiableOn_integral A k (isOpen_DL A) (DL_subset_HL A) hK1 ha hb).differentiableAt ((isOpen_DL A).mem_nhds hα)
  have hL : HasDerivAt (fun s => A.app s - a - b) (A.ell : ℂ) α := by
    simpa [Aff.app] using ((((hasDerivAt_id α).const_mul (A.ell : ℂ)).add_const
      (A.ell0 : ℂ)).sub_const a).sub_const b
  change HasDerivAt (fun s => (A.app s - a - b) *
    ∫ t in (0 : ℝ)..1, k (a + (t : ℂ) * (A.app s - a - b)) s) _ α
  simpa [h, smul_eq_mul] using hL.fun_smul hI.hasDerivAt

end GoldbachBoundaries.Paper2.M4a
