import GoldbachBoundaries.Paper2.M3.Fill.CCommon

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
namespace GoldbachBoundaries.Paper2.M3
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **`Mform F` is analytic where `F` is `T`** (unconditional). Near `s` with `σ > 2`: `F = T` is analytic
(`T_differentiableOn` on the open half-plane, `DifferentiableOn.analyticAt`), `Γ` is analytic at `s` and `s - 1`
(`Complex.differentiableAt_Gamma`, real parts `> 0`), `Qcont` is analytic at `s - 1` (`Re > 1`, so `s - 1 ∉ Σ_Q`;
`M2.isQCont_Qcont`), `1/(s - 2)` is analytic (`s ≠ 2`), `E`, `e` are entire (`TIdentity.differentiable_E2`,
`differentiable_e1`). `AnalyticAt.congr` for `F`. Size: 60–120 lines. -/
theorem analyticAt_Mform_of_eq_T {F : ℂ → ℂ} {s : ℂ} (hs : 2 < s.re) (hF : F =ᶠ[𝓝 s] T) :
    AnalyticAt ℂ (Mform F) s := by
  have hT : AnalyticAt ℂ T s :=
    T_differentiableOn.analyticAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)
  have hFa : AnalyticAt ℂ F s := hT.congr hF.symm
  have hG0 : AnalyticAt ℂ Gamma s := cc_analyticAt_Gamma (by linarith)
  have hsub : AnalyticAt ℂ (fun z : ℂ => z - 1) s := by fun_prop
  have hG1 : AnalyticAt ℂ (fun z => Gamma (z - 1)) s :=
    AnalyticAt.comp (g := Gamma) (f := fun z : ℂ => z - 1)
      (cc_analyticAt_Gamma (z := s - 1) (by simp; linarith)) hsub
  have hQ : AnalyticAt ℂ (fun z => Qcont (z - 1)) s :=
    AnalyticAt.comp (g := Qcont) (f := fun z : ℂ => z - 1)
      (TIdentity.analyticAt_Qcont_of_one_lt (z := s - 1) (by simp; linarith)) hsub
  have hE : AnalyticAt ℂ Ecal s := by
    rw [Ecal_eq_E2]; exact TIdentity.differentiable_E2.analyticAt s
  have he : AnalyticAt ℂ (fun z => ecal (z - 1)) s :=
    AnalyticAt.comp (g := ecal) (f := fun z : ℂ => z - 1)
      (by rw [ecal_eq_e1]; exact TIdentity.differentiable_e1.analyticAt (s - 1)) hsub
  have hs2 : s - 2 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hinv : AnalyticAt ℂ (fun z : ℂ => 1 / (z - 2)) s := by
    fun_prop (disch := exact hs2)
  unfold Mform
  fun_prop

end GoldbachBoundaries.Paper2.M3
