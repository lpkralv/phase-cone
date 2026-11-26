import GoldbachBoundaries.Paper2.M3.Fill.CCommon

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
namespace GoldbachBoundaries.Paper2.M3
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **`Mform F` is meromorphic where `F` is** (unconditional). On `W ⊆ ℍ`: `Γ(s)`, `Γ(s - 1)` are analytic
(`Re s > 1`), `Qcont(s - 1)` is meromorphic (`meromorphicAt_Qcont` of paper 1 composed with `s ↦ s - 1`,
`MeromorphicAt.comp_analyticAt`), `1/(s - 2)` is meromorphic, `E`, `e` are entire; sums and products of meromorphic
functions are meromorphic. Size: 40–80 lines. -/
theorem meromorphicOn_Mform {F : ℂ → ℂ} {W : Set ℂ} (hF : MeromorphicOn F W) (hW : W ⊆ HH) :
    MeromorphicOn (Mform F) W := by
  intro s hs
  have hs1 : 1 < s.re := hW hs
  have hG0 : MeromorphicAt Gamma s := (cc_analyticAt_Gamma (by linarith)).meromorphicAt
  have hsub : AnalyticAt ℂ (fun z : ℂ => z - 1) s := by fun_prop
  have hG1 : MeromorphicAt (fun z => Gamma (z - 1)) s :=
    MeromorphicAt.comp_analyticAt (f := Gamma) (g := fun z : ℂ => z - 1)
      (cc_analyticAt_Gamma (z := s - 1) (by simp; linarith)).meromorphicAt hsub
  have hQ : MeromorphicAt (fun z => Qcont (z - 1)) s :=
    MeromorphicAt.comp_analyticAt (f := Qcont) (g := fun z : ℂ => z - 1)
      (meromorphicAt_Qcont (a := s - 1) (by simp; linarith)) hsub
  have hE : MeromorphicAt Ecal s := by
    rw [Ecal_eq_E2]; exact (TIdentity.differentiable_E2.analyticAt s).meromorphicAt
  have he : MeromorphicAt (fun z => ecal (z - 1)) s :=
    MeromorphicAt.comp_analyticAt (f := ecal) (g := fun z : ℂ => z - 1)
      (by rw [ecal_eq_e1]; exact (TIdentity.differentiable_e1.analyticAt (s - 1)).meromorphicAt) hsub
  have hinv : MeromorphicAt (fun z : ℂ => 1 / (z - 2)) s := by fun_prop
  have hFs := hF s hs
  unfold Mform
  fun_prop

end GoldbachBoundaries.Paper2.M3
