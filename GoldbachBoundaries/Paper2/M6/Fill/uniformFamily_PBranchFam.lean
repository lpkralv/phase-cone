import GoldbachBoundaries.Paper2.M6.Fill.isOpen_halfPlane_diff_poleSetQ
import GoldbachBoundaries.Paper2.M6.Fill.BCommon

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M6

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **The branches of `P` form a uniform family on `{Re z > 0} ∖ Σ`** (unconditional; paper 1's `ThmA.UniformFamily`).
For `p ∈ U` take `ball p r ⊆ U` and a primitive `Φ` of `Qcont` on it. A member `f` at `q ∈ ball p r` has
`f' = -Qcont = (-Φ)'` near `q`, so `f = -Φ + C` near `q`; `F = -Φ + C` is analytic on the ball and in the family at
every point of it. -/
theorem uniformFamily_PBranchFam : ThmA.UniformFamily PBranchFam (halfPlane 0 \ PoleSetQ) := by
  intro p hp
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp isOpen_halfPlane_diff_poleSetQ p hp
  have hQan : AnalyticOnNhd ℂ Qcont (halfPlane 0 \ PoleSetQ) := M2.isQCont_Qcont.2.2
  obtain ⟨Φ, hΦ⟩ := B_exists_primitive_ball (c := p) (r := r) (g := Qcont)
    fun z hz => (hQan z (hrU hz)).differentiableAt.differentiableWithinAt
  refine ⟨r, hr, fun q hq f hf => ?_⟩
  obtain ⟨hfa, hfd⟩ := hf
  obtain ⟨C, hC⟩ := B_eventuallyEq_add_const (f := f) (g := fun z => -Φ z) (φ := fun z => -Qcont z)
    (z₁ := q) (by
      filter_upwards [hfa.eventually_analyticAt, hfd, isOpen_ball.mem_nhds hq] with z hza hzd hzb
      refine ⟨?_, (hΦ z hzb).neg⟩
      have h2 : deriv f z = -Qcont z := by rw [← hzd]; ring
      exact h2 ▸ hza.differentiableAt.hasDerivAt)
  have hFd : ∀ z ∈ ball p r, HasDerivAt (fun z => -Φ z + C) (-Qcont z) z := fun z hz =>
    ((hΦ z hz).neg).add_const C
  have hFdo : DifferentiableOn ℂ (fun z => -Φ z + C) (ball p r) := fun z hz =>
    (hFd z hz).differentiableAt.differentiableWithinAt
  have hFan : AnalyticOnNhd ℂ (fun z => -Φ z + C) (ball p r) := hFdo.analyticOnNhd isOpen_ball
  refine ⟨fun z => -Φ z + C, hFan, hC.symm, fun q' hq' => ⟨hFan q' hq', ?_⟩⟩
  filter_upwards [isOpen_ball.mem_nhds hq'] with z hz
  rw [(hFd z hz).deriv, neg_neg]

end GoldbachBoundaries.Paper2.M6
