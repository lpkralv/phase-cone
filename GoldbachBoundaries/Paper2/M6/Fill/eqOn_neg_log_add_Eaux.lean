import GoldbachBoundaries.Paper2.M6.Fill.OmegaP_inter_halfPlane_half
import GoldbachBoundaries.Paper2.M6.Fill.isOpen_isPreconnected_slitHalf

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
namespace GoldbachBoundaries.Paper2.M6
open GoldbachBoundaries GoldbachBoundaries.Paper2

theorem eqOn_neg_log_add_Eaux (hRH : RiemannHypothesis) {Pt : ℂ → ℂ} (hPt : DifferentiableOn ℂ Pt OmegaP)
    (hEq : EqOn Pt P (halfPlane 1)) :
    ∀ z ∈ OmegaP ∩ halfPlane (1 / 2), Pt z = -Complex.log (z - 1) + ThmA.Eaux z := by
  let V := halfPlane (1 / 2) \ {z | ∃ x : ℝ, 1 / 2 < x ∧ x ≤ 1 ∧ z = x}
  have hV : IsOpen V := isOpen_isPreconnected_slitHalf.1
  have hVc : IsPreconnected V := isOpen_isPreconnected_slitHalf.2
  have hVO : V ⊆ OmegaP := by
    dsimp [V]
    rw [← OmegaP_inter_halfPlane_half hRH]
    exact inter_subset_left
  have hlog : DifferentiableOn ℂ (fun z => Complex.log (z - 1)) V := by
    intro z hz
    have hslit : z - 1 ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      by_cases hi : z.im = 0
      · left
        have hr : 1 < z.re := by
          by_contra hn
          exact hz.2 ⟨z.re, hz.1, le_of_not_gt hn, by apply Complex.ext <;> simp [hi]⟩
        simpa using sub_pos.mpr hr
      · right; simpa using hi
    exact ((Complex.differentiableAt_log hslit).comp z
      (differentiableAt_id.sub_const 1)).differentiableWithinAt
  have ha : AnalyticOnNhd ℂ Pt V :=
    (hPt.mono hVO).analyticOnNhd hV
  have hb : AnalyticOnNhd ℂ (fun z => -Complex.log (z - 1) + ThmA.Eaux z) V :=
    ((hlog.analyticOnNhd hV).neg).add ((ThmA.Eaux_spec hRH).1.mono sdiff_subset)
  have h2 : (2 : ℂ) ∈ V := by
    refine ⟨by norm_num [halfPlane], ?_⟩
    rintro ⟨x, hx, hx1, heq⟩
    have := congrArg Complex.re heq
    norm_num at this; linarith
  have hevent : Pt =ᶠ[𝓝 (2 : ℂ)] (fun z => -Complex.log (z - 1) + ThmA.Eaux z) := by
    filter_upwards [(isOpen_halfPlane 1).mem_nhds (show (2 : ℂ) ∈ halfPlane 1 by norm_num [halfPlane])] with z hz
    rw [hEq hz, (ThmA.Eaux_spec hRH).2 z hz]
    ring
  have hid := ha.eqOn_of_preconnected_of_eventuallyEq hb hVc h2 hevent
  intro z hz
  apply hid
  change z ∈ halfPlane (1 / 2) \ {z | ∃ x : ℝ, 1 / 2 < x ∧ x ≤ 1 ∧ z = x}
  rwa [← OmegaP_inter_halfPlane_half hRH]

end GoldbachBoundaries.Paper2.M6
