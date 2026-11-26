import GoldbachBoundaries.Paper2.M6.Fill.BCommon

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M6

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **The holomorphic part `E_a` of `P` at `a ∈ Σ`** (RH). With `q` from paper 1's `ThmA.Qcont_pole_split` and
`sigmaRes a = Rcoef a` (M1's `hasResidue_Qcont_Rcoef`): the ball lies in `{Re z > 0} ∖ (Σ ∖ {a})`, where `q` is
analytic, so `-q` has a primitive `E` on the ball (`DifferentiableOn.isExactOn_ball`); off `a` the ball misses `Σ`,
so `-q z = -Qcont z + Rcoef a/(z - a)`. -/
theorem exists_E_pole (hRH : RiemannHypothesis) {a : ℂ} (ha : a ∈ PoleSetQ) {R : ℝ}
    (hΔ : ball a R ⊆ halfPlane 0) (hΔS : ball a R ∩ PoleSetQ = {a}) :
    ∃ E : ℂ → ℂ, DifferentiableOn ℂ E (ball a R) ∧
      ∀ z ∈ ball a R, z ≠ a → HasDerivAt E (-Qcont z + Rcoef a / (z - a)) z := by
  obtain ⟨q, hq, hsplit⟩ := ThmA.Qcont_pole_split hRH ha
  have hres : sigmaRes a = Rcoef a := sigmaRes_eq (M1.hasResidue_Qcont_Rcoef ha)
  have hnot : ∀ z ∈ ball a R, z ≠ a → z ∉ PoleSetQ := fun z hz hza hzS => by
    have : z ∈ ball a R ∩ PoleSetQ := ⟨hz, hzS⟩
    rw [hΔS] at this
    exact hza this
  have hsub : ball a R ⊆ halfPlane 0 \ (PoleSetQ \ {a}) := fun z hz => by
    refine ⟨hΔ hz, fun ⟨hzS, hza⟩ => hnot z hz hza hzS⟩
  obtain ⟨Ψ, hΨ⟩ := B_exists_primitive_ball (c := a) (r := R) (g := fun z => -q z)
    fun z hz => (hq z (hsub hz)).differentiableAt.neg.differentiableWithinAt
  refine ⟨Ψ, fun z hz => (hΨ z hz).differentiableAt.differentiableWithinAt, fun z hz hza => ?_⟩
  have hQ := hsplit z (hΔ hz) (hnot z hz hza)
  rw [hres] at hQ
  convert hΨ z hz using 1
  rw [hQ]; ring

end GoldbachBoundaries.Paper2.M6
