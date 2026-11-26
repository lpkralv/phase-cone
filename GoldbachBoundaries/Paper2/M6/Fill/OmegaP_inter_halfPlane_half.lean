import GoldbachBoundaries.Paper2.M6.Defs

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
namespace GoldbachBoundaries.Paper2.M6
open GoldbachBoundaries GoldbachBoundaries.Paper2

theorem OmegaP_inter_halfPlane_half (hRH : RiemannHypothesis) :
    OmegaP ∩ halfPlane (1 / 2) = halfPlane (1 / 2) \ {z | ∃ x : ℝ, 1 / 2 < x ∧ x ≤ 1 ∧ z = x} := by
  have h1 : (1 : ℂ) ∈ PoleSetQ := by
    have h : (1 : ℂ) ∈ PoleSetQ ∩ halfPlane (1 / 2) := by
      rw [(lem_Sigma_iv_proof hRH).1]; simp
    exact h.1
  ext z
  constructor
  · rintro ⟨hz, hzhalf⟩
    refine ⟨hzhalf, ?_⟩
    rintro ⟨x, hx, hx1, rfl⟩
    apply hz.2
    simp only [mem_iUnion]
    exact ⟨1, h1, 1 - x, by linarith, by push_cast; ring⟩
  · rintro ⟨hzhalf, hzcut⟩
    refine ⟨⟨by change 0 < z.re; change 1 / 2 < z.re at hzhalf; linarith, ?_⟩, hzhalf⟩
    simp only [mem_iUnion]
    rintro ⟨a, ha, t, ht, heq⟩
    have hre : a ∈ halfPlane (1 / 2) := by
      change 1 / 2 < a.re
      change 1 / 2 < z.re at hzhalf
      rw [heq, sub_re, ofReal_re] at hzhalf
      linarith
    have ha1 : a = 1 := by
      have : a ∈ PoleSetQ ∩ halfPlane (1 / 2) := ⟨ha, hre⟩
      rwa [(lem_Sigma_iv_proof hRH).1, mem_singleton_iff] at this
    subst a
    apply hzcut
    refine ⟨1 - t, ?_, by linarith, ?_⟩
    · change 1 / 2 < z.re at hzhalf
      simpa [heq] using hzhalf
    · simpa using heq

end GoldbachBoundaries.Paper2.M6
