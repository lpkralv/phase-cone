import GoldbachBoundaries.Paper2.M6.Defs

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M6

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- The straight path (helper for `isAdmissibleGermOn_eventually`) `t ↦ s + t(s' - s)`. -/
def exG_segPath (s s' : ℂ) : C(unitInterval, ℂ) :=
  ⟨fun t => s + ((t : ℝ) : ℂ) * (s' - s), by fun_prop⟩

lemma exG_segPath_mem_ball {s s' : ℂ} {ε : ℝ} (hs' : s' ∈ ball s ε) (t : unitInterval) :
    exG_segPath s s' t ∈ ball s ε := by
  have hε : 0 < ε := lt_of_le_of_lt dist_nonneg hs'
  simp only [exG_segPath, ContinuousMap.coe_mk, mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul,
    Complex.norm_real, Real.norm_eq_abs] at hs' ⊢
  rw [← dist_eq_norm] at hs' ⊢
  have h0 := t.2.1
  have h1 := t.2.2
  rw [abs_of_nonneg h0]
  calc (t : ℝ) * dist s' s ≤ 1 * dist s' s := by gcongr
    _ < ε := by simpa using hs'

/-- **Admissibility spreads to nearby points** (`Ω` open). Append to the path the straight segment from `s` to a
point `s'` of a small ball around `s` on which `g` is analytic and which lies in `Ω` (paper 1's
`ThmA.isTerminalGerm_of_analyticAt`, `ThmA.isTerminalGerm_trans_proof`). -/
theorem isAdmissibleGermOn_eventually {F : ℂ → ℂ} {Ω S : Set ℂ} (hΩ : IsOpen Ω) {g : ℂ → ℂ} {s : ℂ}
    (h : IsAdmissibleGermOn F Ω S g s) : ∀ᶠ s' in 𝓝 s, IsAdmissibleGermOn F Ω S g s' := by
  have hg := analyticAt_of_isAdmissibleGermOn h
  have hs := mem_of_isAdmissibleGermOn h
  obtain ⟨γ, hγΩ, hγS, hγ1, hT⟩ := h
  have hev : ∀ᶠ z in 𝓝 s, AnalyticAt ℂ g z ∧ z ∈ Ω :=
    hg.eventually_analyticAt.and (hΩ.mem_nhds hs)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  rw [Metric.eventually_nhds_iff_ball]
  refine ⟨ε, hε, fun s' hs' => ?_⟩
  have hδ : ∀ t, exG_segPath s s' t ∈ ball s ε := exG_segPath_mem_ball hs'
  have hδ0 : exG_segPath s s' 0 = γ 1 := by simp [exG_segPath, hγ1]
  have hδ1 : exG_segPath s s' 1 = s' := by simp [exG_segPath]
  have hT2 : IsTerminalGerm g (exG_segPath s s' ) g :=
    ThmA.isTerminalGerm_of_analyticAt (fun t => (hball _ (hδ t)).1) EventuallyEq.rfl
  obtain ⟨γ', h0, h1, hrange, hT'⟩ := ThmA.isTerminalGerm_trans_proof hT hδ0 hT2
  refine ⟨γ', fun t => ?_, h0 ▸ hγS, h1.trans hδ1, hT'⟩
  rcases hrange t with ⟨u, hu⟩ | ⟨u, hu⟩
  · rw [← hu]; exact hγΩ u
  · rw [← hu]; exact (hball _ (hδ u)).2

end GoldbachBoundaries.Paper2.M6
