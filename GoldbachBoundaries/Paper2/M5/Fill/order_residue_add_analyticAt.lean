import GoldbachBoundaries.Paper2.M5.Defs

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics
namespace GoldbachBoundaries.Paper2.M5
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

theorem order_residue_add_analyticAt {f h u : ℂ → ℂ} {α c : ℂ} (hfe : f =ᶠ[𝓝[≠] α] fun s => h s + u s)
    (hh : AnalyticAt ℂ h α) (hu : MeromorphicAt u α) (hord : -1 ≤ meromorphicOrderAt u α)
    (hres : HasResidue u α c) :
    MeromorphicAt f α ∧ -1 ≤ meromorphicOrderAt f α ∧ HasResidue f α c ∧
      (meromorphicOrderAt f α < 0 ↔ meromorphicOrderAt u α < 0) := by
  have he : meromorphicOrderAt f α = meromorphicOrderAt (h + u) α :=
    meromorphicOrderAt_congr hfe
  have hmin : min (meromorphicOrderAt h α) (meromorphicOrderAt u α) ≤
      meromorphicOrderAt (h + u) α := meromorphicOrderAt_add hh.meromorphicAt hu
  have hnonneg := hh.meromorphicOrderAt_nonneg
  refine ⟨(hh.meromorphicAt.add hu).congr hfe.symm, ?_, ?_, ?_⟩
  · rw [he]
    exact (le_min (by exact le_trans (show (-1 : WithTop ℤ) ≤ 0 from by decide) hnonneg) hord).trans hmin
  · have hz : Tendsto (fun s : ℂ => (s - α) * h s) (𝓝[≠] α) (𝓝 0) := by
      have hsub : Tendsto (fun s : ℂ => s - α) (𝓝 α) (𝓝 (α - α)) :=
        tendsto_id.sub tendsto_const_nhds
      simpa using (hsub.mul hh.continuousAt.tendsto).mono_left nhdsWithin_le_nhds
    have hadd := hz.add hres
    simp only [zero_add] at hadd
    apply hadd.congr'
    filter_upwards [hfe] with s hs
    simp only [hs, mul_add]
  · rw [he]
    constructor
    · intro hneg
      by_contra hu0
      have := (le_min hnonneg (le_of_not_gt hu0)).trans hmin
      exact (not_lt_of_ge this) hneg
    · intro hneg
      rw [meromorphicOrderAt_add_eq_right_of_lt hh.meromorphicAt (hneg.trans_le hnonneg)]
      exact hneg

end GoldbachBoundaries.Paper2.M5
