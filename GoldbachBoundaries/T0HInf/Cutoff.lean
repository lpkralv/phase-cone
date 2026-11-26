import GoldbachBoundaries.T0HInf.Defs

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
namespace GoldbachBoundaries.T0HInf
open GoldbachBoundaries Paper2
open _root_.GoldbachBoundaries.Phi2HInf (StirlingStrip)

theorem cutoff_bounds (hH : Hinf) :
    Bsup / 2 < remainderAbscissa ∧ 1 / 3 < remainderAbscissa ∧ remainderAbscissa < 1 / 2 ∧
      1 / 2 < cutoffAbscissa ∧ crossingAbscissa < 1 := by
  have hB : Bsup < 1 := lem_B_iii hH
  have hm : max (Bsup / 2) (1 / 3 : ℝ) < 1 / 2 :=
    max_lt (by linarith) (by norm_num)
  have hmB := le_max_left (Bsup / 2) (1 / 3 : ℝ)
  have hm3 := le_max_right (Bsup / 2) (1 / 3 : ℝ)
  have ha : remainderAbscissa < 1 / 2 := by unfold remainderAbscissa; linarith
  refine ⟨?_, ?_, ha, ?_, ?_⟩
  · unfold remainderAbscissa; linarith
  · unfold remainderAbscissa; linarith
  · unfold cutoffAbscissa; linarith
  · unfold crossingAbscissa cutoffAbscissa
    exact max_lt hB (by linarith)

theorem exists_cutoff (hH : Hinf) : ∃ E : Finset NontrivialZeros, IsCutoff E := by
  classical
  have hb : 1 / 2 < cutoffAbscissa := (cutoff_bounds hH).2.2.2.1
  have hfin : {ρ : NontrivialZeros | cutoffAbscissa < (ρ : ℂ).re}.Finite := by
    refine ((hH (cutoffAbscissa - 1 / 2) (by linarith)).preimage
      Subtype.val_injective.injOn).subset ?_
    intro ρ hρ
    exact ⟨ρ.2, by change cutoffAbscissa < (ρ : ℂ).re at hρ; linarith⟩
  exact ⟨hfin.toFinset, fun ρ => hfin.mem_toFinset⟩

end GoldbachBoundaries.T0HInf
