import GoldbachBoundaries.Paper2.M1.BNumbers
import GoldbachBoundaries.Paper2.M1.Fill.BCommon
import GoldbachBoundaries.Paper2.M1.Fill.finite_zeros_re_gt
/-! Filler group B: `Bsup_attained` (`BNumbers.lean`). -/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M1

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- If `B > B_∞`: `B < 1`, and `β = B` for finitely many zeros, at least one (`B` is the maximum of `β` over the
finitely many zeros with `β > B_∞ + δ`, `δ = (B - B_∞)/2`). Uses: `finite_zeros_re_gt`. Size: 100–200 lines. -/
theorem Bsup_attained (h : Binf < Bsup) :
    Bsup < 1 ∧ {ρ | ρ ∈ NontrivialZeros ∧ ρ.re = Bsup}.Finite ∧
      {ρ | ρ ∈ NontrivialZeros ∧ ρ.re = Bsup}.Nonempty := by
  set δ := (Bsup - Binf) / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hδB : Binf + δ < Bsup := by rw [hδdef]; linarith
  set S := {ρ | ρ ∈ NontrivialZeros ∧ Binf + δ < ρ.re} with hSdef
  have hS : S.Finite := finite_zeros_re_gt δ hδ
  have hZne : (re '' NontrivialZeros).Nonempty := image_nonempty.2 nontrivialZeros_nonempty
  have hne : (re '' S).Nonempty := by
    obtain ⟨_, ⟨ρ, hρ, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup hZne hδB
    exact ⟨ρ.re, ρ, ⟨hρ, hlt⟩, rfl⟩
  obtain ⟨ρ₀, hρ₀, hρ₀e⟩ := hne.csSup_mem (hS.image _)
  have hBeq : Bsup = ρ₀.re := by
    refine le_antisymm (csSup_le hZne ?_) (re_le_Bsup hρ₀.1)
    rintro _ ⟨ρ, hρ, rfl⟩
    by_cases hr : Binf + δ < ρ.re
    · rw [hρ₀e]
      exact le_csSup (hS.image _).bddAbove ⟨ρ, ⟨hρ, hr⟩, rfl⟩
    · push Not at hr
      linarith [hρ₀.2]
  refine ⟨?_, hS.subset ?_, ⟨ρ₀, hρ₀.1, hBeq.symm⟩⟩
  · rw [hBeq]; exact hρ₀.1.2.2
  · rintro ρ ⟨hρ, hr⟩
    exact ⟨hρ, by rw [hr]; exact hδB⟩

end GoldbachBoundaries.Paper2.M1
