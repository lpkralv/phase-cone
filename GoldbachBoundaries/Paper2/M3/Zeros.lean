import GoldbachBoundaries.Paper2.M3.Defs
import GoldbachBoundaries.Paper2.M3.Fill.Rcoef_of_half_le_re
import GoldbachBoundaries.Paper2.M3.Fill.mem_nontrivialZeros_of_zeta_eq_zero

/-!
# M3: Mathlib's RH and the zeros in the strip; `R_ρ` at a zero with `β ≥ 1/2`

Mathlib's `RiemannHypothesis` speaks of every zero of `ζ` other than the trivial zeros `-2(n+1)` and the point `1`;
the paper's RH, and `NontrivialZeros`, speak of the zeros in the strip `0 < β < 1`. They agree because every zero that
is not trivial lies in the strip (`riemannZeta_ne_zero_of_one_le_re` on `σ ≥ 1`, the functional equation on
`σ ≤ 0`). `thm_test`, `cor_test` (direction `←`) conclude Mathlib's RH, and `rem_dichotomy_ii` assumes its negation;
both go through `riemannHypothesis_iff` below.

`Rcoef_of_half_le_re` (proved in `Fill/Rcoef_of_half_le_re.lean`) is the computation `R_ρ = -m(ρ)` that the paper uses in Step 4 of `nr:thm:test`,
in `nr:rem:classical`(ii) and (with `β = B`) in the proof of `nr:thm:real`(b).
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M3

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-! ## Real lemmas -/

/-- Mathlib's RH is the statement that every zero in the strip has real part `1/2`. -/
theorem riemannHypothesis_iff : RiemannHypothesis ↔ ∀ ρ ∈ NontrivialZeros, ρ.re = 1 / 2 := by
  refine ⟨fun hRH ρ hρ => re_eq_half_of_mem_nontrivialZeros hRH hρ, fun h s hs htriv h1 => ?_⟩
  exact h s (mem_nontrivialZeros_of_zeta_eq_zero hs htriv h1)

/-- If RH fails, some zero has `β > 1/2` ((Z1): reflect a zero with `β < 1/2` to `1 - ρ̄`). -/
theorem exists_re_gt_half_of_not_RH (hZ1 : Z1) (hRH : ¬ RiemannHypothesis) :
    ∃ ρ ∈ NontrivialZeros, 1 / 2 < ρ.re := by
  rw [riemannHypothesis_iff] at hRH
  push Not at hRH
  obtain ⟨ρ, hρ, hne⟩ := hRH
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · refine ⟨1 - conj ρ, ((hZ1 ρ hρ).2).1, ?_⟩
    simp only [sub_re, one_re, conj_re]
    linarith
  · exact ⟨ρ, hρ, hgt⟩

/-- If RH fails, `B > 1/2` ((Z1)). -/
theorem half_lt_Bsup_of_not_RH (hZ1 : Z1) (hRH : ¬ RiemannHypothesis) : 1 / 2 < Bsup := by
  obtain ⟨ρ, hρ, hgt⟩ := exists_re_gt_half_of_not_RH hZ1 hRH
  exact lt_of_lt_of_le hgt ((Bsup_facts hZ1).1 ρ hρ)

end GoldbachBoundaries.Paper2.M3
