import GoldbachBoundaries.Paper2.M3.Test
import GoldbachBoundaries.Paper2.M3.Fill.hasResidue_Mform_Tcont_two_Bsup
import GoldbachBoundaries.Paper2.M3.Fill.order_Mform_Tcont_nonneg

/-!
# M3: the abscissa of `𝓜` (`nr:rem:classical` (ii), (iii))

(ii) `σ_c ≥ 2B` unconditionally ((Z1)): every `x ∈ mellinConvSet` bounds the zeros with `β ≥ 1/2` by `x/2`
(`re_le_of_mem_mellinConvSet`), and with (Z1) every zero (a zero with `β < 1/2` reflects to `1 - ρ̄`); so `B ≤ x/2`.

(iii) Under `B > B_∞`: `Mform Tcont` (the right side of `(nr:eq:hsq)` with M1's `Tcont` for `T`) is meromorphic on
`σ > 2B_∞`, equal to `𝓜` on `σ > 2`, regular at every real point of `(2B, 2]` (`order_Mform_Tcont_nonneg`: the real
pinch points above `2B` are `2` and the `1 + 1/k`, cancelled as in Step 1 of `nr:thm:test`), with residue `Γ(2B)A` at
`2B` (`hasResidue_Mform_Tcont_two_Bsup`: `Γ(2B)𝓡(2B) = Γ(2B)(A + [2B = 1 + 1/k]2μ(k))`, and `2Γ(s-1)Q(s-1)` removes the
bracket). Landau (`mem_mellinConvSet_of_differentiableOn_balls` with `a = 2B`) gives `σ_c ≤ 2B`. The target
`rem_classical_iii_proof` is in `Skeleton.lean`; `rem_classical_ii_proof` is at the end of this file.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M3

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1 GoldbachBoundaries.Paper2.M2

/-! ## Real lemmas -/

/-- `nr:rem:classical`(ii) in junk-free form ((Z1)): every point of `mellinConvSet` is `≥ 2B`. -/
theorem two_Bsup_le_of_mem (hZ1 : Z1) {x : ℝ} (hx : x ∈ mellinConvSet) : 2 * Bsup ≤ x := by
  have hb : ∀ ρ ∈ NontrivialZeros, ρ.re ≤ x / 2 := by
    intro ρ hρ
    by_cases h : 1 / 2 ≤ ρ.re
    · exact re_le_of_mem_mellinConvSet hx hρ h
    · push Not at h
      have h' := re_le_of_mem_mellinConvSet hx ((hZ1 ρ hρ).2.1) (by simp; linarith)
      simp at h'
      linarith
  have hne : (re '' NontrivialZeros).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have := (Bsup_facts hZ1).2.1
    rw [Bsup, hemp, Real.sSup_empty] at this
    norm_num at this
  have : Bsup ≤ x / 2 := csSup_le hne (by rintro _ ⟨ρ, hρ, rfl⟩; exact hb ρ hρ)
  linarith

/-! ## Target: `rem_classical_ii` -/

/-- `rem_classical_ii` of `Paper2/Statements.lean`, statement verbatim. -/
theorem rem_classical_ii_proof (hZ1 : Z1) :
    (∀ x : ℝ, 2 < x → x ∈ mellinConvSet) ∧ (∀ x ∈ mellinConvSet, 2 * Bsup ≤ x) ∧
      BddBelow mellinConvSet ∧ 2 * Bsup ≤ sigmaC := by
  have h1 : ∀ x : ℝ, 2 < x → x ∈ mellinConvSet := fun x hx => mem_mellinConvSet_of_two_lt hx
  have h2 : ∀ x ∈ mellinConvSet, 2 * Bsup ≤ x := fun x hx => two_Bsup_le_of_mem hZ1 hx
  exact ⟨h1, h2, ⟨2 * Bsup, h2⟩, le_csInf ⟨3, h1 3 (by norm_num)⟩ h2⟩

end GoldbachBoundaries.Paper2.M3
