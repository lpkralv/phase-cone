import GoldbachBoundaries.Paper2.M4b.Fill.C2Common

/-! Filler for `mero_mul_Qcont_app` (M4b, group C2). -/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M4b

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **The poles of `g(s)Q(L(s) - 1)`** (general, no RH). At `α` with `L(α) - 1 = b ∈ Σ_Q`, `Qcont` has order `≥ -1`
and residue `R_b` at `b` (M1's `meromorphicOrderAt_Qcont_ge`, `hasResidue_Qcont_Rcoef`). The affine map
`s ↦ L(s) - 1 = ℓ(s - α) + b` has derivative `ℓ ≠ 0`, so `s ↦ Qcont(L(s) - 1)` has order `≥ -1` at `α` and residue
`R_b/ℓ` (`(s - α)Qcont(ℓ(s - α) + b) = ℓ⁻¹(w - b)Qcont(w)`, `w → b`). Multiplying by `g` analytic at `α`: order
`≥ -1`, residue `g(α)R_b/ℓ` (`Tendsto.mul` with `g` continuous). Order `< 0` iff the residue is non-zero: an order
`≥ 0` gives residue `0` (`(s - α)f(s) → 0`); order `-1` gives a non-zero residue (the leading coefficient of
`MeromorphicAt.order_eq_int_iff`). Size: 150–250 lines. -/
theorem mero_mul_Qcont_app (A : Aff) {g : ℂ → ℂ} {α b : ℂ} (hg : AnalyticAt ℂ g α) (hb : b ∈ PoleSetQ)
    (hα : A.app α = 1 + b) :
    -1 ≤ meromorphicOrderAt (fun s => g s * Qcont (A.app s - 1)) α ∧
      HasResidue (fun s => g s * Qcont (A.app s - 1)) α (g α * Rcoef b / A.ell) ∧
      (meromorphicOrderAt (fun s => g s * Qcont (A.app s - 1)) α < 0 ↔ g α * Rcoef b ≠ 0) := by
  obtain ⟨hm, hr⟩ := FillC2.Qcont_app_facts A hb hα
  have hm' : MeromorphicAt (fun s => g s * Qcont (A.app s - 1)) α := hg.meromorphicAt.mul hm
  have hr' : HasResidue (fun s => g s * Qcont (A.app s - 1)) α (g α * Rcoef b / A.ell) := by
    rw [mul_div_assoc]; exact FillC2.hasResidue_mul_left hr hg.continuousAt
  have hl : (A.ell : ℂ) ≠ 0 := by exact_mod_cast A.ell_pos.ne'
  refine ⟨hr'.neg_one_le_meromorphicOrderAt hm', hr', ?_⟩
  rw [FillC2.order_neg_iff_of_hasResidue hm' hr']
  exact ⟨fun h h0 => h (by rw [h0, zero_div]), fun h => div_ne_zero h hl⟩

end GoldbachBoundaries.Paper2.M4b
