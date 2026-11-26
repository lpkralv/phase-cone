import GoldbachBoundaries.Paper2.M3.Real

/-!
# `Mcal_eq_formula`: `(nr:eq:hsq)` for `σ > 2`

A real lemma of `Hsq.lean`, moved here so that `Fill/tendsto_sub_two_mul_Gamma_T.lean` can use it without importing
`Hsq.lean` (which imports that fill file). Statement and proof unchanged.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M3

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- `(nr:eq:hsq)` for `σ > 2`, from paper 1's two splitting identities. -/
theorem Mcal_eq_formula {s : ℂ} (hs : 2 < s.re) :
    Mcal s = Gamma s * T s - 2 * Gamma (s - 1) * Q (s - 1) + 1 / (s - 2) - Ecal s + 2 * ecal (s - 1) := by
  have h1 := TIdentity.Gamma_mul_T_eq_split hs
  have h2 := TIdentity.Gamma_mul_Q_eq_split (z := s - 1) (by simp; linarith)
  rw [show s - 1 - 1 = s - 2 by ring] at h2
  rw [Mcal_eq_Rr, Ecal_eq_E2, ecal_eq_e1, mul_assoc 2, h1, h2]
  ring

end GoldbachBoundaries.Paper2.M3
