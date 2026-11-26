import GoldbachBoundaries.Paper2.M6.Defs

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M6

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **`P(z̄) = conj P(z)`** (unconditional, every `z`). `(p : ℂ)^(-conj z) = conj ((p : ℂ)^(-z))` for the positive real
`p` (`Complex.cpow_conj`, `arg p = 0 ≠ π`), then `Complex.conj_tsum` (no summability needed). -/
theorem P_conj (z : ℂ) : P (conj z) = conj (P z) := by
  unfold P
  rw [Complex.conj_tsum]
  congr 1
  funext p
  have harg : ((p : ℕ) : ℂ).arg ≠ Real.pi := by
    rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm
  rw [show -conj z = conj (-z) by simp, Complex.cpow_conj _ _ harg, Complex.conj_natCast]

end GoldbachBoundaries.Paper2.M6
