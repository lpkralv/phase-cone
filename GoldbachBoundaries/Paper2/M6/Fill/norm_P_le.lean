import GoldbachBoundaries.Paper2.M6.Defs

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
namespace GoldbachBoundaries.Paper2.M6
open GoldbachBoundaries GoldbachBoundaries.Paper2

theorem norm_P_le {z : ℂ} (hz : 1 < z.re) : ‖P z‖ ≤ (P z.re).re := by
  have hterm (p : Nat.Primes) :
      ‖((p : ℕ) : ℂ) ^ (-z)‖ = (((p : ℕ) : ℂ) ^ (-(z.re : ℂ))).re := by
    rw [norm_natCast_cpow_of_pos p.prop.pos]
    have hp : (0 : ℝ) ≤ (p : ℕ) := Nat.cast_nonneg _
    rw [← ofReal_neg, ← ofReal_natCast, ← ofReal_cpow hp]
    simp
  unfold P
  calc
    _ ≤ ∑' p : Nat.Primes, ‖((p : ℕ) : ℂ) ^ (-z)‖ :=
      norm_tsum_le_tsum_norm (summable_norm_P_terms hz)
    _ = _ := by
      simp_rw [hterm]
      exact (Complex.re_tsum (summable_P_terms (z := (z.re : ℂ)) hz)).symm

end GoldbachBoundaries.Paper2.M6
