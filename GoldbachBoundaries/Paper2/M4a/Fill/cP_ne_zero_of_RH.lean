import GoldbachBoundaries.Paper2.M4a.Fill.Rcoef_div_of_RH

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
namespace GoldbachBoundaries.Paper2.M4a
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **`c_a ≠ 0` on `Σ` under RH.** Case split on `PoleSetQ`: `a = 1`: `c_1 = -R_1 = -1` (M1's `Rcoef_one'`);
`a = 1/j`: `c = -μ(j)/j` (M1's `Rcoef_inv`), `μ(j) ≠ 0` as `j` is squarefree
(`ArithmeticFunction.moebius_ne_zero_iff_squarefree`); `a = ρ/n`: `c = μ(n)m(ρ)/n` (`Rcoef_div_of_RH`), with
`μ(n) ≠ 0` and `m(ρ) ≥ 1` (paper 1's `one_le_zetaMult`). Size: 50–100 lines. -/
theorem cP_ne_zero_of_RH (hRH : RiemannHypothesis) {a : ℂ} (ha : a ∈ PoleSetQ) : cP a ≠ 0 := by
  rcases ha with (rfl | ⟨j, hj, hsq, rfl⟩) | ⟨n, hn, hsq, ρ, hρ, rfl⟩
  · rw [cP, Rcoef_one']
    exact neg_ne_zero.mpr one_ne_zero
  · rw [cP, Rcoef_inv hj hsq]
    exact neg_ne_zero.mpr (div_ne_zero (mu_ne_zero_of_squarefree hsq)
      (by exact_mod_cast (by omega : j ≠ 0)))
  · rw [cP, Rcoef_div_of_RH hRH hn hsq hρ, neg_neg]
    have hm : 1 ≤ zetaMult ρ := one_le_zetaMult_of_zero (by
      intro heq
      have := hρ.2.2
      simp [heq] at this) hρ.1
    exact div_ne_zero (mul_ne_zero (mu_ne_zero_of_squarefree hsq)
      (by exact_mod_cast (by omega : zetaMult ρ ≠ 0)))
      (by exact_mod_cast (by omega : n ≠ 0))

end GoldbachBoundaries.Paper2.M4a
