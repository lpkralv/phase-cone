import GoldbachBoundaries.Paper2.M3.Defs

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
namespace GoldbachBoundaries.Paper2.M3
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- A zero in the open strip cannot be real. -/
private lemma A1_im_ne_zero {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) : ρ.im ≠ 0 := by
  intro hi
  have he : (ρ.re : ℂ) = ρ := Complex.ext (by simp) (by simp [hi])
  exact riemannZeta_ne_zero_of_mem_Ioo ⟨hρ.2.1, hρ.2.2⟩ (he.symm ▸ hρ.1)


/-- **`R_ρ = -m(ρ)` for a zero with `β ≥ 1/2`** (unconditional). In `Rcoef ρ = -∑_{k ≥ 0} μ(k+1)/(k+1) ·
ord_{(k+1)ρ} ζ`, the term `k = 0` is `ordZeta ρ = m(ρ)` (`ρ ≠ 1`, `ρ ∈ NontrivialZeros`). For `n = k + 1 ≥ 2`,
`Re(nρ) = nβ ≥ 1`, so `nρ ∉ NontrivialZeros` (whose real parts are `< 1`), and `nρ ≠ 1` because `Im ρ ≠ 0` (a real zero
in `(0, 1)` is excluded by `riemannZeta_ne_zero_of_mem_Ioo`); so `ordZeta (nρ) = 0`. The `tsum` of a function supported
on `{0}` is its value there (`tsum_eq_single`). The same computation as M1's `Rcoef_one'`. Size: 80–150 lines. -/
theorem Rcoef_of_half_le_re {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) (hre : 1 / 2 ≤ ρ.re) :
    Rcoef ρ = -(zetaMult ρ : ℂ) := by
  classical
  unfold Rcoef
  rw [tsum_eq_single 0]
  · simp [ordZeta, ne_one_of_mem_nontrivialZeros hρ, hρ, mu]
  · intro k hk
    have hk2 : 2 ≤ k + 1 := by omega
    have hn : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) * ρ.re := by
      have : (2 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast hk2
      nlinarith
    have hnot : ((k + 1 : ℕ) : ℂ) * ρ ∉ NontrivialZeros := by
      intro hm
      have := hm.2.2
      simp only [mul_re, natCast_re, natCast_im, zero_mul, sub_zero] at this
      linarith
    have hne : ((k + 1 : ℕ) : ℂ) * ρ ≠ 1 := by
      intro he
      have hi := congrArg Complex.im he
      simp only [mul_im, natCast_re, natCast_im, zero_mul, add_zero, one_im] at hi
      exact (mul_ne_zero (by exact_mod_cast (show k + 1 ≠ 0 by omega)) (A1_im_ne_zero hρ)) hi
    simp only [ordZeta, if_neg hne, if_neg hnot, Int.cast_zero, mul_zero]

end GoldbachBoundaries.Paper2.M3
