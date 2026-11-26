import GoldbachBoundaries.Paper2.M4a.Catalogue
import GoldbachBoundaries.SigmaFinite
import GoldbachBoundaries.Density

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
namespace GoldbachBoundaries.Paper2.M4a
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

private lemma A_scaled_inj (hRH : RiemannHypothesis) {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    {ρ σ : ℂ} (hρ : ρ ∈ NontrivialZeros) (hσ : σ ∈ NontrivialZeros)
    (h : ρ / (n : ℂ) = σ / (m : ℂ)) : n = m ∧ ρ = σ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hmR : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hre := congrArg Complex.re h
  simp only [Complex.div_natCast_re, sigmaFinite_re_eq_half hRH hρ,
    sigmaFinite_re_eq_half hRH hσ] at hre
  have hnm : n = m := by
    have := (div_eq_div_iff hnR.ne' hmR.ne').mp hre
    have : (n : ℝ) = m := by linarith
    exact_mod_cast this
  subst m
  exact ⟨rfl, (div_left_inj' (by exact_mod_cast hnR.ne' : (n : ℂ) ≠ 0)).mp h⟩

/-- **`R_{ρ/n}` under RH.** `a = ρ/n` is not real (`Im ρ ≠ 0`: no zero of `ζ` in `(0, 1)`, paper 1's
`riemannZeta_ne_zero_of_mem_Ioo`) and lies in `Σ_Q`, so M1's `Rcoef_eq_finsum` writes `R_a` as `-∑ᶠ` over
`{k ≥ 1 squarefree, k < 1/Re a, k·a ∈ Z}`. Under RH (paper 1's `re_eq_half_of_mem_nontrivialZeros`) `Re(kρ/n) = k/(2n)`
equals `1/2` iff `k = n`, and `n·(ρ/n) = ρ` is a zero with `n < 2n = 1/Re a`; so the set is `{n}`
(`finsum_mem_singleton`), and the term is `μ(n)/n · m(ρ)`. Size: 80–150 lines. -/
theorem Rcoef_div_of_RH (hRH : RiemannHypothesis) {n : ℕ} (hn : 1 ≤ n) (hsq : Squarefree n) {ρ : ℂ}
    (hρ : ρ ∈ NontrivialZeros) : Rcoef (ρ / (n : ℂ)) = -(mu n * (zetaMult ρ : ℂ) / n) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hu : ρ / (n : ℂ) ∈ PoleSetQ := Or.inr ⟨n, hn, hsq, ρ, hρ, rfl⟩
  have him : (ρ / (n : ℂ)).im ≠ 0 := by
    simp only [Complex.div_natCast_im]
    exact div_ne_zero (im_ne_zero_of_mem_nontrivialZeros hρ) hnR.ne'
  have hset : {k : ℕ | 1 ≤ k ∧ Squarefree k ∧ (k : ℝ) < 1 / (ρ / (n : ℂ)).re ∧
      (k : ℂ) * (ρ / (n : ℂ)) ∈ NontrivialZeros} = {n} := by
    ext k
    simp only [mem_ofPred_eq, mem_singleton_iff]
    constructor
    · rintro ⟨hk, _, _, hz⟩
      have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
      exact (A_scaled_inj hRH hk hn hz hρ (by field_simp)).1
    · rintro rfl
      refine ⟨hn, hsq, ?_, ?_⟩
      · rw [Complex.div_natCast_re, one_div_div, lt_div_iff₀ hρ.2.1]
        nlinarith [hρ.2.2]
      · rwa [mul_div_cancel₀ _ hn0]
  rw [Rcoef_eq_finsum hu him, hset, finsum_mem_singleton, mul_div_cancel₀ _ hn0]
  ring

end GoldbachBoundaries.Paper2.M4a
