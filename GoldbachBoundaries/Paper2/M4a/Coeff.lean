import GoldbachBoundaries.Paper2.M4a.Catalogue
import GoldbachBoundaries.Paper2.M4a.Fill.Rcoef_div_of_RH
import GoldbachBoundaries.Paper2.M4a.Fill.cP_ne_zero_of_RH

/-!
# M4a: the coefficients `c_a = -R_a` under RH (`cl:lem:P`(iv), the values)

`c_1 = -1` and `c_{1/j} = -μ(j)/j` are M1's `Rcoef_one'` and `Rcoef_inv` (no RH). For `a = ρ/n` the finite sum of
M1's `Rcoef_eq_finsum` runs over the squarefree `k` with `kρ/n` a zero; under RH `Re(kρ/n) = k/(2n)` must be `1/2`,
so `k = n` and `R_{ρ/n} = -μ(n)m(ρ)/n` (`Rcoef_div_of_RH`). Reality and `c_{ā} = c_a` are M1's `Rcoef_real_conj`
((Z1)). Non-vanishing: `μ(j) ≠ 0`, `μ(n) ≠ 0` for squarefree `j`, `n`, and `m(ρ) ≥ 1`.

The target `lem_P_iv_values_proof` is at the end of the file (`H3.lean` uses it).
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M4a

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-! ## Lemmas

Proved in `Fill/`, one file per lemma (same name, same statement): `Rcoef_div_of_RH`, `cP_ne_zero_of_RH`. -/

/-! ## Target -/

/-- `lem_P_iv_values` of `Paper2/Statements.lean`, statement verbatim. -/
theorem lem_P_iv_values_proof (hRH : RiemannHypothesis) (hZ1 : Z1) :
    (∀ a ∈ PoleSetQ, (cP a).im = 0 ∧ cP (conj a) = cP a ∧ cP a ≠ 0) ∧ cP 1 = -1 ∧
    (∀ j : ℕ, 2 ≤ j → Squarefree j → cP (1 / (j : ℂ)) = -(mu j / j)) ∧
    ∀ n : ℕ, 1 ≤ n → Squarefree n → ∀ ρ ∈ NontrivialZeros,
      cP (ρ / (n : ℂ)) = mu n * (zetaMult ρ : ℂ) / n := by
  refine ⟨fun a ha => ?_, by rw [cP, Rcoef_one'], fun j hj hsq => by rw [cP, Rcoef_inv hj hsq],
    fun n hn hsq ρ hρ => by rw [cP, Rcoef_div_of_RH hRH hn hsq hρ, neg_neg]⟩
  obtain ⟨hre, hconj⟩ := Rcoef_real_conj hZ1 ha
  refine ⟨by simp [cP, hre], by rw [cP, cP, hconj], cP_ne_zero_of_RH hRH ha⟩

end GoldbachBoundaries.Paper2.M4a
