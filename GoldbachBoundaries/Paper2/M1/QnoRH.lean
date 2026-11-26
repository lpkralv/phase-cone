import GoldbachBoundaries.Paper2.M1.Defs

/-!
# M1: the singularities of `Q` without RH (`nr:lem:Q` (i), (ii))

Everything is unconditional except where (Z1)
appears (the multiplicity of `ρ̄`, and a zero with `β ≥ 1/2`).

Paper 1's library already gives, without RH: `Qcont` meromorphic on `Re z > 0` (`meromorphicAt_Qcont`), the local
structure `Qcont - ∑_{n ∈ S} μ(n) A(n ·)` analytic at `a` when the terms outside `S` are regular
(`analyticAt_Qcont_sub_sum`), regularity of every term off `Σ` (`regular_of_not_mem_poleSetQ`), the residue of
`A = -ζ'/ζ` at its poles (`hasResidue_negLogDerivZeta_*`), the residue API (`ResidueAPI.lean`), finiteness of zeros
in compact sets avoiding `1` (`riemannZeta_zeros_finite_of_isCompact`), and the proof of local finiteness of `Σ`
inside `lem_Sigma_iv_proof` (it does not use its RH hypothesis for that part).

**Integrated layout.** The 13 lemmas this file stated with `sorry` (`poleSetQ_locallyFinite`, `conj_mem_poleSetQ`,
`poleSetQ_re_bounds`, `Bsup_facts`, `hasResidue_Qcont_Rcoef`, `meromorphicOrderAt_Qcont_ge`,
`meromorphicOrderAt_Qcont_neg_iff`, `Qcont_conj`, `isQCont_eventuallyEq`, `Rcoef_real_conj`, `Rcoef_inv`,
`Rcoef_eq_finsum`, `poleSetQ_re_le_Bsup`) are proved in `Fill/<name>.lean`, statements unchanged, each with its sketch
as docstring; `Assembly.lean` imports them. The real lemmas that use them moved to the fill file of the lemma they
use: `isQCont_order_ge` to `Fill/isQCont_eventuallyEq.lean`. This file keeps the statements' context and the real
lemmas that use none of them.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M1

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- `R_1 = 1` (the proof of `Rcoef_one` in `Paper2/Statements.lean`, which this file may not import). -/
lemma Rcoef_one' : Rcoef 1 = 1 := by
  have hz : ∀ k : ℕ, k ≠ 0 →
      mu (k + 1) / ((k + 1 : ℕ) : ℂ) * (ordZeta (((k + 1 : ℕ) : ℂ) * 1) : ℂ) = 0 := by
    intro k hk
    have h1 : ((k + 1 : ℕ) : ℂ) * 1 ≠ 1 := by
      rw [mul_one]; exact_mod_cast (by omega : k + 1 ≠ 1)
    have h2 : ((k + 1 : ℕ) : ℂ) * 1 ∉ NontrivialZeros := by
      rintro ⟨-, -, h⟩
      simp only [mul_one, Complex.natCast_re] at h
      have : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ k + 1)
      linarith
    simp only [mul_one, Nat.cast_add, Nat.cast_one] at h2
    simp [ordZeta, hk, h2]
  rw [Rcoef, tsum_eq_single 0 hz]
  simp [ordZeta]

end GoldbachBoundaries.Paper2.M1
