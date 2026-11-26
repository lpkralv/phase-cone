import GoldbachBoundaries.Phi2.Defs

/-!
## Junk values (as for `Phi2`)

`PhiR r` is a `tsum`, so it is `0` where the `r`-fold series is not summable (for `Re s ≤ r`). No statement evaluates it
off `σ > r`: continuations are quantified functions that agree with it on `σ > r`.
-/

noncomputable section

open Complex Filter Topology Set Metric

namespace GoldbachBoundaries

/-- `Φ_r(s) = ∑_{k_1, …, k_r ≥ 1} Λ(k_1) ⋯ Λ(k_r) (k_1 + ⋯ + k_r)^{-s}`, over ordered `r`-tuples. Meaningful for
`Re s > r` only.

Indexed by `Fin r → ℕ`: a tuple with some `k_i = 0` contributes `0` because `Λ(0) = 0`, so this is the sum over
`k_i ≥ 1` (`PhiR_term_eq_zero` in `Statement.lean`). For `r = 2` it is `Phi2` at every `s` (`PhiR_two`). -/
def PhiR (r : ℕ) (s : ℂ) : ℂ :=
  ∑' k : Fin r → ℕ, (∏ i, ((ArithmeticFunction.vonMangoldt (k i) : ℝ) : ℂ)) *
    (((∑ i, k i : ℕ) : ℂ)) ^ (-s)

/-- The vertical line `σ = a`. (`lineAt 1 = lineOne`, `lineAt_one`.) -/
def lineAt (a : ℝ) : Set ℂ := {s | s.re = a}

 
def polyP (j : ℕ) (s : ℂ) : ℂ := ∏ l ∈ Finset.Icc 1 j, (s - (l : ℂ))

/-- The poles of the continuation of `Φ_r` in `σ > r - 1`: `r` and `r - 1 + ρ` for every non-trivial zero `ρ` (under
RH the points `r - 1/2 + iγ`). Defined without RH; it lies in `σ > r - 1` unconditionally (`phiRPoles_subset`).
`phiRPoles 2 = phi2Poles` (`phiRPoles_two`). -/
def phiRPoles (r : ℕ) : Set ℂ := {(r : ℂ)} ∪ {s | ∃ ρ ∈ NontrivialZeros, s = ((r : ℂ) - 1) + ρ}



def HasPhiRResidues (r : ℕ) (v : ℂ → ℂ) : Prop :=
  v (r : ℂ) = 1 / ((r - 1).factorial : ℂ) ∧
  ∀ ρ ∈ NontrivialZeros,
    v (((r : ℂ) - 1) + ρ) = -((r : ℂ) * (zetaMult ρ : ℂ)) * Gamma ρ / Gamma (ρ + ((r : ℂ) - 1))

end GoldbachBoundaries
