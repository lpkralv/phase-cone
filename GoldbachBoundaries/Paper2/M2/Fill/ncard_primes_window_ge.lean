import GoldbachBoundaries.Paper2.M2.Fill.BCommon

/-! Filler group B: `ncard_primes_window_ge` (`Single.lean`). The proof is `ncard_primes_window_geB` in `Fill/BCommon.lean`. -/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M2

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **Many primes for each ordinate** (Z5). `γ/q ∈ (y - ε/2, y + ε/2)` iff `x < q < (1 + θ)x` with
`x = γ/(y + ε/2)`, `1 + θ = (y + ε/2)/(y - ε/2)` (`y - ε/2 > 0`), so the set is the set of (Z5) at `(θ, x)`, finite
(bounded). For large `X` and every `γ ∈ (X/M, X]`: `x ≥ X/(M(y + ε/2)) → ∞` uniformly, so `x ≥ x₀(θ)`;
`log x ≤ 2 log X`; `M ≤ 3 log X/A₀`. Hence `θx/(2 log x) ≥ θA₀X/(12(y + ε/2) log² X)`; take
`c₁ = θA₀/(12(y + ε/2))`. Size: 150–250 lines. -/
theorem ncard_primes_window_ge (hZ5 : Z5) {A₀ y ε : ℝ} (hA₀ : 0 < A₀) (hy : 0 < y) (hε : 0 < ε)
    (hεy : ε < y) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ᶠ X in atTop, ∀ γ : ℝ, X / (Mfun A₀ X : ℝ) < γ → γ ≤ X →
      {q : ℕ | q.Prime ∧ γ / (q : ℝ) ∈ Ioo (y - ε / 2) (y + ε / 2)}.Finite ∧
      c₁ * X / Real.log X ^ 2 ≤
        ({q : ℕ | q.Prime ∧ γ / (q : ℝ) ∈ Ioo (y - ε / 2) (y + ε / 2)}.ncard : ℝ) :=
  ncard_primes_window_geB hZ5 hA₀ hy hε hεy

end GoldbachBoundaries.Paper2.M2
