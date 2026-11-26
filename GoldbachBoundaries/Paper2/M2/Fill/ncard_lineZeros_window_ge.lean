import GoldbachBoundaries.Paper2.M2.Fill.BCommon

/-! Filler group B: `ncard_lineZeros_window_ge` (`Single.lean`). The proof is `ncard_lineZeros_window_geB` in `Fill/BCommon.lean`. -/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M2

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **Many zeros on the line in `(X/M, X]`** ((Z2) and the (Z4) witnesses). For large `X`: `M = ⌈2 log X/A₀⌉₊ ≥ 1`,
`X/M ≤ X`, and the window is `{ρ on the line : 0 < γ ≤ X} ∖ {ρ on the line : 0 < γ ≤ X/M}`, so its size is
`N₀(X) - N₀(X/M) ≥ A₀X - N(X/M)` (`hN0` at `X ≥ t₀`; `N₀ ≤ N` by `ncard_zeros_le_Nzero` and `Set.ncard_le_ncard`;
`Set.ncard_diff`). Since `X/M ≥ X/(2 log X/A₀ + 1) → ∞`, `Nzero_le_mul_log` applies at `X/M`:
`N(X/M) ≤ (X/M) log(X/M) ≤ (X/M) log X ≤ A₀X/2` (`M ≥ 2 log X/A₀`). Size: 150–250 lines. -/
theorem ncard_lineZeros_window_ge (hZ2 : Z2) {A₀ t₀ : ℝ} (hA₀ : 0 < A₀)
    (hN0 : ∀ t ≥ t₀, A₀ * t ≤ (N0 t : ℝ)) :
    ∀ᶠ X in atTop,
      {ρ : ℂ | ρ ∈ NontrivialZeros ∧ ρ.re = 1 / 2 ∧ X / (Mfun A₀ X : ℝ) < ρ.im ∧ ρ.im ≤ X}.Finite ∧
      A₀ / 2 * X ≤
        ({ρ : ℂ | ρ ∈ NontrivialZeros ∧ ρ.re = 1 / 2 ∧ X / (Mfun A₀ X : ℝ) < ρ.im ∧ ρ.im ≤ X}.ncard : ℝ) :=
  ncard_lineZeros_window_geB hZ2 hA₀ hN0

end GoldbachBoundaries.Paper2.M2
