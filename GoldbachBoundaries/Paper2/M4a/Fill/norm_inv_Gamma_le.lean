import GoldbachBoundaries.Paper2.M4a.Fill.DCommon

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M4a

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/- Filler for `norm_inv_Gamma_le` (`Kernel.lean`): reflection, a shift by `N`, (Z6); compactness for `|t| ≤ 1`. -/
/-- **`1/Γ` on a vertical strip** ((Z6)). For `|t| ≤ 1` the bound is compactness: `1/Γ` is entire
(`Complex.differentiable_one_div_Gamma`), so bounded on `[σ₁, σ₂] × [-1, 1]`. For `|t| ≥ 1`: the reflection formula
`Γ(s)Γ(1 - s) = π/sin(πs)` (`Complex.Gamma_mul_Gamma_one_sub`) gives `1/|Γ(s)| = |Γ(1 - s)||sin(πs)|/π`, with
`|sin(πs)| ≤ cosh(πt) ≤ e^{π|t|}`. Shift `1 - s` right by `N` with `1 - σ₂ + N > 0`:
`Γ(1 - s) = Γ(1 - s + N)/∏_{j<N}(1 - s + j)` (`Complex.Gamma_add_one`), each `|1 - s + j| ≥ |t| ≥ 1`, and (Z6) on
`[1 - σ₂ + N, 1 - σ₁ + N]` gives `|Γ(1 - s + N)| ≤ C(1 + |t|)^{x₂}e^{-π|t|/2}`. (Alternatively the paper's product
formula, from Mathlib's `Complex.GammaSeq` limit.) Size: 150–250 lines. -/
theorem norm_inv_Gamma_le (hZ6 : Z6) {σ₁ σ₂ : ℝ} (h₁ : 0 < σ₁) (h₁₂ : σ₁ ≤ σ₂) :
    ∃ C A : ℝ, ∀ σ ∈ Icc σ₁ σ₂, ∀ t : ℝ,
      ‖(Gamma (σ + t * I))⁻¹‖ ≤ C * (1 + |t|) ^ A * Real.exp (Real.pi * |t| / 2) := by
  obtain ⟨C, A, -, -, h⟩ := FillD.norm_inv_Gamma_le' hZ6 h₁ h₁₂
  exact ⟨C, A, h⟩

end GoldbachBoundaries.Paper2.M4a
