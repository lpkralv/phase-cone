import GoldbachBoundaries.Paper2.M4a.Fill.DCommon

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M4a

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/- Filler for `norm_KerS_le_kernelt` (`Kernel.lean`): (Z6) twice and `norm_inv_Gamma_le`. -/
/-- **The kernel bound of `cl:lem:kernelt`** ((Z6)). `s - w = (σ - x) + (t - y)i` with
`σ - x ∈ [σ₁ - x₂, σ₂ - x₁] ⊂ (0, ∞)`. (Z6) on `[x₁, x₂]`: `|Γ(x + iy)| ≤ C₁(1 + |y|)^{x₂}e^{-π|y|/2}`; (Z6) on
`[σ₁ - x₂, σ₂ - x₁]`: `|Γ(s - w)| ≤ C₂(1 + |t - y|)^{σ₂ - x₁}e^{-π|t - y|/2}`; `norm_inv_Gamma_le`:
`1/|Γ(s)| ≤ C₃(1 + |t|)^{A₃}e^{π|t|/2}`. Multiply (`norm_div`, `norm_mul`, `Real.exp_add`) and take
`A = max(x₂, σ₂ - x₁, A₃, 0)`, using `(1 + |u|)^a ≤ (1 + |u|)^A` for `a ≤ A` (base `≥ 1`, `Real.rpow_le_rpow_of_exponent_le`)
and `C = max(C₁,0)·max(C₂,0)·max(C₃,0)`. Size: 100–200 lines. -/
theorem norm_KerS_le_kernelt (hZ6 : Z6) :
    ∀ x₁ x₂ σ₁ σ₂ : ℝ, 0 < x₁ → x₁ ≤ x₂ → x₂ < σ₁ → σ₁ ≤ σ₂ → ∃ C A : ℝ,
      ∀ x ∈ Icc x₁ x₂, ∀ y : ℝ, ∀ σ ∈ Icc σ₁ σ₂, ∀ t : ℝ,
        ‖KerS (σ + t * I) (x + y * I)‖ ≤ C * (1 + |y|) ^ A * (1 + |t - y|) ^ A * (1 + |t|) ^ A *
          Real.exp (-(Real.pi / 2 * (|y| + |t - y| - |t|))) := by
  intro x₁ x₂ σ₁ σ₂ hx₁ hx₁₂ hxσ hσ₁₂
  obtain ⟨C, A, -, -, h⟩ := FillD.norm_KerS_le_kernelt' hZ6 hx₁ hx₁₂ hxσ hσ₁₂
  exact ⟨C, A, h⟩

end GoldbachBoundaries.Paper2.M4a
