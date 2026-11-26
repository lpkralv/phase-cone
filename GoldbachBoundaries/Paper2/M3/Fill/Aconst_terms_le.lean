import GoldbachBoundaries.Paper2.M3.Numerics
import GoldbachBoundaries.Paper2.M3.Fill.norm_Gamma_sq_le
import GoldbachBoundaries.Paper2.M3.Fill.sum_weight_le

/-!
# Fill: `Aconst_terms_le`

With `x_ρ = m(ρ)/(1 + γ²)` and `W = ∑_{β = B} x_ρ ≤ 2C₀` (`sum_weight_le`): `m(ρ)²|Γ(ρ)|² ≤ 4π x_ρ²`
(`norm_Gamma_sq_le` at `ρ = B + iγ`) and `x_ρ² ≤ W x_ρ`, so the sum is at most `4πW² ≤ 16πC₀²`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M3

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **(d) The sum in `A`** (Z7). Write `ρ = B + iγ` (`Complex.re_add_im`); `norm_Gamma_sq_le` (with `1/2 ≤ B ≤ 1`)
gives `m(ρ)²|Γ(ρ)|² ≤ 4π x_ρ²`, `x_ρ = m(ρ)/(1 + γ²)`. With `W = ∑ x_ρ` (`sum_weight_le`): `x_ρ² ≤ W x_ρ`
(`x_ρ ≤ W`, `le_tsum` for non-negative terms), so `∑ x_ρ²` is summable with sum `≤ W² ≤ 4C₀²` (`0 ≤ W ≤ 2C₀`).
Comparison (`Summable.of_nonneg_of_le`, `Summable.tsum_le_tsum`). Size: 100–200 lines. -/
theorem Aconst_terms_le (hZ7 : Z7) (hB1 : 1 / 2 ≤ Bsup) (hB2 : Bsup < 1) :
    Summable (fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ ρ.re = Bsup} =>
        (zetaMult (ρ : ℂ) : ℝ) ^ 2 * ‖Gamma (ρ : ℂ)‖ ^ 2) ∧
      ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ ρ.re = Bsup},
        (zetaMult (ρ : ℂ) : ℝ) ^ 2 * ‖Gamma (ρ : ℂ)‖ ^ 2 ≤ 16 * Real.pi * C0 ^ 2 := by
  obtain ⟨hxs, hW⟩ := sum_weight_le hZ7 hB1 hB2
  set x : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ ρ.re = Bsup} → ℝ :=
    fun ρ => (zetaMult (ρ : ℂ) : ℝ) / (1 + (ρ : ℂ).im ^ 2) with hx
  set W := ∑' ρ, x ρ with hWdef
  have hxnn : ∀ ρ, 0 ≤ x ρ := fun ρ => by positivity
  have hW0 : 0 ≤ W := tsum_nonneg hxnn
  have hxW : ∀ ρ, x ρ ≤ W := fun ρ => hxs.le_tsum ρ (fun j _ => hxnn j)
  -- the pointwise Gamma bound
  have hterm : ∀ ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ ρ.re = Bsup},
      (zetaMult (ρ : ℂ) : ℝ) ^ 2 * ‖Gamma (ρ : ℂ)‖ ^ 2 ≤ 4 * Real.pi * W * x ρ := by
    intro ρ
    have hre := ρ.2.2
    have hG := norm_Gamma_sq_le (x := (ρ : ℂ).re) (t := (ρ : ℂ).im) (by rw [hre]; exact hB1)
      (by rw [hre]; exact hB2.le)
    rw [Complex.re_add_im] at hG
    have hm : (0 : ℝ) ≤ (zetaMult (ρ : ℂ) : ℝ) ^ 2 := by positivity
    have hpos : 0 < 1 + (ρ : ℂ).im ^ 2 := by positivity
    calc (zetaMult (ρ : ℂ) : ℝ) ^ 2 * ‖Gamma (ρ : ℂ)‖ ^ 2
        ≤ (zetaMult (ρ : ℂ) : ℝ) ^ 2 * (4 * Real.pi / (1 + (ρ : ℂ).im ^ 2) ^ 2) :=
          mul_le_mul_of_nonneg_left hG hm
      _ = 4 * Real.pi * x ρ * x ρ := by
          rw [hx]
          field_simp
      _ ≤ 4 * Real.pi * x ρ * W := by
          gcongr
          exact hxW ρ
      _ = 4 * Real.pi * W * x ρ := by ring
  have hnn : ∀ ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ ρ.re = Bsup},
      0 ≤ (zetaMult (ρ : ℂ) : ℝ) ^ 2 * ‖Gamma (ρ : ℂ)‖ ^ 2 := fun ρ => by positivity
  have hbs : Summable (fun ρ => 4 * Real.pi * W * x ρ) := hxs.mul_left _
  have hs := Summable.of_nonneg_of_le hnn hterm hbs
  refine ⟨hs, ?_⟩
  calc _ ≤ ∑' ρ, 4 * Real.pi * W * x ρ := hs.tsum_le_tsum hterm hbs
    _ = 4 * Real.pi * W * W := by rw [tsum_mul_left]
    _ ≤ 4 * Real.pi * (2 * C0) * (2 * C0) := by
        have hC : W ≤ 2 * C0 := hW
        have hC0 : 0 ≤ 2 * C0 := hW0.trans hC
        gcongr
    _ = 16 * Real.pi * C0 ^ 2 := by ring

end GoldbachBoundaries.Paper2.M3
