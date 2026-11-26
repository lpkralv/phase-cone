import GoldbachBoundaries.Paper2.M3.Numerics

/-!
# Fill: `sum_weight_le`

For a zero with `β ∈ [1/2, 1)`: `m(ρ)/(1 + γ²) ≤ 2m(ρ)Re(1/ρ)`, since `Re(1/ρ) = β/(β² + γ²)` and
`2β(1 + γ²) - (β² + γ²) = β(2 - β) + γ²(2β - 1) ≥ 0`. The (Z7) terms are non-negative, so the sub-sum over the zeros
with `β = B` (an injection into `NontrivialZeros`) is at most `C₀`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M3

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- `1/(1 + γ²) ≤ 2 Re(1/ρ)` for `1/2 ≤ β ≤ 1`. -/
lemma groupB_inv_one_add_im_sq_le {ρ : ℂ} (h1 : 1 / 2 ≤ ρ.re) (h2 : ρ.re ≤ 1) :
    1 / (1 + ρ.im ^ 2) ≤ 2 * (1 / ρ).re := by
  have hb : 0 < ρ.re := by linarith
  have hns : 0 < ρ.re * ρ.re + ρ.im * ρ.im := by nlinarith [mul_pos hb hb, mul_self_nonneg ρ.im]
  rw [one_div ρ, Complex.inv_re, Complex.normSq_apply]
  rw [div_le_iff₀ (by positivity), mul_comm, ← mul_assoc, mul_div_assoc', le_div_iff₀ hns]
  nlinarith [sq_nonneg ρ.im, mul_nonneg (sq_nonneg ρ.im) (by linarith : (0 : ℝ) ≤ 2 * ρ.re - 1)]

/-- The (Z7) terms are non-negative. -/
lemma groupB_z7_term_nonneg (ρ : NontrivialZeros) : 0 ≤ (zetaMult (ρ : ℂ) : ℝ) * (1 / (ρ : ℂ)).re := by
  have hb : 0 < (ρ : ℂ).re := ρ.2.2.1
  refine mul_nonneg (Nat.cast_nonneg _) ?_
  rw [one_div, Complex.inv_re]
  exact div_nonneg hb.le (Complex.normSq_nonneg _)

/-- Pointwise comparison with the (Z7) terms. -/
lemma groupB_weight_le (hB1 : 1 / 2 ≤ Bsup) (hB2 : Bsup < 1)
    (ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ ρ.re = Bsup}) :
    (zetaMult (ρ : ℂ) : ℝ) / (1 + (ρ : ℂ).im ^ 2) ≤
      2 * ((zetaMult (ρ : ℂ) : ℝ) * (1 / (ρ : ℂ)).re) := by
  have hre := ρ.2.2
  have h := groupB_inv_one_add_im_sq_le (ρ := (ρ : ℂ)) (by rw [hre]; exact hB1) (by rw [hre]; exact hB2.le)
  have hm : (0 : ℝ) ≤ zetaMult (ρ : ℂ) := Nat.cast_nonneg _
  calc (zetaMult (ρ : ℂ) : ℝ) / (1 + (ρ : ℂ).im ^ 2)
      = (zetaMult (ρ : ℂ) : ℝ) * (1 / (1 + (ρ : ℂ).im ^ 2)) := by ring
    _ ≤ (zetaMult (ρ : ℂ) : ℝ) * (2 * (1 / (ρ : ℂ)).re) := mul_le_mul_of_nonneg_left h hm
    _ = _ := by ring

/-- **(a) The weights `x_ρ`** (Z7). For a zero with `β = B ∈ [1/2, 1)`: `Re(1/ρ) = β/(β² + γ²)` and
`β(1 + γ²) - (β² + γ²)/2 = β(1 - β/2) + γ²(β - 1/2) ≥ 0`, so `m(ρ)/(1 + γ²) ≤ 2m(ρ)Re(1/ρ)`. (Z7) is a `HasSum` of
non-negative terms over all zeros (non-negative: `β > 0`); restricted to the subtype `{β = B}` (an injection into
`NontrivialZeros`) it is summable with sum `≤ C₀` (`Summable.subtype`, `Summable.tsum_le_tsum_of_inj` or
`tsum_subtype_le`). Comparison gives both claims. Size: 100–200 lines. -/
theorem sum_weight_le (hZ7 : Z7) (hB1 : 1 / 2 ≤ Bsup) (hB2 : Bsup < 1) :
    Summable (fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ ρ.re = Bsup} =>
        (zetaMult (ρ : ℂ) : ℝ) / (1 + (ρ : ℂ).im ^ 2)) ∧
      ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ ρ.re = Bsup},
        (zetaMult (ρ : ℂ) : ℝ) / (1 + (ρ : ℂ).im ^ 2) ≤ 2 * C0 := by
  set g : NontrivialZeros → ℝ := fun ρ => (zetaMult (ρ : ℂ) : ℝ) * (1 / (ρ : ℂ)).re with hg
  let e : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ ρ.re = Bsup} → NontrivialZeros := fun ρ => ⟨ρ.1, ρ.2.1⟩
  have he : Function.Injective e := by
    intro a b hab
    exact Subtype.ext (congrArg (fun x : NontrivialZeros => (x : ℂ)) hab)
  have hgs : Summable g := hZ7.summable
  have hge : Summable (g ∘ e) := hgs.comp_injective he
  have hle : ∀ ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ ρ.re = Bsup}, (zetaMult (ρ : ℂ) : ℝ) / (1 + (ρ : ℂ).im ^ 2) ≤ 2 * (g ∘ e) ρ :=
    fun ρ => groupB_weight_le hB1 hB2 ρ
  have hnn : ∀ ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ ρ.re = Bsup},
      0 ≤ (zetaMult (ρ : ℂ) : ℝ) / (1 + (ρ : ℂ).im ^ 2) := fun ρ => by positivity
  have hs : Summable (fun ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ ρ.re = Bsup} =>
      (zetaMult (ρ : ℂ) : ℝ) / (1 + (ρ : ℂ).im ^ 2)) :=
    Summable.of_nonneg_of_le hnn hle (hge.mul_left 2)
  refine ⟨hs, ?_⟩
  calc _ ≤ ∑' ρ, 2 * (g ∘ e) ρ := hs.tsum_le_tsum hle (hge.mul_left 2)
    _ = 2 * ∑' ρ, (g ∘ e) ρ := tsum_mul_left
    _ ≤ 2 * ∑' ρ, g ρ := by
        gcongr
        exact hge.tsum_le_tsum_of_inj e he (fun c _ => groupB_z7_term_nonneg c) (fun _ => le_rfl) hgs
    _ = 2 * C0 := by rw [hZ7.tsum_eq]

end GoldbachBoundaries.Paper2.M3
