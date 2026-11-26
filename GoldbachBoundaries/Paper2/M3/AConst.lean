import GoldbachBoundaries.Paper2.M3.Numerics
import GoldbachBoundaries.Paper2.M3.Fill.Aconst_terms_le
import GoldbachBoundaries.Paper2.M3.Fill.exp_neg_one_le_Gamma
import GoldbachBoundaries.Paper2.M3.Fill.norm_Gamma_sq_le
import GoldbachBoundaries.Paper2.M3.Fill.sum_weight_le

/-!
# M3: the constant `A` (`nr:lem:A`)

(Z7), `1/2 < B < 1`, some zero with `β = B`. `A = Γ(2B)⁻¹ ∑_{β = B} m(ρ)²|Γ(ρ)|²` (`Aconst`, a `tsum` over the
subtype of zeros with `β = B`, which may be infinite here: `lem_A` does not assume `B > B_∞`). The paper's four steps:

(a) `x_ρ = m(ρ)/(1 + γ²) ≤ 2m(ρ) Re(1/ρ)` for `1/2 ≤ β < 1`, so `W = ∑_{β = B} x_ρ ≤ 2C₀` by (Z7) (the terms of (Z7)
    are non-negative, so a sub-sum is at most `C₀`);
(b) `|Γ(β + iγ)|² ≤ 4π/(1 + γ²)²` for `1/2 ≤ β ≤ 1`;
(c) `Γ(x) ≥ e⁻¹` for `x ≥ 1`, so `1/Γ(2B) ≤ e`;
(d) `∑ m(ρ)²|Γ(ρ)|² ≤ 4π ∑ x_ρ² ≤ 4π W² ≤ 16πC₀²`.

Then `A ≤ 16πeC₀²`, and `Numerics.lean` gives `0.0728 < 16πeC₀² < 0.0729`. The paper writes `<` in (a), (c), (d);
`≤` is all the statement needs. The target `lem_A_proof` is at the end of this file (`Real.lean` uses it).
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M3

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-! ## Target: `lem_A` -/

/-- `lem_A` of `Paper2/Statements.lean`, statement verbatim. -/
theorem lem_A_proof (hZ7 : Z7) (h1 : 1 / 2 < Bsup) (h2 : Bsup < 1)
    (h3 : ∃ ρ ∈ NontrivialZeros, ρ.re = Bsup) :
    0 < Aconst ∧ Aconst ≤ 16 * Real.pi * Real.exp 1 * C0 ^ 2 ∧
      0.0728 < 16 * Real.pi * Real.exp 1 * C0 ^ 2 ∧ 16 * Real.pi * Real.exp 1 * C0 ^ 2 < 0.0729 := by
  obtain ⟨hsum, hle⟩ := Aconst_terms_le hZ7 h1.le h2
  have hG : Real.exp (-1) ≤ Real.Gamma (2 * Bsup) := exp_neg_one_le_Gamma (by linarith)
  have hGpos : 0 < Real.Gamma (2 * Bsup) := Real.Gamma_pos_of_pos (by linarith)
  obtain ⟨ρ, hρ, hre⟩ := h3
  have hpos : 0 < ∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ ρ.re = Bsup},
      (zetaMult (ρ : ℂ) : ℝ) ^ 2 * ‖Gamma (ρ : ℂ)‖ ^ 2 := by
    refine hsum.tsum_pos (fun _ => by positivity) ⟨ρ, hρ, hre⟩ ?_
    have hm : (1 : ℝ) ≤ zetaMult ρ := by exact_mod_cast one_le_zetaMult hρ
    have hΓ : Gamma ρ ≠ 0 := Gamma_ne_zero_of_re_pos hρ.2.1
    exact mul_pos (pow_pos (by linarith) 2) (pow_pos (norm_pos_iff.mpr hΓ) 2)
  refine ⟨div_pos hpos hGpos, ?_, const_bounds⟩
  unfold Aconst
  rw [div_le_iff₀ hGpos]
  have hC : 0 ≤ 16 * Real.pi * Real.exp 1 * C0 ^ 2 := by positivity
  calc _ ≤ 16 * Real.pi * C0 ^ 2 := hle
    _ = 16 * Real.pi * Real.exp 1 * C0 ^ 2 * Real.exp (-1) := by
      rw [Real.exp_neg]
      field_simp
    _ ≤ 16 * Real.pi * Real.exp 1 * C0 ^ 2 * Real.Gamma (2 * Bsup) :=
      mul_le_mul_of_nonneg_left hG hC

end GoldbachBoundaries.Paper2.M3
