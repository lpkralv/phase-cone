import GoldbachBoundaries.Paper2.M3.Numerics

/-!
# Fill: `norm_Gamma_sq_le`

`s = x + it`, `1/2 ≤ x ≤ 1`. `Γ(s + 2) = (s + 1)sΓ(s)` and `|Γ(s + 2)| ≤ Γ(x + 2) = x(x + 1)Γ(x)` (PNT+'s
`Complex.Gamma.norm_le_Gamma_re`), with `Γ(x) ≤ max(Γ(1/2), Γ(1)) = √π` (convexity of `Γ`). Then
`|s|² = x² + t² ≥ x²(1 + t²)` (`x ≤ 1`) and `|s + 1|² = (x + 1)² + t² ≥ (x + 1)²(1 + t²)/4` (`x + 1 ≤ 2`) give
`|Γ(s)|² x²(x + 1)²(1 + t²)²/4 ≤ |Γ(s)|²|s|²|s + 1|² ≤ x²(x + 1)²π`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M3

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- `Γ(x) ≤ √π` on `[1/2, 1]` (convexity, below the larger end value `Γ(1/2) = √π ≥ 1 = Γ(1)`). -/
lemma groupB_Gamma_le_sqrt_pi {x : ℝ} (hx1 : 1 / 2 ≤ x) (hx2 : x ≤ 1) :
    Real.Gamma x ≤ Real.sqrt Real.pi := by
  have hseg : x ∈ segment ℝ (1 / 2 : ℝ) 1 := by
    rw [segment_eq_Icc (by norm_num)]
    exact ⟨hx1, hx2⟩
  have h := Real.convexOn_Gamma.le_on_segment (by norm_num : (1 / 2 : ℝ) ∈ Ioi 0)
    (by norm_num : (1 : ℝ) ∈ Ioi 0) hseg
  rw [Real.Gamma_one_half_eq, Real.Gamma_one] at h
  have h1 : (1 : ℝ) ≤ Real.sqrt Real.pi := by
    rw [Real.one_le_sqrt]
    linarith [Real.pi_gt_three]
  rwa [max_eq_left h1] at h

/-- **(b) `|Γ(x + it)|² ≤ 4π/(1 + t²)²` on `1/2 ≤ x ≤ 1`** (special functions). Avoid the Weierstrass product:
`Γ(x + it) = Γ(x + 2 + it)/((x + it)(x + 1 + it))` (`Complex.Gamma_add_one` twice), and
`|Γ(x + 2 + it)| ≤ Γ(x + 2)` (`Complex.Gamma_eq_integral`, `‖∫ f‖ ≤ ∫ ‖f‖` with `|u^{s-1}| = u^{Re s - 1}`, and
`Complex.Gamma_ofReal`). With `Γ(x + 2) = x(x + 1)Γ(x)`:
`|Γ(x + it)|² ≤ Γ(x)² / ((1 + t²/x²)(1 + t²/(x + 1)²))`. Then `1 + t²/x² ≥ 1 + t²` (`x ≤ 1`),
`1 + t²/(x + 1)² ≥ (1 + t²)/4` (`x + 1 ≤ 2`), and `Γ(x) ≤ Γ(1/2) = √π` on `[1/2, 1]` (convexity,
`Real.convexOn_Gamma`, below the chord from `(1/2, √π)` to `(1, 1)`; `Real.Gamma_one_half_eq`). Checked numerically
on `x ∈ [1/2, 1]`, `t ∈ [0, 40]`: the ratio of the two sides is at most `1/4`. Size: 150–300 lines. -/
theorem norm_Gamma_sq_le {x t : ℝ} (hx1 : 1 / 2 ≤ x) (hx2 : x ≤ 1) :
    ‖Gamma (x + t * I)‖ ^ 2 ≤ 4 * Real.pi / (1 + t ^ 2) ^ 2 := by
  set s : ℂ := x + t * I with hs
  have hx0 : 0 < x := by linarith
  have hsre : s.re = x := by simp [hs]
  have hsim : s.im = t := by simp [hs]
  have hs0 : s ≠ 0 := fun h => by rw [h] at hsre; simp at hsre; linarith
  have hs1 : s + 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h
    simp [hsre] at this
    linarith
  -- `Γ(s + 2) = (s + 1) s Γ(s)`
  have hrec : Gamma (s + 1 + 1) = (s + 1) * (s * Gamma s) := by
    rw [Complex.Gamma_add_one _ hs1, Complex.Gamma_add_one _ hs0]
  have hre2 : (s + 1 + 1).re = x + 1 + 1 := by simp [hsre]
  have hbound : ‖Gamma (s + 1 + 1)‖ ≤ Real.Gamma (x + 1 + 1) := by
    have := Complex.Gamma.norm_le_Gamma_re (z := s + 1 + 1) (by rw [hre2]; linarith)
    rwa [hre2] at this
  have hreal : Real.Gamma (x + 1 + 1) = (x + 1) * (x * Real.Gamma x) := by
    rw [Real.Gamma_add_one (by linarith), Real.Gamma_add_one (by linarith)]
  have hGx := groupB_Gamma_le_sqrt_pi hx1 hx2
  have hGx0 : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx0
  set G := ‖Gamma s‖ with hG
  set a := ‖s‖ with ha
  set b := ‖s + 1‖ with hb
  have hG0 : 0 ≤ G := norm_nonneg _
  have hmain : G * (a * b) ≤ (x + 1) * x * Real.sqrt Real.pi := by
    have h1 : ‖Gamma (s + 1 + 1)‖ = b * (a * G) := by rw [hrec, norm_mul, norm_mul]
    have h2 : (x + 1) * (x * Real.Gamma x) ≤ (x + 1) * x * Real.sqrt Real.pi := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_left hGx (by positivity)
    calc G * (a * b) = ‖Gamma (s + 1 + 1)‖ := by rw [h1]; ring
      _ ≤ _ := hbound.trans (hreal ▸ le_rfl) |>.trans h2
  have ha2 : a ^ 2 = x ^ 2 + t ^ 2 := by
    rw [ha, Complex.sq_norm, Complex.normSq_apply, hsre, hsim]
    ring
  have hb2 : b ^ 2 = (x + 1) ^ 2 + t ^ 2 := by
    rw [hb, Complex.sq_norm, Complex.normSq_apply]
    simp [hsre, hsim]
    ring
  have hpi : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  -- square the main bound
  have hsq : G ^ 2 * (a ^ 2 * b ^ 2) ≤ (x + 1) ^ 2 * x ^ 2 * Real.pi := by
    have h0 : 0 ≤ G * (a * b) := by positivity
    have := pow_le_pow_left₀ h0 hmain 2
    rw [← hpi]
    nlinarith [this]
  have hA : x ^ 2 * (1 + t ^ 2) ≤ a ^ 2 := by
    rw [ha2]
    nlinarith [sq_nonneg t, mul_nonneg (sq_nonneg t) (by nlinarith : (0 : ℝ) ≤ 1 - x ^ 2)]
  have hB : (x + 1) ^ 2 * (1 + t ^ 2) ≤ 4 * b ^ 2 := by
    rw [hb2]
    nlinarith [sq_nonneg t, mul_nonneg (sq_nonneg t) (by nlinarith : (0 : ℝ) ≤ 4 - (x + 1) ^ 2)]
  have hT : 0 < 1 + t ^ 2 := by positivity
  rw [le_div_iff₀ (by positivity)]
  have hxx : 0 < (x + 1) ^ 2 * x ^ 2 := by positivity
  have hkey : (x + 1) ^ 2 * x ^ 2 * (G ^ 2 * (1 + t ^ 2) ^ 2) ≤ (x + 1) ^ 2 * x ^ 2 * (4 * Real.pi) := by
    have hG2 : 0 ≤ G ^ 2 := sq_nonneg G
    have hprod : x ^ 2 * (1 + t ^ 2) * ((x + 1) ^ 2 * (1 + t ^ 2)) ≤ a ^ 2 * (4 * b ^ 2) :=
      mul_le_mul hA hB (by positivity) (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hprod hG2]
  exact le_of_mul_le_mul_left hkey hxx

end GoldbachBoundaries.Paper2.M3
