import GoldbachBoundaries.T0HInf.FilteredRemainder

/-! The explicit remainder is bounded by the two absolute vertical integrals. -/
noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
namespace GoldbachBoundaries.T0HInf
open GoldbachBoundaries Paper2
open _root_.GoldbachBoundaries.Phi2HInf (StirlingStrip)

lemma remainder_bound_aux (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3)
    (hStir : StirlingStrip) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ Ioc (0 : ℝ) 1, ‖R x‖ ≤ K * x ^ (-remainderAbscissa) := by
  let K₀ : ℝ := (1 / (2 * Real.pi)) * ∫ y : ℝ,
    ‖(1 - (((-(1 / 2 : ℝ) : ℝ) : ℂ) + y * I)) * (Gamma (((-(1 / 2 : ℝ) : ℝ) : ℂ) + y * I) *
      negLogDerivZeta (((-(1 / 2 : ℝ) : ℝ) : ℂ) + y * I))‖
  let K₁ : ℝ := (1 / (2 * Real.pi)) * ∫ y : ℝ,
    ‖(1 - (remainderAbscissa + y * I)) * (Gamma (remainderAbscissa + y * I) *
      primeCorrection (remainderAbscissa + y * I))‖
  have hK₀ : 0 ≤ K₀ := by dsimp [K₀]; positivity
  have hK₁ : 0 ≤ K₁ := by dsimp [K₁]; positivity
  refine ⟨‖Phi2HInf.c0‖ + K₀ + K₁, by positivity, ?_⟩
  intro x hx
  have ha : 0 < remainderAbscissa := by linarith [(cutoff_bounds hH).2.1]
  have hp : 1 ≤ x ^ (-remainderAbscissa) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hx.1 hx.2 (by linarith)
  have hhalf : x ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hx.1.le hx.2 (by norm_num)
  have hV : ‖filteredLambdaIntegral x‖ ≤ K₀ * x ^ (1 / 2 : ℝ) := by
    simpa only [filteredLambdaIntegral, K₀, neg_neg] using norm_inverse_vertical_le (σ := -(1 / 2)) hx.1
      (fun z => (1 - z) * (Gamma z * negLogDerivZeta z))
  have hP : ‖filteredCorrectionIntegral x‖ ≤ K₁ * x ^ (-remainderAbscissa) :=
    norm_inverse_vertical_le hx.1 (fun z => (1 - z) * (Gamma z * primeCorrection z))
  rw [remainder_as_integrals hH hZ1 hZ2 hZ3 hStir hx.1]
  calc
    _ ≤ ‖Phi2HInf.c0‖ + ‖filteredLambdaIntegral x‖ + ‖filteredCorrectionIntegral x‖ := norm_add₃_le
    _ ≤ ‖Phi2HInf.c0‖ + K₀ * x ^ (1 / 2 : ℝ) + K₁ * x ^ (-remainderAbscissa) := by linarith
    _ ≤ (‖Phi2HInf.c0‖ + K₀ + K₁) * x ^ (-remainderAbscissa) := by
      nlinarith [mul_le_mul_of_nonneg_left hhalf hK₀,
        mul_le_mul_of_nonneg_left hp (norm_nonneg Phi2HInf.c0),
        mul_le_mul_of_nonneg_left hp hK₀]

end GoldbachBoundaries.T0HInf
