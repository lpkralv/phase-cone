import GoldbachBoundaries.T0HInf.PrimeCorrectionBounds
import GoldbachBoundaries.T0HInf.InverseMellinDerivative

/-! Absolute integrability, including one extra Mellin variable for real differentiation. -/
noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
namespace GoldbachBoundaries.T0HInf
open GoldbachBoundaries Paper2

lemma continuous_primeCorrection_line (hH : Hinf) (hZ1 : Z1) :
    Continuous (fun y : ℝ => primeCorrection (remainderAbscissa + y * I)) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  apply (analyticAt_primeCorrection hH hZ1 (by simp) (by
    intro he
    have := congrArg Complex.re he
    simp at this
    linarith [(cutoff_bounds hH).2.2.1])).continuousAt.comp
  fun_prop

lemma integrable_Gamma_primeCorrection (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) :
    Integrable (fun y : ℝ => Gamma (remainderAbscissa + y * I) *
      primeCorrection (remainderAbscissa + y * I)) := by
  obtain ⟨K, -, hK⟩ := primeCorrection_line_bound hH hZ1 hZ2 hZ3
  exact TIdentity.integrable_Gamma_mul_of_bound (by linarith [(cutoff_bounds hH).2.1])
    (continuous_primeCorrection_line hH hZ1) hK

lemma integrable_z_Gamma_primeCorrection (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) :
    Integrable (fun y : ℝ => (remainderAbscissa + y * I) *
      (Gamma (remainderAbscissa + y * I) * primeCorrection (remainderAbscissa + y * I))) := by
  obtain ⟨K, -, hK⟩ := primeCorrection_line_bound hH hZ1 hZ2 hZ3
  have ha : 0 < remainderAbscissa := by linarith [(cutoff_bounds hH).2.1]
  have hi := TIdentity.integrable_Gamma_mul_of_bound (σ := remainderAbscissa + 1)
    (by linarith) (continuous_primeCorrection_line hH hZ1) hK
  convert! hi using 1
  ext y
  have hz : (remainderAbscissa : ℂ) + y * I ≠ 0 := by
    intro he
    have := congrArg Complex.re he
    simp at this
    linarith
  rw [show ((remainderAbscissa + 1 : ℝ) : ℂ) + y * I =
    ((remainderAbscissa : ℂ) + y * I) + 1 by push_cast; ring, Gamma_add_one _ hz]
  ring

lemma integrable_Gamma_Lambda_negative (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) :
    Integrable (fun y : ℝ => Gamma (((-(1 / 2 : ℝ) : ℝ) : ℂ) + y * I) *
      negLogDerivZeta (((-(1 / 2 : ℝ) : ℝ) : ℂ) + y * I)) := by
  simpa only [Phi2Proof.kernelL, ofReal_one, one_cpow, one_mul] using
    Phi2HInf.integrable_kernelL_negative hZ1 hZ2 hZ3 (x := 1) zero_lt_one

lemma integrable_z_Gamma_Lambda_negative (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) :
    Integrable (fun y : ℝ => (((-(1 / 2 : ℝ) : ℝ) : ℂ) + y * I) *
      (Gamma (((-(1 / 2 : ℝ) : ℝ) : ℂ) + y * I) * negLogDerivZeta (((-(1 / 2 : ℝ) : ℝ) : ℂ) + y * I))) := by
  obtain ⟨K, hK, hb⟩ := Phi2HInf.negative_line_log_bound hZ1 hZ2 hZ3
  have hc := Phi2Proof.fillB_continuous_negLogDerivZeta_line (σ := -(1 / 2)) (by norm_num)
    (fun y => Phi2HInf.zeta_ne_zero_negative_strip (by simp) (by norm_num))
  have hbound (y : ℝ) : ‖negLogDerivZeta (((-(1 / 2 : ℝ) : ℝ) : ℂ) + y * I)‖ ≤ (2 * K) * (1 + |y|) := by
    have hl : Real.log (|y| + 3) ≤ 2 * (1 + |y|) := by
      have := Real.log_le_sub_one_of_pos (show 0 < |y| + 3 by positivity)
      linarith [abs_nonneg y]
    exact (hb y).trans (by nlinarith [mul_le_mul_of_nonneg_left hl hK])
  have hi := TIdentity.integrable_Gamma_mul_of_bound (σ := 1 / 2) (by norm_num) hc hbound
  convert! hi using 1
  ext y
  have hz : ((-(1 / 2 : ℝ) : ℝ) : ℂ) + y * I ≠ 0 := by
    intro he
    have := congrArg Complex.re he
    norm_num at this
  rw [show ((1 / 2 : ℝ) : ℂ) + y * I = (((-(1 / 2 : ℝ) : ℝ) : ℂ) + y * I) + 1 by push_cast; ring,
    Gamma_add_one _ hz]
  ring

lemma integrable_Gamma_primeCorrection_two :
    Integrable (fun y : ℝ => Gamma ((2 : ℝ) + y * I) * primeCorrection ((2 : ℝ) + y * I)) := by
  have hQ := TIdentity.integrable_Gamma_mul_Qcont_of_one_lt (σ := 2) (by norm_num)
  have hM := Phi2Proof.FillA.integrable_Gamma_mul_negLogDerivZeta_of_one_lt (σ := 2) (by norm_num)
  convert! hQ.sub hM using 1
  ext y
  dsimp [primeCorrection]
  ring

end GoldbachBoundaries.T0HInf
