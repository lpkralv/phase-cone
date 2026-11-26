import GoldbachBoundaries.T0HInf.CorrectionContour
import GoldbachBoundaries.T0HInf.FpBasic

/-! Combine the existing all-zero Lambda formula with the prime-square correction. -/
noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
namespace GoldbachBoundaries.T0HInf
open GoldbachBoundaries Paper2
open _root_.GoldbachBoundaries.Phi2HInf (StirlingStrip)

lemma inverse_primeCorrection_split {x : ℝ} (hx : 0 < x) :
    VerticalIntegral' (TIdentity.kernelQ x) 2 = VerticalIntegral' (Phi2Proof.kernelL x) 2 +
      VerticalIntegral' (correctionKernel x) 2 := by
  have hM := Phi2Proof.FillA.integrable_kernelL hx
    (Phi2Proof.FillA.integrable_Gamma_mul_negLogDerivZeta_of_one_lt (σ := 2) (by norm_num))
  have hP := integrable_inverse_kernel (σ := 2) (f := fun z => Gamma z * primeCorrection z) hx integrable_Gamma_primeCorrection_two
  have he : TIdentity.kernelQ x = fun z => Phi2Proof.kernelL x z + correctionKernel x z := by
    ext z
    dsimp [TIdentity.kernelQ, Phi2Proof.kernelL, correctionKernel, primeCorrection]
    ring
  rw [he]
  simp only [VerticalIntegral', VerticalIntegral, smul_eq_mul]
  change Integrable (fun y : ℝ => correctionKernel x ((2 : ℝ) + y * I)) at hP
  have hadd := integral_add hM hP
  rw [hadd]
  ring

lemma Fp_value_explicit (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3)
    (hStir : StirlingStrip) {x : ℝ} (hx : 0 < x) :
    (Fp x : ℂ) = -Phi2Proof.zeroSum x + Phi2HInf.c0 + Phi2HInf.V x +
      (x : ℂ) ^ (-(1 : ℂ)) - (Real.sqrt Real.pi : ℂ) / 2 * (x : ℂ) ^ (-(1 / 2 : ℂ)) +
      correctionIntegral x := by
  rw [Fp, TIdentity.Fw_eq_verticalIntegral' (c := 2) (by norm_num) hx,
    inverse_primeCorrection_split hx,
    Phi2HInf.verticalIntegral'_kernelL_regularized hZ1 hZ2 hZ3 hStir hx,
    correction_contour_shift hH hZ1 hZ2 hZ3 hx]
  simp only [Phi2HInf.V, cpow_neg_one, one_div]
  ring

end GoldbachBoundaries.T0HInf
