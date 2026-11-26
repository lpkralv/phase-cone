import GoldbachBoundaries.T0HInf.PrimeExplicitValue
import GoldbachBoundaries.T0HInf.ZeroFilter
import GoldbachBoundaries.T0HInf.InverseFilter

/-! The filtered explicit formula with both absolutely convergent remainder integrals. -/
noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
namespace GoldbachBoundaries.T0HInf
open GoldbachBoundaries Paper2
open _root_.GoldbachBoundaries.Phi2HInf (StirlingStrip)

def filteredLambdaIntegral (x : ℝ) : ℂ :=
  VerticalIntegral' (fun z => (x : ℂ) ^ (-z) * ((1 - z) * (Gamma z * negLogDerivZeta z))) (-(1 / 2))

def filteredCorrectionIntegral (x : ℝ) : ℂ :=
  VerticalIntegral' (fun z => (x : ℂ) ^ (-z) * ((1 - z) * (Gamma z * primeCorrection z))) remainderAbscissa

lemma mul_cpow_sub_one {x : ℝ} (hx : 0 < x) (z : ℂ) :
    (x : ℂ) * (x : ℂ) ^ (z - 1) = (x : ℂ) ^ z := by
  rw [cpow_sub _ _ (ofReal_ne_zero.mpr hx.ne'), cpow_one]
  field_simp [ofReal_ne_zero.mpr hx.ne']

lemma remainder_as_integrals (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3)
    (hStir : StirlingStrip) {x : ℝ} (hx : 0 < x) :
    R x = Phi2HInf.c0 + filteredLambdaIntegral x + filteredCorrectionIntegral x := by
  let dZ : ℂ := ∑' ρ : NontrivialZeros,
    Phi2Proof.zeroCoef ρ * (-(ρ : ℂ)) * (x : ℂ) ^ (-(ρ : ℂ) - 1)
  let dV : ℂ := VerticalIntegral' (fun z => -z * (x : ℂ) ^ (-z - 1) *
    (Gamma z * negLogDerivZeta z)) (-(1 / 2))
  let dP : ℂ := VerticalIntegral' (fun z => -z * (x : ℂ) ^ (-z - 1) *
    (Gamma z * primeCorrection z)) remainderAbscissa
  let k : ℂ := -(Real.sqrt Real.pi : ℂ) / 2
  let F : ℝ → ℂ := fun t => -Phi2Proof.zeroSum t + Phi2HInf.c0 + Phi2HInf.V t +
    (t : ℂ) ^ (-(1 : ℂ)) + k * (t : ℂ) ^ (-(1 / 2 : ℂ)) + correctionIntegral t
  have he (t : ℝ) (ht : 0 < t) : (Fp t : ℂ) = F t := by
    rw [Fp_value_explicit hH hZ1 hZ2 hZ3 hStir ht]
    dsimp [F, k]
    ring
  have hV : HasDerivAt Phi2HInf.V dV x := by
    convert! hasDerivAt_inverse_vertical (σ := -(1 / 2)) (f := fun z => Gamma z * negLogDerivZeta z) hx (integrable_Gamma_Lambda_negative hZ1 hZ2 hZ3)
      (integrable_z_Gamma_Lambda_negative hZ1 hZ2 hZ3) using 1
  have hP : HasDerivAt correctionIntegral dP x := by
    convert! hasDerivAt_inverse_vertical (σ := remainderAbscissa) (f := fun z => Gamma z * primeCorrection z) hx (integrable_Gamma_primeCorrection hH hZ1 hZ2 hZ3)
      (integrable_z_Gamma_primeCorrection hH hZ1 hZ2 hZ3) using 1
  have hD : HasDerivAt F (-dZ + dV + (-(1 : ℂ)) * (x : ℂ) ^ (-(1 : ℂ) - 1) +
      k * (-(1 / 2 : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ) - 1)) + dP) x := by
    exact (((((hasDerivAt_zeroSum hZ1 hZ2 hStir hx).neg.add_const Phi2HInf.c0).add hV).add
      (real_cpow_derivative hx (-(1 : ℂ)))).add
      ((real_cpow_derivative hx (-(1 / 2 : ℂ))).const_mul k)).add hP
  have hDF : HasDerivAt (fun t : ℝ => (Fp t : ℂ))
      (-dZ + dV + (-(1 : ℂ)) * (x : ℂ) ^ (-(1 : ℂ) - 1) +
        k * (-(1 / 2 : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ) - 1)) + dP) x :=
    hD.congr_of_eventuallyEq (by filter_upwards [Ioi_mem_nhds hx] with t ht using he t ht)
  have hd := hDF.unique (hasDerivAt_Fp hx).ofReal_comp
  have hxd : (x : ℂ) * (FpPrime x : ℂ) = -(x : ℂ) * dZ + (x : ℂ) * dV -
      (x : ℂ) ^ (-(1 : ℂ)) + k * (-(1 / 2 : ℂ)) * (x : ℂ) ^ (-(1 / 2 : ℂ)) + (x : ℂ) * dP := by
    rw [← hd]
    linear_combination -(mul_cpow_sub_one hx (-(1 : ℂ))) + k * (-(1 / 2 : ℂ)) *
      (mul_cpow_sub_one hx (-(1 / 2 : ℂ)))
  have hVf := filter_inverse_vertical (σ := -(1 / 2)) (f := fun z => Gamma z * negLogDerivZeta z) hx (integrable_Gamma_Lambda_negative hZ1 hZ2 hZ3)
    (integrable_z_Gamma_Lambda_negative hZ1 hZ2 hZ3)
  have hPf := filter_inverse_vertical (σ := remainderAbscissa) (f := fun z => Gamma z * primeCorrection z) hx (integrable_Gamma_primeCorrection hH hZ1 hZ2 hZ3)
    (integrable_z_Gamma_primeCorrection hH hZ1 hZ2 hZ3)
  have hZf := filter_zeroSum hZ1 hZ2 hStir hx
  change Phi2HInf.V x + (x : ℂ) * dV = filteredLambdaIntegral x at hVf
  change correctionIntegral x + (x : ℂ) * dP = filteredCorrectionIntegral x at hPf
  change -Phi2Proof.zeroSum x - (x : ℂ) * dZ = U x at hZf
  have hval := he x hx
  dsimp [F] at hval
  dsimp [R, L]
  simp only [ofReal_add, ofReal_mul]
  dsimp [k, primeSquareCoef] at hxd hval ⊢
  linear_combination hval + hxd + hZf + hVf + hPf

end GoldbachBoundaries.T0HInf
