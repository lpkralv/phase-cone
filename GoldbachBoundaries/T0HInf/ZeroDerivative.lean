import GoldbachBoundaries.T0HInf.ZeroCoefficients
import GoldbachBoundaries.T0HInf.InverseMellinDerivative

/-! Absolute differentiation of the old all-zero series supplies the filtered coefficients. -/
noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
namespace GoldbachBoundaries.T0HInf
open GoldbachBoundaries Paper2
open _root_.GoldbachBoundaries.Phi2HInf (StirlingStrip)

lemma summable_norm_rho_zeroCoef (hZ1 : Z1) (hZ2 : Z2) (hStir : StirlingStrip) :
    Summable (fun ρ : NontrivialZeros => ‖(ρ : ℂ) * Phi2Proof.zeroCoef ρ‖) := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_
    ((summable_norm_zeroCoef hZ1 hZ2).add (Phi2HInf.summable_norm_zeroCoef_hinf hZ1 hZ2 hStir))
  intro ρ
  have he : (ρ : ℂ) * Phi2Proof.zeroCoef ρ = zeroCoef ρ + Phi2Proof.zeroCoef ρ := by
    dsimp [zeroCoef]
    ring
  rw [he]
  exact norm_add_le _ _

lemma rpow_strip_local_bound {d y r : ℝ} (hd : 0 < d) (hy : d ≤ y)
    (hr0 : 0 ≤ r) (hr2 : r ≤ 2) : y ^ (-r) ≤ 1 + d ^ (-(2 : ℝ)) := by
  have hy0 : 0 < y := hd.trans_le hy
  by_cases hy1 : 1 ≤ y
  · have hh : y ^ (-r) ≤ 1 := by
      simpa using Real.rpow_le_rpow_of_exponent_le hy1 (neg_nonpos.mpr hr0)
    linarith [Real.rpow_nonneg hd.le (-(2 : ℝ))]
  · have h1 := Real.rpow_le_rpow_of_exponent_ge hy0 (not_le.mp hy1).le (neg_le_neg hr2)
    have h2 := Real.rpow_le_rpow_of_nonpos hd hy (by norm_num : -(2 : ℝ) ≤ 0)
    linarith

lemma hasDerivAt_zeroSum (hZ1 : Z1) (hZ2 : Z2) (hStir : StirlingStrip)
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt Phi2Proof.zeroSum
      (∑' ρ : NontrivialZeros, Phi2Proof.zeroCoef ρ * (-(ρ : ℂ)) * (x : ℂ) ^ (-(ρ : ℂ) - 1)) x := by
  let f (ρ : NontrivialZeros) (t : ℝ) := Phi2Proof.zeroCoef ρ * (t : ℂ) ^ (-(ρ : ℂ))
  let f' (ρ : NontrivialZeros) (t : ℝ) := Phi2Proof.zeroCoef ρ * (-(ρ : ℂ)) * (t : ℂ) ^ (-(ρ : ℂ) - 1)
  let b (ρ : NontrivialZeros) := ‖(ρ : ℂ) * Phi2Proof.zeroCoef ρ‖ * (1 + (x / 2) ^ (-(2 : ℝ)))
  have hx2 : 0 < x / 2 := by linarith
  have hder (ρ : NontrivialZeros) (t : ℝ) (ht : t ∈ Ioi (x / 2)) : HasDerivAt (f ρ) (f' ρ t) t := by
    have ht0 : 0 < t := hx2.trans ht
    convert! (real_cpow_derivative ht0 (-(ρ : ℂ))).const_mul (Phi2Proof.zeroCoef ρ) using 1 <;> dsimp [f, f'] <;> ring
  have hbound (ρ : NontrivialZeros) (t : ℝ) (ht : t ∈ Ioi (x / 2)) : ‖f' ρ t‖ ≤ b ρ := by
    have ht0 : 0 < t := hx2.trans ht
    dsimp [f', b]
    rw [norm_mul, norm_mul, norm_neg, norm_cpow_eq_rpow_re_of_pos ht0]
    simp only [sub_re, neg_re, one_re]
    rw [show -(ρ : ℂ).re - 1 = -((ρ : ℂ).re + 1) by ring, norm_mul, mul_comm ‖(ρ : ℂ)‖]
    exact mul_le_mul_of_nonneg_left (rpow_strip_local_bound hx2 ht.le
      (by linarith [ρ.2.2.1]) (by linarith [ρ.2.2.2])) (by positivity)
  have hsum : Summable (fun ρ => f ρ x) := by
    apply Summable.of_norm_bounded ((Phi2HInf.summable_norm_zeroCoef_hinf hZ1 hZ2 hStir).mul_right
      (1 + x ^ (-(2 : ℝ))))
    intro ρ
    dsimp [f]
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx, neg_re]
    exact mul_le_mul_of_nonneg_left (rpow_strip_local_bound hx le_rfl ρ.2.2.1.le
      (by linarith [ρ.2.2.2])) (norm_nonneg _)
  have h := hasDerivAt_tsum_of_isPreconnected ((summable_norm_rho_zeroCoef hZ1 hZ2 hStir).mul_right _)
    isOpen_Ioi (convex_Ioi (x / 2)).isPreconnected hder hbound
    (show x ∈ Ioi (x / 2) by change x / 2 < x; linarith) hsum
    (show x ∈ Ioi (x / 2) by change x / 2 < x; linarith)
  convert! h using 1

end GoldbachBoundaries.T0HInf
