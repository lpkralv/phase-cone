import GoldbachBoundaries.T0HInf.ZeroDerivative

/-! The Euler filter turns the old Lambda coefficients into `zeroCoef`. -/
noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
namespace GoldbachBoundaries.T0HInf
open GoldbachBoundaries Paper2
open _root_.GoldbachBoundaries.Phi2HInf (StirlingStrip)

lemma summable_zero_cpow_all {a : NontrivialZeros → ℂ}
    (ha : Summable (fun ρ => ‖a ρ‖)) {x : ℝ} (hx : 0 < x) :
    Summable (fun ρ => a ρ * (x : ℂ) ^ (-(ρ : ℂ))) := by
  apply Summable.of_norm_bounded (ha.mul_right (1 + x ^ (-(2 : ℝ))))
  intro ρ
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx, neg_re]
  exact mul_le_mul_of_nonneg_left (rpow_strip_local_bound hx le_rfl ρ.2.2.1.le
    (by linarith [ρ.2.2.2])) (norm_nonneg _)

lemma filter_zeroSum (hZ1 : Z1) (hZ2 : Z2) (hStir : StirlingStrip)
    {x : ℝ} (hx : 0 < x) :
    -Phi2Proof.zeroSum x - (x : ℂ) *
      (∑' ρ : NontrivialZeros, Phi2Proof.zeroCoef ρ * (-(ρ : ℂ)) * (x : ℂ) ^ (-(ρ : ℂ) - 1)) = U x := by
  have ha := summable_zero_cpow_all (summable_norm_zeroCoef hZ1 hZ2) hx
  have hb := summable_zero_cpow_all (Phi2HInf.summable_norm_zeroCoef_hinf hZ1 hZ2 hStir) hx
  have he : (x : ℂ) *
      (∑' ρ : NontrivialZeros, Phi2Proof.zeroCoef ρ * (-(ρ : ℂ)) * (x : ℂ) ^ (-(ρ : ℂ) - 1)) =
        -(U x + Phi2Proof.zeroSum x) := by
    rw [← tsum_mul_left, U, Phi2Proof.zeroSum, ← ha.tsum_add hb, ← tsum_neg]
    apply tsum_congr
    intro ρ
    rw [cpow_sub _ _ (ofReal_ne_zero.mpr hx.ne'), cpow_one]
    dsimp [zeroCoef]
    field_simp [ofReal_ne_zero.mpr hx.ne']
    <;> ring
  rw [he]
  ring

end GoldbachBoundaries.T0HInf
