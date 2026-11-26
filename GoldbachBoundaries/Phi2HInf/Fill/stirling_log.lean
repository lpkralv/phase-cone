import GoldbachBoundaries.Phi2HInf.Proof.Defs
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-! Principal-log identities and uniform Taylor errors used by the strip cone. -/
noncomputable section
open Complex Filter Topology Set Metric
namespace GoldbachBoundaries.Phi2HInf

/-- A small perturbation of either imaginary ray stays on the principal branch. -/
theorem log_ray_mul {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) {u : ℝ} (hu : 0 < u) :
    log ((u : ℂ) * (I * (1 + w))) =
      (Real.log u : ℂ) + (Real.pi : ℂ) / 2 * I + log (1 + w) ∧
    log ((u : ℂ) * (-I * (1 + w))) =
      (Real.log u : ℂ) - (Real.pi : ℂ) / 2 * I + log (1 + w) := by
  have hre : 0 < (1 + w).re := by
    have := (abs_le.mp (abs_re_le_norm w)).1
    simp only [add_re, one_re]
    linarith
  have hn : 1 + w ≠ 0 := by intro h; rw [h] at hre; simp at hre
  have ha := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre)
  have hp := Real.pi_pos
  have ht := abs_lt.mp ha
  constructor
  · rw [log_ofReal_mul hu (mul_ne_zero I_ne_zero hn),
      log_mul I_ne_zero hn (by simp only [mem_Ioc, arg_I]; constructor <;> linarith), log_I]
    ring
  · rw [log_ofReal_mul hu (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hn),
      log_mul (neg_ne_zero.mpr I_ne_zero) hn
        (by simp only [mem_Ioc, arg_neg_I]; constructor <;> linarith), log_neg_I]
    ring

/-- On the half-unit disc the quadratic Taylor error has constant one. -/
theorem log_ray_remainder {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) :
    ‖log (1 + w) - w‖ ≤ ‖w‖ ^ 2 := by
  have hw1 : ‖w‖ < 1 := by linarith
  have hi : (1 - ‖w‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith : 0 < 1 - ‖w‖) (by norm_num : (0 : ℝ) < 2)]
    norm_num
    linarith
  calc
    ‖log (1 + w) - w‖ ≤ ‖w‖ ^ 2 * (1 - ‖w‖)⁻¹ / 2 :=
      norm_log_one_add_sub_self_le hw1
    _ ≤ ‖w‖ ^ 2 * 2 / 2 := by gcongr
    _ = ‖w‖ ^ 2 := by ring

end GoldbachBoundaries.Phi2HInf
