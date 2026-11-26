import GoldbachBoundaries.T0HInf.MellinAssembly

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
namespace GoldbachBoundaries.T0HInf
open GoldbachBoundaries Paper2
open _root_.GoldbachBoundaries.Phi2HInf (StirlingStrip)

theorem FpPrime_basic {x : ℝ} (hx : 0 < x) : HasDerivAt Fp (FpPrime x) x := by
  exact hasDerivAt_Fp hx

theorem L_basic : ContinuousOn L (Ioi 0) ∧
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 1 ≤ x → ‖L x‖ ≤ K * Real.exp (-x) := by
  exact filteredPrime_basic

theorem t0_mellin_sq {s : ℂ} (hs : 2 < s.re) :
    MellinConvergent (fun x => L x ^ 2) s ∧ mellin (fun x => L x ^ 2) s = Gamma s * T0 s := by
  exact t0_mellin_sq_aux hs

theorem L_mellin {s : ℂ} (hs : 1 < s.re) :
    MellinConvergent L s ∧ mellin L s = (1 - s) * Gamma s * Qcont s := by
  exact L_mellin_aux hs

theorem differentiable_EL : Differentiable ℂ EL := by
  obtain ⟨hcont, K, hK, hbound⟩ := L_basic
  apply TIdentity.differentiable_integral_Ioi_cpow
    ((hcont.mono (by intro x hx; change 0 < x; change 1 < x at hx; linarith)).aestronglyMeasurable measurableSet_Ioi)
  intro x hx
  exact hbound x hx.le

theorem differentiable_E2 : Differentiable ℂ E2 := by
  obtain ⟨hcont, K, hK, hbound⟩ := L_basic
  apply TIdentity.differentiable_integral_Ioi_cpow (C := K ^ 2)
    (((hcont.pow 2).mono (by intro x hx; change 0 < x; change 1 < x at hx; linarith)).aestronglyMeasurable measurableSet_Ioi)
  intro x hx
  have he : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by have : 1 < x := hx; linarith)
  change ‖L x ^ 2‖ ≤ _
  rw [norm_pow]
  calc ‖L x‖ ^ 2 ≤ (K * Real.exp (-x)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hbound x hx.le) 2
    _ = K ^ 2 * Real.exp (-x) * Real.exp (-x) := by ring
    _ ≤ K ^ 2 * Real.exp (-x) * 1 := mul_le_mul_of_nonneg_left he (by positivity)
    _ = K ^ 2 * Real.exp (-x) := mul_one _

end GoldbachBoundaries.T0HInf
