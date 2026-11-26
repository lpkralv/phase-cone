import GoldbachBoundaries.Paper2.M3.Numerics

/-!
# Fill: `exp_neg_one_le_Gamma`

`Γ(x) = ∫_0^∞ e^{-u} u^{x-1} du ≥ ∫_1^∞ e^{-u} u^{x-1} du ≥ ∫_1^∞ e^{-u} du = e⁻¹` for `x ≥ 1`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M3

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **(c) `Γ(x) ≥ e⁻¹` for `x ≥ 1`** (special functions). `Γ(x) = ∫_0^∞ u^{x-1}e^{-u} du ≥ ∫_1^∞ u^{x-1} e^{-u} du ≥
∫_1^∞ e^{-u} du = e⁻¹` (`Real.Gamma_eq_integral`, `setIntegral_mono_set` for the non-negative integrand,
`u^{x-1} ≥ 1` on `u ≥ 1`, `integral_exp_neg_Ioi`). Size: 50–100 lines. -/
theorem exp_neg_one_le_Gamma {x : ℝ} (hx : 1 ≤ x) : Real.exp (-1) ≤ Real.Gamma x := by
  have hx0 : 0 < x := by linarith
  have hint := Real.GammaIntegral_convergent hx0
  rw [Real.Gamma_eq_integral hx0, ← integral_exp_neg_Ioi 1]
  calc ∫ u in Ioi (1 : ℝ), Real.exp (-u)
      ≤ ∫ u in Ioi (1 : ℝ), Real.exp (-u) * u ^ (x - 1) := by
        refine setIntegral_mono_on ?_ (hint.mono_set (Ioi_subset_Ioi zero_le_one)) measurableSet_Ioi
          fun u hu => ?_
        · exact integrableOn_exp_neg_Ioi 1
        · have hu1 : (1 : ℝ) ≤ u := le_of_lt hu
          have : 1 ≤ u ^ (x - 1) := Real.one_le_rpow hu1 (by linarith)
          have he := Real.exp_pos (-u)
          nlinarith
    _ ≤ ∫ u in Ioi (0 : ℝ), Real.exp (-u) * u ^ (x - 1) := by
        refine setIntegral_mono_set hint ?_ (Filter.Eventually.of_forall (Ioi_subset_Ioi zero_le_one))
        refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun u hu => ?_)
        exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (le_of_lt hu) _)

end GoldbachBoundaries.Paper2.M3
