import GoldbachBoundaries.Paper2.M6.Defs

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M6

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **`P̃ = P` on `Re z > 1`** (unconditional). For `Re z > 1`, `t ↦ P(z + t)` has derivative
`-Q(z + t) = -Qcont(z + t)` on `[0, 2]`, continuous in `t`; the fundamental theorem of calculus gives
`∫_0^2 Qcont(z + t) dt = P(z) - P(z + 2)`. -/
theorem Ptil_eqOn_P : EqOn Ptil P (halfPlane 1) := by
  intro z hz
  simp only [halfPlane, mem_ofPred_eq] at hz
  have hre : ∀ t : ℝ, 0 ≤ t → 1 < (z + t).re := fun t ht => by simp; linarith
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 2,
      HasDerivAt (fun t : ℝ => P (z + t)) (-Qcont (z + t)) t := by
    intro t ht
    rw [uIcc_of_le (by norm_num)] at ht
    have h1 : HasDerivAt (fun w : ℂ => P (z + w)) (-Q (z + t)) (t : ℂ) := by
      have := (hasDerivAt_P (show z + (t : ℂ) ∈ halfPlane 1 from hre t ht.1)).comp (t : ℂ)
        ((hasDerivAt_id (t : ℂ)).const_add z)
      simpa [Function.comp_def] using this
    rw [TIdentity.Qcont_eq_Q_of_one_lt (hre t ht.1)]
    exact h1.comp_ofReal
  have hcont : ContinuousOn (fun t : ℝ => -Qcont (z + t)) (uIcc 0 2) := by
    intro t ht
    rw [uIcc_of_le (by norm_num)] at ht
    have hc : ContinuousAt (fun t : ℝ => Qcont (z + t)) t :=
      ContinuousAt.comp (f := fun t : ℝ => z + (t : ℂ)) (g := Qcont)
        (TIdentity.analyticAt_Qcont_of_one_lt (hre t ht.1)).continuousAt (by fun_prop)
    exact hc.neg.continuousWithinAt
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  rw [intervalIntegral.integral_neg] at hftc
  simp only [ofReal_ofNat, ofReal_zero, add_zero] at hftc
  unfold Ptil
  linear_combination -hftc

end GoldbachBoundaries.Paper2.M6
