import GoldbachBoundaries.Paper2.M3.Real

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics
namespace GoldbachBoundaries.Paper2.M3
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1
open GoldbachBoundaries.TIdentity

/-- Integrability version of paper 1's exponentially decaying Mellin kernel
(`TIdentity/G9h_HolomorphyIoi.lean`). -/
private lemma A1_integrable_decay {g : ℝ → ℂ} {C : ℝ}
    (hg : AEStronglyMeasurable g (volume.restrict (Ioi (1 : ℝ))))
    (hbound : ∀ t ∈ Ioi (1 : ℝ), ‖g t‖ ≤ C * Real.exp (-t)) (s : ℂ) :
    IntegrableOn (fun t : ℝ => g t * (t : ℂ) ^ (s - 1)) (Ioi (1 : ℝ)) := by
  let f : ℝ → ℂ := (Ioi (1 : ℝ)).indicator g
  have hfmeas : AEStronglyMeasurable f volume :=
    (aestronglyMeasurable_indicator_iff measurableSet_Ioi).2 hg
  have hcont : Continuous (fun t : ℝ => C * Real.exp (-t)) := by fun_prop
  have hlocal : LocallyIntegrableOn f (Ioi 0) := by
    refine (hcont.locallyIntegrable.locallyIntegrableOn (Ioi 0)).mono hfmeas ?_
    exact Eventually.of_forall fun t => by
      by_cases ht : t ∈ Ioi (1 : ℝ)
      · simpa only [f, indicator_of_mem ht] using
          (hbound t ht).trans (Real.le_norm_self (C * Real.exp (-t)))
      · simp only [f, indicator_of_notMem ht, norm_zero]
        exact norm_nonneg _
  have htop : f =O[atTop] (fun t : ℝ => Real.exp (-(1 : ℝ) * t)) := by
    refine IsBigO.of_bound C ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    simpa only [f, indicator_of_mem (show t ∈ Ioi (1 : ℝ) from ht), neg_one_mul,
      Real.norm_of_nonneg (Real.exp_pos _).le] using hbound t ht
  have hbot (b : ℝ) : f =O[𝓝[>] 0] (fun t : ℝ => t ^ (-b)) := by
    refine IsBigO.of_bound 0 ?_
    filter_upwards [(eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
      nhdsWithin_le_nhds] with t ht
    simp [f, indicator_of_notMem (show t ∉ Ioi (1 : ℝ) from not_lt_of_gt ht)]
  have hc := mellinConvergent_of_isBigO_rpow_exp (s := s)
    (by norm_num : (0 : ℝ) < 1) hlocal htop (hbot (s.re - 1)) (by linarith)
  refine (hc.mono_set (Ioi_subset_Ioi (show (0 : ℝ) ≤ 1 by norm_num))).congr_fun
    (fun t ht => ?_) measurableSet_Ioi
  simp only [f, indicator_of_mem ht, smul_eq_mul, mul_comm]

/-- **The integrals on `(1, ∞)`** (unconditional). Paper 1's `TIdentity.Fw_continuousOn_and_le_exp`:
`0 ≤ Θ(t) ≤ Ce^{-t}` for `t ≥ 1` (`TIdentity.Fw_nonneg`), so `|Θ(t)t^{z-1}| ≤ Ce^{-t}t^{Re z - 1}` and
`|Θ(t)²t^{s-1}| ≤ C²e^{-2t}t^{Re s - 1}`, integrable on `(1, ∞)` for every exponent (`integrableOn_rpow_mul_exp_neg_mul_rpow`
or comparison with `e^{-t/2}`); measurability from continuity on `(0, ∞)`. (The same bounds give `differentiable_e1`,
`differentiable_E2` in paper 1.) Size: 60–120 lines. -/
theorem integrableOn_Theta_Ioi :
    (∀ s : ℂ, IntegrableOn (fun t : ℝ => ((Theta t ^ 2 : ℝ) : ℂ) * (t : ℂ) ^ (s - 1)) (Ioi (1 : ℝ))) ∧
      ∀ z : ℂ, IntegrableOn (fun t : ℝ => (Theta t : ℂ) * (t : ℂ) ^ (z - 1)) (Ioi (1 : ℝ)) := by
  change (∀ s : ℂ, IntegrableOn (fun t : ℝ => ((TIdentity.Fw t ^ 2 : ℝ) : ℂ) * (t : ℂ) ^ (s - 1)) (Ioi (1 : ℝ))) ∧
    ∀ z : ℂ, IntegrableOn (fun t : ℝ => (TIdentity.Fw t : ℂ) * (t : ℂ) ^ (z - 1)) (Ioi (1 : ℝ))
  obtain ⟨hc, C, hC⟩ := Fw_continuousOn_and_le_exp
  have hc1 : ContinuousOn Fw (Ioi (1 : ℝ)) :=
    hc.mono (Ioi_subset_Ioi zero_le_one)
  constructor
  · intro s
    refine A1_integrable_decay (g := fun t : ℝ => ((Fw t ^ 2 : ℝ) : ℂ)) (C := C ^ 2) ?_ ?_ s
    · exact (Complex.continuous_ofReal.comp_continuousOn
        (hc1.pow 2)).aestronglyMeasurable
        measurableSet_Ioi
    intro t ht
    have ht1 : 1 ≤ t := le_of_lt ht
    rw [Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
    have h1 : Fw t ^ 2 ≤ (C * Real.exp (-t)) ^ 2 := pow_le_pow_left₀ (Fw_nonneg t) (hC t ht1) 2
    have h2 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have h3 : (C * Real.exp (-t)) ^ 2 = C ^ 2 * Real.exp (-t) * Real.exp (-t) := by ring
    calc Fw t ^ 2 ≤ C ^ 2 * Real.exp (-t) * Real.exp (-t) := h3 ▸ h1
      _ ≤ C ^ 2 * Real.exp (-t) * 1 :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
      _ = C ^ 2 * Real.exp (-t) := mul_one _
  · intro z
    refine A1_integrable_decay (g := fun t : ℝ => (Fw t : ℂ)) (C := C) ?_ ?_ z
    · exact (Complex.continuous_ofReal.comp_continuousOn
        hc1).aestronglyMeasurable measurableSet_Ioi
    intro t ht
    rw [Complex.norm_real, Real.norm_of_nonneg (TIdentity.Fw_nonneg t)]
    exact hC t ht.le

end GoldbachBoundaries.Paper2.M3
