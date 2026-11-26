import GoldbachBoundaries.Paper2.M3.Real

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
namespace GoldbachBoundaries.Paper2.M3
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- The integrability construction is adapted from paper 1's
`TIdentity/G9f_SplitT.lean`, `Gamma_mul_T_eq_split`. -/
private lemma A1_hsq_complex {s : ℂ} (hs : 2 < s.re) :
    IntegrableOn (fun t : ℝ => ((hErr t ^ 2 : ℝ) : ℂ) * (t : ℂ) ^ (s - 1))
      (Ioc (0 : ℝ) 1) := by
  open GoldbachBoundaries.TIdentity in
    have hadd : ∀ t : ℝ, 0 < t → ∀ w : ℂ, (t : ℂ) ^ (w + 1) = (t : ℂ) ^ w * t := by
      intro t ht w
      rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr ht.ne'), Complex.cpow_one]
    have hc1 : ∀ t : ℝ, 0 < t → (t : ℂ) ^ (s - 1 - 1) = (t : ℂ) ^ (s - 3) * t := by
      intro t ht
      rw [← hadd t ht]
      ring_nf
    have hc2 : ∀ t : ℝ, 0 < t → (t : ℂ) ^ (s - 1) = (t : ℂ) ^ (s - 3) * t * t := by
      intro t ht
      rw [← hc1 t ht, ← hadd t ht]
      ring_nf
    obtain ⟨hconv2, hmel2⟩ := mellin_Fw_sq hs
    have hs1 : 1 < (s - 1).re := by simp; linarith
    have hconv1 := (mellin_Fw hs1).1
    -- A: `t^{s-3}`.
    have hA : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 3)) (Ioc (0 : ℝ) 1) :=
      TIdentity.integrableOn_Ioc_cpow_of_neg_one_lt (by simp; linarith)
    -- B: `h(t) t^{(s-1)-1} = F(t) t^{(s-1)-1} - t^{s-3}`.
    have hB : IntegrableOn (fun t : ℝ => (hErr t : ℂ) * (t : ℂ) ^ (s - 1 - 1)) (Ioc (0 : ℝ) 1) := by
      refine ((hconv1.mono_set Ioc_subset_Ioi_self).sub hA).congr_fun (fun t ht => ?_)
        measurableSet_Ioc
      have ht0 : 0 < t := ht.1
      have htne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0.ne'
      simp only [Pi.sub_apply, hErr, Theta_eq_Fw, smul_eq_mul, hc1 t ht0]
      push_cast
      field_simp
    -- Pointwise expansion `t^{s-1} F² = h² t^{s-1} + 2 h t^{(s-1)-1} + t^{s-3}` on `(0, 1]`.
    have hpt : ∀ t ∈ Ioc (0 : ℝ) 1, (t : ℂ) ^ (s - 1) • ((Fw t ^ 2 : ℝ) : ℂ)
        = ((hErr t ^ 2 : ℝ) : ℂ) * (t : ℂ) ^ (s - 1)
          + 2 * ((hErr t : ℂ) * (t : ℂ) ^ (s - 1 - 1)) + (t : ℂ) ^ (s - 3) := by
      intro t ht
      have ht0 : 0 < t := ht.1
      have htne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0.ne'
      simp only [hErr, Theta_eq_Fw, smul_eq_mul, hc1 t ht0, hc2 t ht0]
      push_cast
      field_simp
      ring
    -- C: `h² t^{s-1} = t^{s-1} F² - 2 h t^{(s-1)-1} - t^{s-3}`.
    have hC : IntegrableOn (fun t : ℝ => ((hErr t ^ 2 : ℝ) : ℂ) * (t : ℂ) ^ (s - 1))
        (Ioc (0 : ℝ) 1) := by
      refine (((hconv2.mono_set Ioc_subset_Ioi_self).sub (hB.const_mul 2)).sub hA).congr_fun
        (fun t ht => ?_) measurableSet_Ioc
      simp only [Pi.sub_apply, hpt t ht]
      ring
    exact hC

/-- **`𝓜(x)` converges for `x > 2`** (unconditional). On `(0, 1]`, `h² t^{x-1} = Θ²t^{x-1} - 2Θt^{x-2} + t^{x-3}`
(`t > 0`); `Θ²t^{x-1}` and `Θt^{x-2}` are integrable on `(0, ∞)` by paper 1's `TIdentity.mellin_Fw_sq` (at `x > 2`)
and `TIdentity.mellin_Fw` (at `x - 1 > 1`) (`MellinConvergent` is `IntegrableOn (t^{s-1} • f) (Ioi 0)`; restrict to
`Ioc 0 1`, take real parts or norms since everything is real and non-negative), and `t^{x-3}` is integrable on `(0, 1]`
(`intervalIntegral.intervalIntegrable_rpow'`, `x - 3 > -1`). Size: 60–150 lines. -/
theorem mem_mellinConvSet_of_two_lt {x : ℝ} (hx : 2 < x) : x ∈ mellinConvSet := by
  have hc := (A1_hsq_complex (s := (x : ℂ)) (by simpa using hx)).norm
  apply Integrable.congr hc
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _),
    Complex.norm_cpow_eq_rpow_re_of_pos ht.1]
  simp

end GoldbachBoundaries.Paper2.M3
