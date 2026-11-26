import GoldbachBoundaries.Paper2.M4a.H2log

/-!
# Fill (group C): `isBigO_integral_param`

A parametric integral to first order: if `ψ` is holomorphic on a ball about `0 ∈ ℂ²`, then
`∫_0^1 w(t)ψ(tδ, δ) dt - ψ(0)∫_0^1 w = O(δ)`. `ψ` is differentiable at `0`, so `ψ p - ψ 0 = O(‖p‖)`; on `[0, 1]`,
`‖(tδ, δ)‖ = ‖δ‖` (sup norm), and the integrand of the difference is bounded by `(sup |w|) C ‖δ‖`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M4a

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- On `[0, 1]`, the point `(tδ, δ)` of `ℂ × ℂ` has (sup) norm `‖δ‖`. -/
lemma fillC_norm_param {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (δ : ℂ) : ‖((t : ℂ) * δ, δ)‖ = ‖δ‖ := by
  rw [Prod.norm_def]
  have : ‖(t : ℂ) * δ‖ ≤ ‖δ‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1]
    exact mul_le_of_le_one_left (norm_nonneg _) ht.2
  exact max_eq_right this

/-- **A parametric integral to first order** (general). `ψ` is differentiable at `0 ∈ ℂ²`, so
`ψ p - ψ 0 = O(‖p‖)` (`HasFDerivAt.isBigO_sub`): `‖ψ p - ψ 0‖ ≤ C‖p‖` for `‖p‖ < η`. For `|δ| < min η ε` and
`t ∈ [0, 1]`, `‖(tδ, δ)‖ = |δ|` (sup norm), and `t ↦ ψ(tδ, δ)` is continuous (`ψ` is continuous on the ball). So
`‖∫_0^1 w(t)(ψ(tδ, δ) - ψ 0) dt‖ ≤ C|δ| ∫_0^1 |w|` (`intervalIntegral.norm_integral_le_of_norm_le_const` or
`norm_integral_le_integral_norm`), and the left side of the claim is that integral (`integral_sub`,
`integral_mul_const`). Size: 100–200 lines. -/
theorem isBigO_integral_param {ψ : ℂ × ℂ → ℂ} {ε : ℝ} (hε : 0 < ε) (hψ : DifferentiableOn ℂ ψ (ball 0 ε))
    {w : ℝ → ℂ} (hw : Continuous w) :
    (fun δ : ℂ => (∫ t in (0 : ℝ)..1, w t * ψ ((t : ℂ) * δ, δ)) - (∫ t in (0 : ℝ)..1, w t) * ψ 0) =O[𝓝 0]
      fun δ => δ := by
  have hd : DifferentiableAt ℂ ψ 0 := hψ.differentiableAt (ball_mem_nhds 0 hε)
  obtain ⟨C, hC⟩ := hd.hasFDerivAt.isBigO_sub.bound
  obtain ⟨η, hη, hηC⟩ := Metric.eventually_nhds_iff.1 hC
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hw.continuousOn (s := Icc (0 : ℝ) 1))
  apply IsBigO.of_bound (M * C)
  filter_upwards [ball_mem_nhds (0 : ℂ) (lt_min hη hε)] with δ hδ
  rw [mem_ball_zero_iff] at hδ
  have hδη := hδ.trans_le (min_le_left _ _)
  have hδε := hδ.trans_le (min_le_right _ _)
  have hint1 : IntervalIntegrable (fun t : ℝ => w t * ψ ((t : ℂ) * δ, δ)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    apply hw.continuousOn.mul
    refine hψ.continuousOn.comp (by fun_prop : Continuous fun t : ℝ => ((t : ℂ) * δ, δ)).continuousOn ?_
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    rw [mem_ball_zero_iff, fillC_norm_param ht]
    exact hδε
  have hint2 : IntervalIntegrable (fun t : ℝ => w t) volume 0 1 := hw.intervalIntegrable _ _
  have heq : (∫ t in (0 : ℝ)..1, w t * ψ ((t : ℂ) * δ, δ)) - (∫ t in (0 : ℝ)..1, w t) * ψ 0
      = ∫ t in (0 : ℝ)..1, w t * (ψ ((t : ℂ) * δ, δ) - ψ 0) := by
    rw [← intervalIntegral.integral_mul_const, ← intervalIntegral.integral_sub hint1 (hint2.mul_const _)]
    congr 1
    funext t
    ring
  rw [heq]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1) (C := M * C * ‖δ‖)
    (f := fun t => w t * (ψ ((t : ℂ) * δ, δ) - ψ 0)) ?_
  · simpa using hb
  intro t ht
  rw [uIoc_of_le zero_le_one] at ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
  rw [norm_mul]
  have h1 := hM t ht'
  have h2 : ‖ψ ((t : ℂ) * δ, δ) - ψ 0‖ ≤ C * ‖δ‖ := by
    have := hηC (y := ((t : ℂ) * δ, δ)) (by rw [dist_zero_right, fillC_norm_param ht']; exact hδη)
    rwa [sub_zero, fillC_norm_param ht'] at this
  calc ‖w t‖ * ‖ψ ((t : ℂ) * δ, δ) - ψ 0‖ ≤ M * (C * ‖δ‖) :=
        mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
    _ = M * C * ‖δ‖ := by ring

end GoldbachBoundaries.Paper2.M4a
