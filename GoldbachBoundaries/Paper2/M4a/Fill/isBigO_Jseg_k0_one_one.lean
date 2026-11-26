import GoldbachBoundaries.Paper2.M4a.Fill.GroupCCommon

/-!
# Fill (group C): `isBigO_Jseg_k0_one_one`

With `δ = s - 2`: `J_{11}(2 + δ) = δ³ ∫_0^1 t(1 - t) ψ(tδ, δ) dt`, `ψ(u, δ) = K_{2+δ}(1 + u)`, `ψ(0) = 1`,
`∫_0^1 t(1 - t) = 1/6`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M4a

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- `∫_0^1 t(1 - t) dt = 1/6` (complex-valued). -/
lemma fillC_integral_t_one_sub_t : (∫ t in (0 : ℝ)..1, (t : ℂ) * (1 - (t : ℂ))) = 1 / 6 := by
  have e : (fun t : ℝ => (t : ℂ) * (1 - (t : ℂ))) = fun t : ℝ => (t : ℂ) ^ 1 - (t : ℂ) ^ 2 := by
    funext t; ring
  rw [e, intervalIntegral.integral_sub ((by fun_prop : Continuous fun t : ℝ => (t : ℂ) ^ 1).intervalIntegrable 0 1)
    ((by fun_prop : Continuous fun t : ℝ => (t : ℂ) ^ 2).intervalIntegrable 0 1), fillC_integral_pow,
    fillC_integral_pow]
  norm_num

/-- `K_2(1) = Γ(1)Γ(1)/Γ(2) = 1`. -/
lemma fillC_KerS_two_one : KerS 2 1 = 1 := by
  unfold KerS
  rw [show (2 : ℂ) - 1 = 1 by norm_num, show (2 : ℂ) = 1 + 1 by norm_num,
    Complex.Gamma_add_one 1 one_ne_zero, Complex.Gamma_one]
  norm_num

/-- **`X₂ = J_{11}` for `k₀` at `2`** (no RH). With `δ = s - 2`: `Jseg Aff.idL k0 1 1 s = δ ∫_0^1 k₀(1 + tδ, 2 + δ) dt`,
`k₀(1 + tδ, 2 + δ) = K_{2+δ}(1 + tδ) · tδ · δ(1 - t)`, so `J_{11} = δ³ ∫_0^1 t(1 - t) ψ(tδ, δ) dt` with
`ψ(u, δ) = KerS (2 + δ) (1 + u)`, `ψ 0 = Γ(1)Γ(1)/Γ(2) = 1`, `∫_0^1 t(1 - t) = 1/6`. As `isBigO_Jseg_kr_one_b`, with
`isBigO_integral_param` for `w t = t(1 - t)`. Size: 100–200 lines. -/
theorem isBigO_Jseg_k0_one_one :
    (fun s => Jseg Aff.idL k0 1 1 s - (s - 2) ^ 3 / 6) =O[𝓝 2] fun s => (s - 2) ^ 4 := by
  have hw : 0 < (1 : ℂ).re := by simp
  have hsw : 0 < ((2 : ℂ) - 1).re := by norm_num
  set ψ : ℂ × ℂ → ℂ := fun p => KerS (2 + p.2) (1 + p.1) with hψdef
  have hψ : DifferentiableOn ℂ ψ (ball 0 (min (1 : ℂ).re ((2 : ℂ) - 1).re / 2)) :=
    fillC_differentiableOn_KerS 2 1 hw hsw
  have hc : (∫ t in (0 : ℝ)..1, (t : ℂ) * (1 - (t : ℂ))) * ψ 0 = 1 / 6 := by
    rw [fillC_integral_t_one_sub_t, hψdef]
    simp only [Prod.fst_zero, Prod.snd_zero, add_zero]
    rw [fillC_KerS_two_one, mul_one]
  have h := fillC_isBigO_of_param (F := Jseg Aff.idL k0 1 1) (α := 2) 3
    (fillC_radius_pos 2 1 hw hsw) hψ (by fun_prop : Continuous fun t : ℝ => (t : ℂ) * (1 - (t : ℂ))) hc
    (fun δ => ?_)
  · refine h.congr_left fun s => ?_
    ring
  simp only [Jseg, app_idL]
  rw [show 2 + δ - 1 - 1 = δ by ring, pow_succ', mul_assoc]
  congr 1
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [k0, hψdef]
  generalize KerS (2 + δ) (1 + (t : ℂ) * δ) = K
  ring

end GoldbachBoundaries.Paper2.M4a
