import GoldbachBoundaries.Paper2.M4a.Fill.GroupCCommon

/-!
# Fill (group C): `isBigO_Jseg_kr_one_b`

With `δ = s - (1 + b)`: `J_{1b}(1 + b + δ) = δ^{r+1} ∫_0^1 t^r ψ₁(tδ, δ) dt`,
`ψ₁(u, δ) = K_{1+b+δ}(1 + u)(b - 1 + δ - u)^r`, `ψ₁(0) = (b - 1)^r/b`, `∫_0^1 t^r = 1/(r + 1)`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M4a

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **`J_{1b}` for `k_r` at `1 + b`** (no RH; any `r`, any `b ∈ Σ`). With `δ = s - (1 + b)`:
`Jseg Aff.idL (kr r) 1 b s = δ^{r+1} ∫_0^1 t^r ψ₁(tδ, δ) dt` (unfold `Jseg`, `kr`, `Aff.app`; `(tδ)^r = t^r δ^r`),
`ψ₁(u, δ) = KerS (1 + b + δ) (1 + u) · (b - 1 + δ - u)^r`. `ψ₁` is differentiable on a ball about `0`: `Γ` is
differentiable at points of positive real part (`differentiableAt_Gamma`), `Re b > 0` (M1's `poleSetQ_re_bounds`),
`Γ(1 + b + δ) ≠ 0` (`Complex.Gamma_ne_zero_of_re_pos`). `ψ₁ 0 = Γ(1)Γ(b)/Γ(1 + b) · (b - 1)^r = (b - 1)^r/b`
(`Complex.Gamma_add_one`, `b ≠ 0`), `∫_0^1 t^r = 1/(r + 1)` (`integral_pow`). Then `isBigO_integral_param` with
`w t = t^r`, multiplied by `δ^{r+1}` (`IsBigO.mul`), and moved from `𝓝 0` to `𝓝 (1 + b)` by `s ↦ s - (1 + b)`
(`IsBigO.comp_tendsto`). Size: 100–200 lines. -/
theorem isBigO_Jseg_kr_one_b (r : ℕ) {b : ℂ} (hb : b ∈ PoleSetQ) :
    (fun s => Jseg Aff.idL (kr r) 1 b s - (b - 1) ^ r / (b * ((r : ℂ) + 1)) * (s - (1 + b)) ^ (r + 1))
      =O[𝓝 (1 + b)] fun s => (s - (1 + b)) ^ (r + 2) := by
  have hbre : 0 < b.re := (poleSetQ_re_bounds hb).1
  have hb0 : b ≠ 0 := fun h => by rw [h] at hbre; simp at hbre
  have hsw : 0 < ((1 + b) - 1).re := by simpa using hbre
  have hw : 0 < (1 : ℂ).re := by simp
  set ψ : ℂ × ℂ → ℂ := fun p => KerS (1 + b + p.2) (1 + p.1) * (b - 1 + p.2 - p.1) ^ r with hψdef
  have hψ : DifferentiableOn ℂ ψ (ball 0 (min (1 : ℂ).re ((1 + b) - 1).re / 2)) :=
    (fillC_differentiableOn_KerS (1 + b) 1 hw hsw).mul (by fun_prop : Differentiable ℂ fun p : ℂ × ℂ =>
      (b - 1 + p.2 - p.1) ^ r).differentiableOn
  have hc : (∫ t in (0 : ℝ)..1, ((t : ℂ)) ^ r) * ψ 0 = (b - 1) ^ r / (b * ((r : ℂ) + 1)) := by
    rw [fillC_integral_pow, hψdef]
    simp only [Prod.fst_zero, Prod.snd_zero, add_zero, sub_zero]
    rw [fillC_KerS_one hbre]
    have hr : (r : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero r
    field_simp
  refine fillC_isBigO_of_param (F := Jseg Aff.idL (kr r) 1 b) (α := 1 + b) (r + 1)
    (fillC_radius_pos (1 + b) 1 hw hsw) hψ (by fun_prop : Continuous fun t : ℝ => ((t : ℂ)) ^ r) hc
    (fun δ => ?_)
  simp only [Jseg, app_idL]
  rw [show 1 + b + δ - 1 - b = δ by ring, pow_succ', mul_assoc]
  congr 1
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [kr, hψdef]
  rw [show (1 + (t : ℂ) * δ - 1) * (1 + b + δ - 1 - (1 + (t : ℂ) * δ)) = δ * ((t : ℂ) * (b - 1 + δ - t * δ)) by
    ring, mul_pow, mul_pow]
  ring

end GoldbachBoundaries.Paper2.M4a
