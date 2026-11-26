import GoldbachBoundaries.Paper2.M4a.Fill.GroupCCommon

/-!
# Fill (group C): `isBigO_Jseg_kr_b_one`

With `δ = s - (1 + b)`: `J_{b1}(1 + b + δ) = δ^{r+1} ∫_0^1 (1 - t)^r ψ₂(tδ, δ) dt`,
`ψ₂(u, δ) = K_{1+b+δ}(b + u)(b - 1 + u)^r`, `ψ₂(0) = (b - 1)^r/b`, `∫_0^1 (1 - t)^r = 1/(r + 1)`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M4a

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **`J_{b1}` for `k_r` at `1 + b`** (no RH; any `r`, any `b ∈ Σ`). With `δ = s - (1 + b)`:
`Jseg Aff.idL (kr r) b 1 s = δ ∫_0^1 k_r(b + tδ, 1 + b + δ) dt` and
`k_r(b + tδ, 1 + b + δ) = K_{1+b+δ}(b + tδ) · ((b - 1 + tδ)(δ(1 - t)))^r`, so
`J_{b1} = δ^{r+1} ∫_0^1 (1 - t)^r ψ₂(tδ, δ) dt` with `ψ₂(u, δ) = KerS (1 + b + δ) (b + u) · (b - 1 + u)^r`,
`ψ₂ 0 = Γ(b)Γ(1)/Γ(1 + b) · (b - 1)^r = (b - 1)^r/b`, `∫_0^1 (1 - t)^r = 1/(r + 1)`. As `isBigO_Jseg_kr_one_b`.
Size: 100–200 lines. -/
theorem isBigO_Jseg_kr_b_one (r : ℕ) {b : ℂ} (hb : b ∈ PoleSetQ) :
    (fun s => Jseg Aff.idL (kr r) b 1 s - (b - 1) ^ r / (b * ((r : ℂ) + 1)) * (s - (1 + b)) ^ (r + 1))
      =O[𝓝 (1 + b)] fun s => (s - (1 + b)) ^ (r + 2) := by
  have hbre : 0 < b.re := (poleSetQ_re_bounds hb).1
  have hb0 : b ≠ 0 := fun h => by rw [h] at hbre; simp at hbre
  have hsw : 0 < ((1 + b) - b).re := by simp
  set ψ : ℂ × ℂ → ℂ := fun p => KerS (1 + b + p.2) (b + p.1) * (b - 1 + p.1) ^ r with hψdef
  have hψ : DifferentiableOn ℂ ψ (ball 0 (min b.re ((1 + b) - b).re / 2)) :=
    (fillC_differentiableOn_KerS (1 + b) b hbre hsw).mul (by fun_prop : Differentiable ℂ fun p : ℂ × ℂ =>
      (b - 1 + p.1) ^ r).differentiableOn
  have hc : (∫ t in (0 : ℝ)..1, (1 - (t : ℂ)) ^ r) * ψ 0 = (b - 1) ^ r / (b * ((r : ℂ) + 1)) := by
    rw [fillC_integral_one_sub_pow, hψdef]
    simp only [Prod.fst_zero, Prod.snd_zero, add_zero]
    rw [fillC_KerS_b hbre]
    have hr : (r : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero r
    field_simp
  refine fillC_isBigO_of_param (F := Jseg Aff.idL (kr r) b 1) (α := 1 + b) (r + 1)
    (fillC_radius_pos (1 + b) b hbre hsw) hψ (by fun_prop : Continuous fun t : ℝ => (1 - (t : ℂ)) ^ r) hc
    (fun δ => ?_)
  simp only [Jseg, app_idL]
  rw [show 1 + b + δ - b - 1 = δ by ring, pow_succ', mul_assoc]
  congr 1
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [kr, hψdef]
  rw [show (b + (t : ℂ) * δ - 1) * (1 + b + δ - 1 - (b + (t : ℂ) * δ)) = δ * ((1 - (t : ℂ)) * (b - 1 + t * δ)) by
    ring, mul_pow, mul_pow]
  ring

end GoldbachBoundaries.Paper2.M4a
