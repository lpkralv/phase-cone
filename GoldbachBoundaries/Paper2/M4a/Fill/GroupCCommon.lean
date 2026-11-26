import GoldbachBoundaries.Paper2.M4a.Fill.isBigO_integral_param

/-!
# Fill (group C): shared helpers for the expansions of `J_{ab}` near pinches

* `fillC_differentiableOn_KerS`: `(u, δ) ↦ K_{s₀+δ}(w₀ + u)` is holomorphic on a ball about `0 ∈ ℂ²` when
  `Re w₀ > 0` and `Re(s₀ - w₀) > 0` (all three `Γ` arguments keep positive real part).
* `fillC_KerS_add_one`: `K_{1+b}(1) = 1/b` and `K_{1+b}(b) = 1/b` for `Re b > 0`.
* `fillC_isBigO_of_param`: if `F(α + δ) = δ^m ∫_0^1 w(t)ψ(tδ, δ) dt` with `ψ` holomorphic near `0`, then
  `F(s) - (ψ(0)∫w)(s - α)^m = O((s - α)^{m+1})` at `α` (from `isBigO_integral_param`).
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M4a

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

lemma fillC_differentiableAt_Gamma {z : ℂ} (hz : 0 < z.re) : DifferentiableAt ℂ Gamma z := by
  refine Complex.differentiableAt_Gamma z fun m h => ?_
  rw [h] at hz
  simp at hz
  linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

/-- `(u, δ) ↦ K_{s₀+δ}(w₀ + u)` is holomorphic on the ball of radius `min(Re w₀, Re(s₀ - w₀))/2` about `0`. -/
lemma fillC_differentiableOn_KerS (s0 w0 : ℂ) (hw : 0 < w0.re) (hsw : 0 < (s0 - w0).re) :
    DifferentiableOn ℂ (fun p : ℂ × ℂ => KerS (s0 + p.2) (w0 + p.1))
      (ball 0 (min w0.re (s0 - w0).re / 2)) := by
  intro p hp
  rw [mem_ball_zero_iff] at hp
  have h1 : |p.1.re| < min w0.re (s0 - w0).re / 2 :=
    (abs_re_le_norm p.1).trans_lt ((norm_fst_le p).trans_lt hp)
  have h2 : |p.2.re| < min w0.re (s0 - w0).re / 2 :=
    (abs_re_le_norm p.2).trans_lt ((norm_snd_le p).trans_lt hp)
  set μ := min w0.re (s0 - w0).re with hμ
  have hm1 : μ ≤ w0.re := min_le_left _ _
  have hm2 : μ ≤ s0.re - w0.re := by rw [← sub_re]; exact min_le_right _ _
  have hm0 : 0 < μ := lt_min hw hsw
  rw [abs_lt] at h1 h2
  have r1 : 0 < (w0 + p.1).re := by rw [add_re]; linarith
  have r2 : 0 < (s0 + p.2 - (w0 + p.1)).re := by simp only [sub_re, add_re]; linarith
  have r3 : 0 < (s0 + p.2).re := by rw [add_re]; linarith
  unfold KerS
  apply DifferentiableAt.differentiableWithinAt
  simp_rw [div_eq_mul_inv]
  apply DifferentiableAt.mul
  · apply DifferentiableAt.mul
    · exact DifferentiableAt.comp (f := fun p : ℂ × ℂ => w0 + p.1) p (fillC_differentiableAt_Gamma r1)
        (by fun_prop)
    · exact DifferentiableAt.comp (f := fun p : ℂ × ℂ => s0 + p.2 - (w0 + p.1)) p
        (fillC_differentiableAt_Gamma r2) (by fun_prop)
  · exact (DifferentiableAt.comp (f := fun p : ℂ × ℂ => s0 + p.2) p (fillC_differentiableAt_Gamma r3)
      (by fun_prop)).inv (Gamma_ne_zero_of_re_pos r3)

lemma fillC_radius_pos (s0 w0 : ℂ) (hw : 0 < w0.re) (hsw : 0 < (s0 - w0).re) :
    0 < min w0.re (s0 - w0).re / 2 := by
  have := lt_min hw hsw
  linarith

/-- `K_{1+b}(1) = Γ(1)Γ(b)/Γ(1 + b) = 1/b`. -/
lemma fillC_KerS_one {b : ℂ} (hb : 0 < b.re) : KerS (1 + b) 1 = 1 / b := by
  have hb0 : b ≠ 0 := fun h => by rw [h] at hb; simp at hb
  have hG : Gamma b ≠ 0 := Gamma_ne_zero_of_re_pos hb
  unfold KerS
  rw [show (1 + b - 1 : ℂ) = b by ring, add_comm, Complex.Gamma_add_one b hb0, Complex.Gamma_one]
  field_simp

/-- `K_{1+b}(b) = Γ(b)Γ(1)/Γ(1 + b) = 1/b`. -/
lemma fillC_KerS_b {b : ℂ} (hb : 0 < b.re) : KerS (1 + b) b = 1 / b := by
  have hb0 : b ≠ 0 := fun h => by rw [h] at hb; simp at hb
  have hG : Gamma b ≠ 0 := Gamma_ne_zero_of_re_pos hb
  unfold KerS
  rw [show (1 + b - b : ℂ) = 1 by ring, add_comm, Complex.Gamma_add_one b hb0, Complex.Gamma_one]
  field_simp

/-- `∫_0^1 t^r dt = 1/(r + 1)` (complex-valued). -/
lemma fillC_integral_pow (r : ℕ) : (∫ t in (0 : ℝ)..1, ((t : ℂ)) ^ r) = 1 / ((r : ℂ) + 1) := by
  have : (fun t : ℝ => ((t : ℂ)) ^ r) = fun t : ℝ => (((t ^ r : ℝ)) : ℂ) := by
    funext t; push_cast; rfl
  rw [this, intervalIntegral.integral_ofReal, integral_pow]
  push_cast
  simp

/-- `∫_0^1 (1 - t)^r dt = 1/(r + 1)` (complex-valued). -/
lemma fillC_integral_one_sub_pow (r : ℕ) :
    (∫ t in (0 : ℝ)..1, (1 - (t : ℂ)) ^ r) = 1 / ((r : ℂ) + 1) := by
  have h := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := 1) (fun t : ℝ => ((t : ℂ)) ^ r) 1
  simp only [sub_self, sub_zero] at h
  push_cast at h
  rw [h, fillC_integral_pow]

/-- **Reduction to `isBigO_integral_param`.** -/
lemma fillC_isBigO_of_param {F : ℂ → ℂ} {α : ℂ} (m : ℕ) {ψ : ℂ × ℂ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hψ : DifferentiableOn ℂ ψ (ball 0 ε)) {w : ℝ → ℂ} (hw : Continuous w) {c : ℂ}
    (hc : (∫ t in (0 : ℝ)..1, w t) * ψ 0 = c)
    (hF : ∀ δ : ℂ, F (α + δ) = δ ^ m * ∫ t in (0 : ℝ)..1, w t * ψ ((t : ℂ) * δ, δ)) :
    (fun s => F s - c * (s - α) ^ m) =O[𝓝 α] fun s => (s - α) ^ (m + 1) := by
  have h := (isBigO_refl (fun δ : ℂ => δ ^ m) (𝓝 0)).mul (isBigO_integral_param hε hψ hw)
  have ht : Tendsto (fun s : ℂ => s - α) (𝓝 α) (𝓝 0) :=
    tendsto_sub_nhds_zero_iff.2 tendsto_id
  refine (h.comp_tendsto ht).congr (fun s => ?_) (fun s => ?_)
  · have e := hF (s - α)
    rw [show α + (s - α) = s by ring] at e
    simp only [Function.comp_apply]
    rw [e, ← hc]
    ring
  · simp only [Function.comp_apply]
    ring

end GoldbachBoundaries.Paper2.M4a
