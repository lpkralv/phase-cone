import GoldbachBoundaries.Paper2.M4b.Boundary

/-!
# M4b filler group D (the example kernels): shared helpers

* `analyticAt_invGamma`, `analyticAt_invGamma_comp`, `meromorphicAt_Gamma_comp`: `1/Γ` is entire, so `Γ ∘ f` is
  meromorphic for analytic `f`.
* `invGamma_ne_zero_of_im`, `exists_ball_im`: `1/Γ` does not vanish off the real axis, and every ball of `ℂ²` has a
  point with prescribed imaginary parts avoided (for the non-vanishing denominators of (K4)).
* `Z6'`: (Z6) with `C ≥ 0`.
* `exists_rpow_mul_exp_half_le`: `(1 + u)^E e^{-πu/2} ≤ K/(1 + u)²` for `u ≥ 0`.
* `differentiableAt_Gamma_of_re_pos`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M4b

open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace FillD

/-- `1/Γ` is analytic everywhere. -/
lemma analyticAt_invGamma (w : ℂ) : AnalyticAt ℂ (fun w => (Gamma w)⁻¹) w :=
  Complex.differentiable_one_div_Gamma.analyticAt w

/-- `1/Γ ∘ f` is analytic where `f` is. -/
lemma analyticAt_invGamma_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : E → ℂ} {p : E}
    (hf : AnalyticAt ℂ f p) : AnalyticAt ℂ (fun q => (Gamma (f q))⁻¹) p :=
  (analyticAt_invGamma (f p)).comp hf

/-- `Γ ∘ f` is meromorphic where `f` is analytic. -/
lemma meromorphicAt_Gamma_comp {f : ℂ → ℂ} {w : ℂ} (hf : AnalyticAt ℂ f w) :
    MeromorphicAt (fun x => Gamma (f x)) w := by
  have h := (analyticAt_invGamma_comp hf).meromorphicAt.inv
  convert h using 1
  funext x
  simp

/-- `1/Γ(w) ≠ 0` off the real axis. -/
lemma invGamma_ne_zero_of_im {w : ℂ} (hw : w.im ≠ 0) : (Gamma w)⁻¹ ≠ 0 := by
  refine inv_ne_zero (Complex.Gamma_ne_zero fun m hm => hw ?_)
  rw [hm]; simp

/-- `Γ` is differentiable on `Re w > 0`. -/
lemma differentiableAt_Gamma_of_re_pos {w : ℂ} (hw : 0 < w.re) : DifferentiableAt ℂ Gamma w :=
  differentiableAt_Gamma _ (fun m h => by
    rw [h] at hw; simp at hw; linarith [(m.cast_nonneg : (0:ℝ) ≤ m)])

/-- A point within `ε` of `a` whose imaginary part is not `c`. -/
lemma exists_near_im_ne (a : ℂ) {ε : ℝ} (hε : 0 < ε) (c : ℝ) : ∃ a' : ℂ, dist a' a < ε ∧ a'.im ≠ c := by
  by_cases h : a.im = c
  · refine ⟨a + ((ε / 2 : ℝ) : ℂ) * I, ?_, ?_⟩
    · rw [dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by linarith)]
      linarith
    · simp only [add_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero, h]
      linarith
  · exact ⟨a, by simpa using hε, h⟩

/-- Every ball of `ℂ²` has a point `q` with `Im q.1 ≠ c₁` and `Im q.2 ≠ c₂(Im q.1)`. -/
lemma exists_ball_im (p : ℂ × ℂ) {r : ℝ} (hr : 0 < r) (c₁ : ℝ) (c₂ : ℝ → ℝ) :
    ∃ q ∈ ball p r, q.1.im ≠ c₁ ∧ q.2.im ≠ c₂ q.1.im := by
  obtain ⟨z, hz, hz'⟩ := exists_near_im_ne p.1 hr c₁
  obtain ⟨s, hs, hs'⟩ := exists_near_im_ne p.2 hr (c₂ z.im)
  refine ⟨(z, s), ?_, hz', hs'⟩
  rw [mem_ball, Prod.dist_eq]
  exact max_lt hz hs

/-- (Z6) with a non-negative constant. -/
lemma Z6' (hZ6 : Z6) {x₁ x₂ : ℝ} (hx₁ : 0 < x₁) (hx₁₂ : x₁ ≤ x₂) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Icc x₁ x₂, ∀ y : ℝ,
      ‖Gamma (x + y * I)‖ ≤ C * (1 + |y|) ^ x₂ * Real.exp (-(Real.pi * |y| / 2)) := by
  obtain ⟨C, hC⟩ := hZ6 x₁ x₂ hx₁ hx₁₂
  refine ⟨max C 0, le_max_right _ _, fun x hx y => (hC x hx y).trans ?_⟩
  have h1 : 0 ≤ (1 + |y|) ^ x₂ := Real.rpow_nonneg (by positivity) _
  have h2 := Real.exp_pos (-(Real.pi * |y| / 2))
  gcongr
  exact le_max_left _ _

/-- Polynomial against `e^{-πu/2}`: `(1 + u)^E e^{-πu/2} ≤ K/(1 + u)²` for `u ≥ 0` (as M4a's
`FillD.exists_rpow_mul_exp_le`, with `π/2 > 1` in place of `π > 1`). -/
lemma exists_rpow_mul_exp_half_le (E : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : ℝ, 0 ≤ u →
      (1 + u) ^ E * Real.exp (-(Real.pi * u / 2)) ≤ K / (1 + u) ^ 2 := by
  set n : ℕ := ⌈max E 0⌉₊ + 2 with hn
  refine ⟨n.factorial * Real.exp 1, by positivity, fun u hu => ?_⟩
  have hpos : 0 < 1 + u := by linarith
  rw [le_div_iff₀ (by positivity)]
  have hE : E + 2 ≤ (n : ℝ) := by
    have := Nat.le_ceil (max E 0)
    have : E ≤ max E 0 := le_max_left _ _
    push_cast [hn]; linarith
  have h1 : (1 + u) ^ E * (1 + u) ^ 2 = (1 + u) ^ (E + 2) := by
    rw [Real.rpow_add hpos]; norm_cast
  have h2 : (1 + u) ^ (E + 2) ≤ (1 + u) ^ n := by
    rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le (by linarith) hE
  have h3 : (1 + u) ^ n ≤ n.factorial * Real.exp (1 + u) := by
    have := Real.pow_div_factorial_le_exp (1 + u) hpos.le n
    rw [div_le_iff₀ (by positivity)] at this; linarith
  have h4 : Real.exp (1 + u) * Real.exp (-(Real.pi * u / 2)) ≤ Real.exp 1 := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.2
    nlinarith [Real.pi_gt_three]
  calc (1 + u) ^ E * Real.exp (-(Real.pi * u / 2)) * (1 + u) ^ 2
      = (1 + u) ^ (E + 2) * Real.exp (-(Real.pi * u / 2)) := by rw [← h1]; ring
    _ ≤ n.factorial * Real.exp (1 + u) * Real.exp (-(Real.pi * u / 2)) := by
        apply mul_le_mul_of_nonneg_right (h2.trans h3) (Real.exp_pos _).le
    _ = n.factorial * (Real.exp (1 + u) * Real.exp (-(Real.pi * u / 2))) := by ring
    _ ≤ n.factorial * Real.exp 1 := by gcongr

/-- `(1 + v)^a ≤ (1 + R)^a (1 + u)^a` when `1 + v ≤ (1 + R)(1 + u)`. -/
lemma rpow_le_of_le_mul {v u R a : ℝ} (hv : 0 ≤ v) (hu : 0 ≤ u) (hR : 0 ≤ R) (ha : 0 ≤ a)
    (h : 1 + v ≤ (1 + R) * (1 + u)) : (1 + v) ^ a ≤ (1 + R) ^ a * (1 + u) ^ a := by
  rw [← Real.mul_rpow (by linarith) (by linarith)]
  exact Real.rpow_le_rpow (by linarith) h ha

end FillD

end GoldbachBoundaries.Paper2.M4b
