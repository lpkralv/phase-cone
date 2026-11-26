import GoldbachBoundaries.Paper2.M3.Hsq

/-!
# Group E shared helpers: the Laplace transform and its derivatives right of the abscissa

`lapI φ n s u = (-u)^n φ(u) e^{-su}` and `lapN φ n s = ∫_0^∞ lapI φ n s u du`, so `laplace φ = lapN φ 0`.
For `x ∈ laplaceConvSet φ` and `x < Re s`, `lapI φ n s` is integrable on `(0, ∞)` (dominated by
`n!/(Re s - x)^n · φ(u)e^{-xu}`, from `u^n e^{-cu} ≤ n!/c^n`), and `lapN φ n` has complex derivative
`lapN φ (n+1)` at `s` (`hasDerivAt_integral_of_dominated_loc_of_deriv_le` on a ball about `s`).
Measurability of `φ` on `(0, ∞)` is read off the integrability of `φ(u)e^{-xu}`.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory


namespace GoldbachBoundaries.Paper2.M3

open GoldbachBoundaries GoldbachBoundaries.Paper2

namespace LandauFill

variable {φ : ℝ → ℝ}

/-- The integrand `(-u)^n φ(u) e^{-su}`. -/
def lapI (φ : ℝ → ℝ) (n : ℕ) (s : ℂ) (u : ℝ) : ℂ :=
  ((-(u : ℂ)) ^ n * (φ u : ℂ)) * exp (-(s * u))

/-- `∫_0^∞ (-u)^n φ(u) e^{-su} du`. -/
def lapN (φ : ℝ → ℝ) (n : ℕ) (s : ℂ) : ℂ := ∫ u in Ioi (0 : ℝ), lapI φ n s u

lemma laplace_eq_lapN (φ : ℝ → ℝ) : laplace φ = lapN φ 0 := by
  funext s
  simp [laplace, lapN, lapI]

lemma norm_lapI (n : ℕ) (s : ℂ) {u : ℝ} (hu : 0 ≤ u) (hφ : 0 ≤ φ u) :
    ‖lapI φ n s u‖ = u ^ n * φ u * Real.exp (-(s.re * u)) := by
  simp only [lapI, norm_mul, norm_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hu, abs_of_nonneg hφ, Complex.norm_exp]
  congr 2
  simp [Complex.mul_re]

lemma pow_mul_exp_le {c : ℝ} (hc : 0 < c) {u : ℝ} (hu : 0 ≤ u) (n : ℕ) :
    u ^ n * Real.exp (-(c * u)) ≤ (Nat.factorial n) / c ^ n := by
  have h := Real.pow_div_factorial_le_exp _ (mul_nonneg hc.le hu) n
  rw [div_le_iff₀ (by positivity)] at h
  rw [le_div_iff₀ (by positivity)]
  have he : 0 < Real.exp (-(c * u)) := Real.exp_pos _
  calc u ^ n * Real.exp (-(c * u)) * c ^ n = (c * u) ^ n * Real.exp (-(c * u)) := by ring
    _ ≤ (Real.exp (c * u) * (Nat.factorial n)) * Real.exp (-(c * u)) := mul_le_mul_of_nonneg_right h he.le
    _ = (Nat.factorial n) := by
      rw [mul_comm, ← mul_assoc, ← Real.exp_add]; simp

/-- Domination: for `t ≥ x + c`, `u^n φ(u) e^{-tu} ≤ n!/c^n · φ(u) e^{-xu}`. -/
lemma bound_aux {x c t : ℝ} (hc : 0 < c) (ht : x + c ≤ t) {u : ℝ} (hu : 0 ≤ u) (hφ : 0 ≤ φ u)
    (n : ℕ) : u ^ n * φ u * Real.exp (-(t * u)) ≤ (Nat.factorial n) / c ^ n * (φ u * Real.exp (-(x * u))) := by
  have h1 : Real.exp (-(t * u)) ≤ Real.exp (-(c * u)) * Real.exp (-(x * u)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    nlinarith
  have h2 := pow_mul_exp_le hc hu n
  calc u ^ n * φ u * Real.exp (-(t * u))
      ≤ u ^ n * φ u * (Real.exp (-(c * u)) * Real.exp (-(x * u))) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = (u ^ n * Real.exp (-(c * u))) * (φ u * Real.exp (-(x * u))) := by ring
    _ ≤ (Nat.factorial n) / c ^ n * (φ u * Real.exp (-(x * u))) :=
        mul_le_mul_of_nonneg_right h2 (mul_nonneg hφ (Real.exp_pos _).le)

lemma aesm_phi {x : ℝ} (hx : x ∈ laplaceConvSet φ) :
    AEStronglyMeasurable φ (volume.restrict (Ioi (0 : ℝ))) := by
  have h1 : AEStronglyMeasurable (fun u => φ u * Real.exp (-(x * u)))
      (volume.restrict (Ioi (0 : ℝ))) := hx.aestronglyMeasurable
  have h2 : AEStronglyMeasurable (fun u : ℝ => Real.exp (x * u)) (volume.restrict (Ioi (0 : ℝ))) :=
    (by fun_prop : Continuous fun u : ℝ => Real.exp (x * u)).aestronglyMeasurable
  refine (h1.mul h2).congr (Eventually.of_forall fun u => ?_)
  simp only [Pi.mul_apply]
  rw [mul_assoc, ← Real.exp_add]
  simp

lemma aesm_lapI {x : ℝ} (hx : x ∈ laplaceConvSet φ) (n : ℕ) (s : ℂ) :
    AEStronglyMeasurable (lapI φ n s) (volume.restrict (Ioi (0 : ℝ))) := by
  have hφ : AEStronglyMeasurable (fun u => (φ u : ℂ)) (volume.restrict (Ioi (0 : ℝ))) :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable (aesm_phi hx)
  have hc1 : AEStronglyMeasurable (fun u : ℝ => (-(u : ℂ)) ^ n) (volume.restrict (Ioi (0 : ℝ))) :=
    (by fun_prop : Continuous fun u : ℝ => (-(u : ℂ)) ^ n).aestronglyMeasurable
  have hc2 : AEStronglyMeasurable (fun u : ℝ => exp (-(s * u))) (volume.restrict (Ioi (0 : ℝ))) :=
    (by fun_prop : Continuous fun u : ℝ => exp (-(s * u))).aestronglyMeasurable
  exact (hc1.mul hφ).mul hc2

/-- The integrand is integrable right of a point of `S`. -/
lemma integrableOn_lapI (hφ0 : ∀ u, 0 < u → 0 ≤ φ u) {x : ℝ} (hx : x ∈ laplaceConvSet φ) {s : ℂ}
    (hxs : x < s.re) (n : ℕ) : IntegrableOn (lapI φ n s) (Ioi (0 : ℝ)) := by
  refine Integrable.mono' (hx.const_mul ((Nat.factorial n) / (s.re - x) ^ n)) (aesm_lapI hx n s) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
  have hu0 : 0 < u := hu
  rw [norm_lapI n s hu0.le (hφ0 u hu0)]
  exact bound_aux (sub_pos.2 hxs) (by linarith) hu0.le (hφ0 u hu0) n

lemma hasDerivAt_lapI (n : ℕ) (s : ℂ) (u : ℝ) :
    HasDerivAt (fun s => lapI φ n s u) (lapI φ (n + 1) s u) s := by
  have h1 : HasDerivAt (fun s : ℂ => -(s * u)) (-(u : ℂ)) s := by
    exact HasDerivAt.neg (f := fun s : ℂ => s * u) (by simpa using (hasDerivAt_id s).mul_const (u : ℂ))
  have h := h1.cexp.const_mul ((-(u : ℂ)) ^ n * (φ u : ℂ))
  convert h using 1
  · rfl
  · show ((-(u : ℂ)) ^ (n + 1) * (φ u : ℂ)) * exp (-(s * u)) = _
    ring

/-- `lapN φ n` has derivative `lapN φ (n+1)` right of a point of `S`. -/
lemma hasDerivAt_lapN (hφ0 : ∀ u, 0 < u → 0 ≤ φ u) {x : ℝ} (hx : x ∈ laplaceConvSet φ) {s₀ : ℂ}
    (hxs : x < s₀.re) (n : ℕ) : HasDerivAt (lapN φ n) (lapN φ (n + 1) s₀) s₀ := by
  set c := (s₀.re - x) / 2 with hc
  have hc0 : 0 < c := by rw [hc]; linarith
  have hball : ∀ s ∈ ball s₀ c, x + c ≤ s.re := by
    intro s hs
    rw [mem_ball, dist_eq_norm] at hs
    have h1 : |(s - s₀).re| ≤ ‖s - s₀‖ := abs_re_le_norm _
    rw [sub_re] at h1
    have h2 := neg_abs_le (s.re - s₀.re)
    rw [hc] at hs ⊢
    linarith
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun s u => lapI φ n s u) (F' := fun s u => lapI φ (n + 1) s u) (x₀ := s₀)
    (bound := fun u => (Nat.factorial (n + 1)) / c ^ (n + 1) * (φ u * Real.exp (-(x * u))))
    (ball_mem_nhds s₀ hc0) (Eventually.of_forall fun s => aesm_lapI hx n s)
    (integrableOn_lapI hφ0 hx hxs n) (aesm_lapI hx (n + 1) s₀) ?_ (hx.const_mul _)
    (Eventually.of_forall fun u s _ => hasDerivAt_lapI n s u)
  · exact key.2
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu s hs => ?_)
    have hu0 : 0 < u := hu
    rw [norm_lapI (n + 1) s hu0.le (hφ0 u hu0)]
    exact bound_aux hc0 (hball s hs) hu0.le (hφ0 u hu0) (n + 1)

/-- The iterated derivatives of `laplace φ` right of the abscissa. -/
lemma iteratedDeriv_laplace_eq (hφ0 : ∀ u, 0 < u → 0 ≤ φ u) (n : ℕ) :
    ∀ s : ℂ, (∃ x ∈ laplaceConvSet φ, x < s.re) → iteratedDeriv n (laplace φ) s = lapN φ n s := by
  induction n with
  | zero => intro s _; simp [laplace_eq_lapN]
  | succ n ih =>
    rintro s ⟨x, hx, hxs⟩
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv n (laplace φ) =ᶠ[𝓝 s] lapN φ n := by
      filter_upwards [(Complex.continuous_re.tendsto s).eventually_const_lt hxs] with z hz
      exact ih z ⟨x, hx, hz⟩
    rw [hev.deriv_eq]
    exact (hasDerivAt_lapN hφ0 hx hxs n).deriv

end LandauFill

end GoldbachBoundaries.Paper2.M3
