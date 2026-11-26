import GoldbachBoundaries.Paper2.M3.Fill.LandauCommon

/-!
Fill of `laplace_no_extension` (Paper2/M3/Landau.lean), the core of Landau's lemma.

`σ = sInf S`, `a = σ + r/3`, `d = r/2`, `s₁ = a - d = σ - r/6`. The function `L̃` (`𝓛` on `{Re > σ}`, `g`
elsewhere) is holomorphic on `Δ(a, 2r/3)`; its Taylor series at `a` converges at `s₁`
(`Complex.hasSum_taylorSeries_on_ball`), with real terms `T n = ∫_0^∞ (du)^n/n! φ(u)e^{-au} du ≥ 0`. Monotone
convergence (`lintegral_tsum`) and the exponential series give `∫_0^∞ φ(u)e^{-s₁u} du < ∞`, so `s₁ ∈ S`, against
`s₁ < σ`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M3

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- A point of `Δ(σ + r/3, 2r/3)` with real part `≤ σ` lies in `Δ(σ, r)`. -/
lemma LandauFill.mem_ball_of_re_le {σ r : ℝ} (hr : 0 < r) {w : ℂ}
    (hw : w ∈ ball ((σ + r / 3 : ℝ) : ℂ) (2 * r / 3)) (hre : w.re ≤ σ) : w ∈ ball (σ : ℂ) r := by
  rw [mem_ball, dist_eq_norm] at hw ⊢
  have h1 : ‖w - ((σ + r / 3 : ℝ) : ℂ)‖ ^ 2 < (2 * r / 3) ^ 2 := by
    have := norm_nonneg (w - ((σ + r / 3 : ℝ) : ℂ))
    nlinarith
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at h1
  simp only [sub_re, sub_im, ofReal_re, ofReal_im, sub_zero] at h1
  have h2 : ‖w - (σ : ℂ)‖ ^ 2 < r ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [sub_re, sub_im, ofReal_re, ofReal_im, sub_zero]
    nlinarith
  have h3 := norm_nonneg (w - (σ : ℂ))
  nlinarith

/-- The exponential series. -/
lemma LandauFill.hasSum_exp_real (x : ℝ) :
    HasSum (fun n : ℕ => x ^ n / (Nat.factorial n : ℝ)) (Real.exp x) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp x

/-- **No holomorphic extension at the abscissa** (general; the core of `nr:lem:Landau`). Put `σ_c = sInf S` (genuine:
`S` non-empty and bounded below), `a = σ_c + r/3`, `s₁ = σ_c - r/6`. Suppose `g` is holomorphic on `Δ(σ_c, r)` and
equals `𝓛` on its right half. The glued function `L̃` (`𝓛` on `{Re > σ_c}`, `g` on the disc; they agree on the overlap,
which is the right half-disc) is holomorphic on `Δ(a, 2r/3)` (a point `w` of it with `Re w ≤ σ_c` has
`|w - σ_c| < r`), so its Taylor series at `a` converges at `s₁` (`|s₁ - a| = r/2 < 2r/3`;
`DifferentiableOn.hasFPowerSeriesOnBall`, `HasFPowerSeriesOnBall.hasSum_iteratedFDeriv` or the `taylorSeries` lemmas
of `Mathlib/Analysis/Complex/TaylorSeries.lean`). The derivatives at `a` are those of `𝓛` (`a` is interior to
`{Re > σ_c}`; `iteratedDeriv_laplace`, with `a > σ_c` giving some `x ∈ S`, `x < a`), so
`L̃(s₁) = ∑_n ∫_0^∞ ((a - s₁)u)^n/n! φ(u)e^{-au} du`, every term non-negative; Tonelli
(`integral_tsum` / `lintegral_tsum` on the non-negative terms) gives
`∫_0^∞ φ(u)e^{-au}e^{(a - s₁)u} du = ∫_0^∞ φ(u)e^{-s₁u} du < ∞`, i.e. `s₁ ∈ S`, against `s₁ < σ_c = sInf S`
(`csInf_le`). Size: 250–450 lines. -/
theorem laplace_no_extension (φ : ℝ → ℝ) (hφm : Measurable ((Ioi (0 : ℝ)).domRestrict φ))
    (hφ0 : ∀ u, 0 < u → 0 ≤ φ u) (hS : (laplaceConvSet φ).Nonempty) (hB : BddBelow (laplaceConvSet φ))
    {r : ℝ} (hr : 0 < r) :
    ¬ ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball ((sInf (laplaceConvSet φ) : ℝ) : ℂ) r) ∧
      EqOn g (laplace φ) (ball ((sInf (laplaceConvSet φ) : ℝ) : ℂ) r ∩
        {s | sInf (laplaceConvSet φ) < s.re}) := by
  rintro ⟨g, hg, hgeq⟩
  set σ := sInf (laplaceConvSet φ) with hσ
  have hright : ∀ w : ℂ, σ < w.re → ∃ x ∈ laplaceConvSet φ, x < w.re := fun w hw =>
    exists_lt_of_csInf_lt hS hw
  set a : ℝ := σ + r / 3 with ha
  set d : ℝ := r / 2 with hd
  set s₁ : ℝ := a - d with hs₁
  have hd0 : 0 < d := by rw [hd]; linarith
  -- the glued function
  set Lt : ℂ → ℂ := fun z => if σ < z.re then laplace φ z else g z with hLt
  have hLt_right : ∀ z : ℂ, σ < z.re → Lt z = laplace φ z := fun z hz => by simp [hLt, hz]
  have hLt_ball : ∀ z ∈ ball (σ : ℂ) r, Lt z = g z := by
    intro z hz
    by_cases h : σ < z.re
    · rw [hLt_right z h]; exact (hgeq ⟨hz, h⟩).symm
    · simp [hLt, h]
  have hdiff : DifferentiableOn ℂ Lt (ball (a : ℂ) (2 * r / 3)) := by
    intro w hw
    apply DifferentiableAt.differentiableWithinAt
    by_cases h : σ < w.re
    · have hev : Lt =ᶠ[𝓝 w] laplace φ := by
        filter_upwards [(Complex.continuous_re.tendsto w).eventually_const_lt h] with z hz
        exact hLt_right z hz
      obtain ⟨x, hx, hxw⟩ := hright w h
      have : DifferentiableAt ℂ (laplace φ) w := by
        rw [LandauFill.laplace_eq_lapN]
        exact (LandauFill.hasDerivAt_lapN hφ0 hx hxw 0).differentiableAt
      exact this.congr_of_eventuallyEq hev
    · have hwb : w ∈ ball (σ : ℂ) r := LandauFill.mem_ball_of_re_le hr hw (not_lt.1 h)
      have hev : Lt =ᶠ[𝓝 w] g := by
        filter_upwards [isOpen_ball.mem_nhds hwb] with z hz
        exact hLt_ball z hz
      exact (hg.differentiableAt (isOpen_ball.mem_nhds hwb)).congr_of_eventuallyEq hev
  have hs₁mem : (s₁ : ℂ) ∈ ball (a : ℂ) (2 * r / 3) := by
    rw [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_neg (by rw [hs₁]; linarith)]
    rw [hs₁, hd]; linarith
  have hsum := Complex.hasSum_taylorSeries_on_ball hdiff hs₁mem
  -- the derivatives at `a` are those of `𝓛`
  have haright : σ < (a : ℂ).re := by rw [ofReal_re, ha]; linarith
  obtain ⟨xa, hxa, hxaa⟩ := hright _ haright
  have hderiv : ∀ n, iteratedDeriv n Lt (a : ℂ) = LandauFill.lapN φ n a := by
    intro n
    have hev : Lt =ᶠ[𝓝 (a : ℂ)] laplace φ := by
      filter_upwards [(Complex.continuous_re.tendsto _).eventually_const_lt haright] with z hz
      exact hLt_right z hz
    rw [hev.iteratedDeriv_eq n]
    exact LandauFill.iteratedDeriv_laplace_eq hφ0 n _ ⟨xa, hxa, hxaa⟩
  -- the real terms
  set f : ℕ → ℝ → ℝ := fun n u => (d * u) ^ n / (Nat.factorial n : ℝ) * (φ u * Real.exp (-(a * u)))
    with hf
  set T : ℕ → ℝ := fun n => ∫ u in Ioi (0 : ℝ), f n u with hT
  have hf_nonneg : ∀ n, ∀ u ∈ Ioi (0 : ℝ), 0 ≤ f n u := by
    intro n u hu
    have hu0 : 0 < u := hu
    have := hφ0 u hu0
    simp only [hf]
    positivity
  have hf_int : ∀ n, IntegrableOn (f n) (Ioi (0 : ℝ)) := by
    intro n
    have h0 : IntegrableOn (fun u => d ^ n / (Nat.factorial n : ℝ) * ‖LandauFill.lapI φ n a u‖)
        (Ioi (0 : ℝ)) :=
      ((LandauFill.integrableOn_lapI hφ0 hxa hxaa n).norm).const_mul (d ^ n / (Nat.factorial n : ℝ))
    refine h0.congr_fun (fun u hu => ?_) measurableSet_Ioi
    have hu0 : 0 < u := hu
    simp only
    rw [LandauFill.norm_lapI n _ hu0.le (hφ0 u hu0), ofReal_re, hf]
    simp only
    rw [mul_pow]
    ring
  have hterm : ∀ n, (Nat.factorial n : ℂ)⁻¹ • ((s₁ : ℂ) - a) ^ n • iteratedDeriv n Lt (a : ℂ) =
      ((T n : ℝ) : ℂ) := by
    intro n
    rw [hderiv n, smul_eq_mul, smul_eq_mul, LandauFill.lapN, ← integral_const_mul,
      ← integral_const_mul, hT, ← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
    have hsd : (s₁ : ℂ) - a = -(d : ℂ) := by rw [hs₁]; push_cast; ring
    have hp : (-(d : ℂ)) ^ n * (-(u : ℂ)) ^ n = ((d : ℂ) * u) ^ n := by
      rw [← mul_pow, neg_mul_neg]
    show (Nat.factorial n : ℂ)⁻¹ * (((s₁ : ℂ) - a) ^ n * (((-(u : ℂ)) ^ n * (φ u : ℂ)) *
      exp (-((a : ℂ) * u)))) = _
    rw [hsd, hf]
    push_cast
    linear_combination ((Nat.factorial n : ℂ)⁻¹ * (φ u : ℂ) * exp (-((a : ℂ) * u))) * hp
  have hsumT : HasSum (fun n => ((T n : ℝ) : ℂ)) (Lt s₁) := by
    simpa only [hterm] using hsum
  have hTsum : Summable T := Complex.summable_ofReal.1 hsumT.summable
  have hT_nonneg : ∀ n, 0 ≤ T n := fun n =>
    setIntegral_nonneg measurableSet_Ioi (hf_nonneg n)
  -- pointwise: the series of `f n u` sums to `φ(u)e^{-s₁u}`
  have hpt : ∀ u ∈ Ioi (0 : ℝ), HasSum (fun n => f n u) (φ u * Real.exp (-(s₁ * u))) := by
    intro u _
    have h := (LandauFill.hasSum_exp_real (d * u)).mul_right (φ u * Real.exp (-(a * u)))
    convert h using 1
    rw [show φ u * Real.exp (-(s₁ * u)) = Real.exp (d * u) * (φ u * Real.exp (-(a * u))) by
      rw [hs₁, mul_comm (Real.exp _), mul_assoc, ← Real.exp_add]; ring_nf]
  -- integrability at `s₁`
  have hint : IntegrableOn (fun u => φ u * Real.exp (-(s₁ * u))) (Ioi (0 : ℝ)) := by
    have hmeas : AEStronglyMeasurable (fun u => φ u * Real.exp (-(s₁ * u)))
        (volume.restrict (Ioi (0 : ℝ))) :=
      (LandauFill.aesm_phi hxa).mul
        (by fun_prop : Continuous fun u : ℝ => Real.exp (-(s₁ * u))).aestronglyMeasurable
    have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] fun u => φ u * Real.exp (-(s₁ * u)) :=
      (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu =>
        mul_nonneg (hφ0 u hu) (Real.exp_pos _).le)
    refine ⟨hmeas, (hasFiniteIntegral_iff_ofReal hnn).2 ?_⟩
    have h1 : ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (φ u * Real.exp (-(s₁ * u))) =
        ∫⁻ u in Ioi (0 : ℝ), ∑' n, ENNReal.ofReal (f n u) := by
      refine setLIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => hf_nonneg n u hu) (hpt u hu).summable,
        (hpt u hu).tsum_eq]
    have h2 : ∫⁻ u in Ioi (0 : ℝ), ∑' n, ENNReal.ofReal (f n u) =
        ∑' n, ENNReal.ofReal (T n) := by
      rw [lintegral_tsum (fun n => (hf_int n).aemeasurable.ennreal_ofReal)]
      congr 1
      funext n
      rw [hT, ofReal_integral_eq_lintegral_ofReal (hf_int n)
        ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall (hf_nonneg n)))]
    rw [h1, h2, ← ENNReal.ofReal_tsum_of_nonneg hT_nonneg hTsum]
    exact ENNReal.ofReal_lt_top
  have hmem : s₁ ∈ laplaceConvSet φ := hint
  have hle : σ ≤ s₁ := csInf_le hB hmem
  rw [hs₁, ha, hd] at hle
  linarith

end GoldbachBoundaries.Paper2.M3
