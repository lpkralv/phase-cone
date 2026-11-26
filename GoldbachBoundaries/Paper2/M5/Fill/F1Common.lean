import GoldbachBoundaries.Paper2.M5.Tk

/-!
# Filler F1: shared lemmas for Theorem F(i) (`FilterI.lean`) and `T₀ = D_{H₀}`

Real proofs of the six F1 targets (`analyticAt_Afun`, `norm_gA_le`, `differentiableOn_FilLine`, `FilLine_eq_of_le`,
`differentiableOn_Fil`, and the `Fil` part of `eqOn_DH_H0f_of_T0`), stated here under `F1_` names so that each
`Fill/<target>.lean` is a one-line wrapper and none of them goes through a `sorry` skeleton lemma of this group.

* `F1_analyticAt_Afun`: `A(z) = (z - 1)Q(z)` is holomorphic on `Re z > 1/2` (RH): off `1` by paper 1's
  `analyticAt_Qcont_of_RH`, at `1` by the removable-singularity criterion (`differentiableOn_compl_singleton_and_continuousAt_iff`)
  with continuity from `hasResidue_Qcont_one`.
* `F1_analyticAt_evalH`, `F1_norm_evalH_le`: a polynomial in two variables is jointly analytic and `O((1 + |z| + |w|)^d)`
  (induction on the polynomial).
* `F1_analyticAt_gA`: `(s, z) ↦ gA H s z` is jointly analytic where `Re z > 1/2` and `Re(s - z) > 1/2`.
* `F1_norm_Afun_le`: `|A(w)| ≤ C(1 + |Im w|)^2` on a vertical strip in `Re w > 1/2` (paper 1's `norm_Qcont_le_log` far out,
  compactness near the real axis).
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-! ## `A` -/

/-- **`A(z) = (z - 1)Q(z)` is holomorphic on `Re z > 1/2`** (RH). -/
theorem F1_analyticAt_Afun (hRH : RiemannHypothesis) {z : ℂ} (hz : 1 / 2 < z.re) : AnalyticAt ℂ Afun z := by
  set U : Set ℂ := {w : ℂ | 1 / 2 < w.re} with hUdef
  have hU : IsOpen U := isOpen_lt continuous_const continuous_re
  have h1U : (1 : ℂ) ∈ U := by show (1 / 2 : ℝ) < (1 : ℂ).re; norm_num
  have hdiff : DifferentiableOn ℂ Afun U := by
    have hoff : DifferentiableOn ℂ Afun (U \ {1}) := by
      rintro w ⟨hw, hw1⟩
      have hw1' : w ≠ 1 := hw1
      have hev : (fun u => (u - 1) * Qcont u) =ᶠ[𝓝 w] Afun := by
        filter_upwards [isOpen_compl_singleton.mem_nhds hw1'] with u hu
        have hu' : u ≠ 1 := hu
        simp [Afun, hu']
      have hd : DifferentiableAt ℂ (fun u => (u - 1) * Qcont u) w :=
        (differentiableAt_id.sub_const 1).mul (TIdentity.analyticAt_Qcont_of_RH hRH hw hw1').differentiableAt
      exact (hd.congr_of_eventuallyEq hev.symm).differentiableWithinAt
    have hc : ContinuousAt Afun 1 := by
      rw [← continuousWithinAt_compl_self]
      have hA1 : Afun 1 = 1 := by simp [Afun]
      unfold ContinuousWithinAt
      rw [hA1]
      refine (hasResidue_Qcont_one : Tendsto (fun s => (s - 1) * Qcont s) (𝓝[≠] 1) (𝓝 1)).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with u hu
      have hu' : u ≠ 1 := hu
      simp [Afun, hu']
    exact (differentiableOn_compl_singleton_and_continuousAt_iff (hU.mem_nhds h1U)).mp ⟨hoff, hc⟩
  exact hdiff.analyticAt (hU.mem_nhds hz)

/-! ## Polynomials in two variables -/

/-- A polynomial in two variables is jointly analytic. -/
theorem F1_analyticAt_evalH (G : MvPolynomial (Fin 2) ℂ) (q : ℂ × ℂ) :
    AnalyticAt ℂ (fun q : ℂ × ℂ => evalH G q.1 q.2) q := by
  induction G using MvPolynomial.induction_on with
  | C a =>
    simp only [evalH, MvPolynomial.eval_C]
    exact analyticAt_const
  | add p r hp hr =>
    simp only [evalH, map_add]
    exact hp.add hr
  | mul_X p n hp =>
    simp only [evalH, map_mul, MvPolynomial.eval_X]
    refine hp.mul ?_
    fin_cases n
    · simpa using analyticAt_fst
    · simpa using analyticAt_snd

/-- A polynomial in two variables is `O((1 + |z| + |w|)^d)`. -/
theorem F1_norm_evalH_le (G : MvPolynomial (Fin 2) ℂ) :
    ∃ C : ℝ, ∃ d : ℕ, 0 ≤ C ∧ ∀ z w : ℂ, ‖evalH G z w‖ ≤ C * (1 + ‖z‖ + ‖w‖) ^ d := by
  induction G using MvPolynomial.induction_on with
  | C a =>
    refine ⟨‖a‖, 0, norm_nonneg _, fun z w => ?_⟩
    simp [evalH]
  | add p r hp hr =>
    obtain ⟨C₁, d₁, hC₁, h₁⟩ := hp
    obtain ⟨C₂, d₂, hC₂, h₂⟩ := hr
    refine ⟨C₁ + C₂, d₁ + d₂, add_nonneg hC₁ hC₂, fun z w => ?_⟩
    have hb : 1 ≤ 1 + ‖z‖ + ‖w‖ := by linarith [norm_nonneg z, norm_nonneg w]
    have e₁ : (1 + ‖z‖ + ‖w‖) ^ d₁ ≤ (1 + ‖z‖ + ‖w‖) ^ (d₁ + d₂) :=
      pow_le_pow_right₀ hb (Nat.le_add_right _ _)
    have e₂ : (1 + ‖z‖ + ‖w‖) ^ d₂ ≤ (1 + ‖z‖ + ‖w‖) ^ (d₁ + d₂) :=
      pow_le_pow_right₀ hb (Nat.le_add_left _ _)
    have hsplit : evalH (p + r) z w = evalH p z w + evalH r z w := by simp [evalH]
    rw [hsplit]
    calc ‖evalH p z w + evalH r z w‖ ≤ ‖evalH p z w‖ + ‖evalH r z w‖ := norm_add_le _ _
      _ ≤ C₁ * (1 + ‖z‖ + ‖w‖) ^ d₁ + C₂ * (1 + ‖z‖ + ‖w‖) ^ d₂ := add_le_add (h₁ z w) (h₂ z w)
      _ ≤ C₁ * (1 + ‖z‖ + ‖w‖) ^ (d₁ + d₂) + C₂ * (1 + ‖z‖ + ‖w‖) ^ (d₁ + d₂) := by gcongr
      _ = (C₁ + C₂) * (1 + ‖z‖ + ‖w‖) ^ (d₁ + d₂) := by ring
  | mul_X p n hp =>
    obtain ⟨C, d, hC, h⟩ := hp
    refine ⟨C, d + 1, hC, fun z w => ?_⟩
    have hcoord : ‖(![z, w] : Fin 2 → ℂ) n‖ ≤ 1 + ‖z‖ + ‖w‖ := by
      fin_cases n
      · simp only [Fin.zero_eta, Matrix.cons_val_zero]; linarith [norm_nonneg w]
      · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]; linarith [norm_nonneg z]
    have hsplit : evalH (p * MvPolynomial.X n) z w = evalH p z w * (![z, w] : Fin 2 → ℂ) n := by
      simp [evalH]
    rw [hsplit, norm_mul, pow_succ, ← mul_assoc]
    exact mul_le_mul (h z w) hcoord (norm_nonneg _) (by positivity)

/-! ## The integrand `gA` -/

/-- `Γ` is analytic on `Re w > 0`. -/
theorem F1_analyticAt_Gamma {w : ℂ} (hw : 0 < w.re) : AnalyticAt ℂ Gamma w :=
  DifferentiableOn.analyticAt (s := {u : ℂ | 0 < u.re})
    (fun _ hu => (TIdentity.differentiableAt_Gamma_of_re_pos hu).differentiableWithinAt)
    ((isOpen_lt continuous_const continuous_re).mem_nhds hw)

/-- **`(s, z) ↦ gA H s z` is jointly analytic** where `Re z > 1/2` and `Re(s - z) > 1/2` (RH). -/
theorem F1_analyticAt_gA (hRH : RiemannHypothesis) (H : MvPolynomial (Fin 2) ℂ) {s z : ℂ}
    (hz : 1 / 2 < z.re) (hsz : 1 / 2 < (s - z).re) :
    AnalyticAt ℂ (fun q : ℂ × ℂ => gA H q.1 q.2) (s, z) := by
  have hs : 0 < s.re := by
    have : (s - z).re = s.re - z.re := sub_re s z
    linarith
  have hfst : AnalyticAt ℂ (fun q : ℂ × ℂ => q.1) (s, z) := analyticAt_fst
  have hsnd : AnalyticAt ℂ (fun q : ℂ × ℂ => q.2) (s, z) := analyticAt_snd
  have hdif : AnalyticAt ℂ (fun q : ℂ × ℂ => q.1 - q.2) (s, z) := hfst.sub hsnd
  have hG1 : AnalyticAt ℂ (fun q : ℂ × ℂ => Gamma q.2) (s, z) :=
    AnalyticAt.comp (g := Gamma) (f := fun q : ℂ × ℂ => q.2) (F1_analyticAt_Gamma (by linarith : 0 < z.re)) hsnd
  have hG2 : AnalyticAt ℂ (fun q : ℂ × ℂ => Gamma (q.1 - q.2)) (s, z) :=
    AnalyticAt.comp (g := Gamma) (f := fun q : ℂ × ℂ => q.1 - q.2) (F1_analyticAt_Gamma (by linarith : 0 < (s - z).re))
      hdif
  have hG3 : AnalyticAt ℂ (fun q : ℂ × ℂ => Gamma q.1) (s, z) := AnalyticAt.comp (g := Gamma) (f := fun q : ℂ × ℂ => q.1) (F1_analyticAt_Gamma hs) hfst
  have hP : AnalyticAt ℂ (fun q : ℂ × ℂ => evalH (Gpoly H) q.2 (q.1 - q.2)) (s, z) :=
    AnalyticAt.comp (g := fun q : ℂ × ℂ => evalH (Gpoly H) q.1 q.2) (f := fun q : ℂ × ℂ => (q.2, q.1 - q.2))
      (F1_analyticAt_evalH (Gpoly H) (z, s - z)) (hsnd.prod hdif)
  have hA1 : AnalyticAt ℂ (fun q : ℂ × ℂ => Afun q.2) (s, z) := 
    AnalyticAt.comp (g := Afun) (f := fun q : ℂ × ℂ => q.2) (F1_analyticAt_Afun hRH hz) hsnd
  have hA2 : AnalyticAt ℂ (fun q : ℂ × ℂ => Afun (q.1 - q.2)) (s, z) :=
    AnalyticAt.comp (g := Afun) (f := fun q : ℂ × ℂ => q.1 - q.2) (F1_analyticAt_Afun hRH hsz) hdif
  have hK : AnalyticAt ℂ (fun q : ℂ × ℂ => KerS q.1 q.2) (s, z) :=
    (hG1.mul hG2).div hG3 (Complex.Gamma_ne_zero_of_re_pos hs)
  exact ((hK.mul hP).mul hA1).mul hA2

/-- `gA H s` is complex differentiable in `z` where `Re z > 1/2`, `Re(s - z) > 1/2`. -/
theorem F1_differentiableAt_gA_z (hRH : RiemannHypothesis) (H : MvPolynomial (Fin 2) ℂ) {s z : ℂ}
    (hz : 1 / 2 < z.re) (hsz : 1 / 2 < (s - z).re) : DifferentiableAt ℂ (gA H s) z := by
  have h := AnalyticAt.comp (g := fun q : ℂ × ℂ => gA H q.1 q.2) (f := fun w : ℂ => (s, w)) (x := z)
    (F1_analyticAt_gA hRH H hz hsz) (analyticAt_const.prod analyticAt_id)
  exact h.differentiableAt

/-- `s ↦ gA H s z` is complex differentiable where `Re z > 1/2`, `Re(s - z) > 1/2`. -/
theorem F1_differentiableAt_gA_s (hRH : RiemannHypothesis) (H : MvPolynomial (Fin 2) ℂ) {s z : ℂ}
    (hz : 1 / 2 < z.re) (hsz : 1 / 2 < (s - z).re) : DifferentiableAt ℂ (fun s => gA H s z) s := by
  have h := AnalyticAt.comp (g := fun q : ℂ × ℂ => gA H q.1 q.2) (f := fun t : ℂ => (t, z)) (x := s)
    (F1_analyticAt_gA hRH H hz hsz) (analyticAt_id.prod analyticAt_const)
  exact h.differentiableAt

/-! ## Bounds -/

/-- **`|A(w)| ≤ C(1 + |Im w|)^2` on a vertical strip in `Re w > 1/2`** (RH). -/
theorem F1_norm_Afun_le (hRH : RiemannHypothesis) {a b : ℝ} (ha : 1 / 2 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, a ≤ w.re → w.re ≤ b → ‖Afun w‖ ≤ C * (1 + |w.im|) ^ 2 := by
  obtain ⟨C₀, hC₀⟩ := TIdentity.norm_Qcont_le_log hRH (ε := a - 1 / 2) (by linarith)
  -- the compact part `|Im w| ≤ 4`
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Afun ((p.1 : ℂ) + p.2 * I)) (Icc a b ×ˢ Icc (-4) 4) := by
    rintro ⟨x, y⟩ ⟨hx, -⟩
    have hre : 1 / 2 < ((x : ℂ) + y * I).re := by simp; linarith [hx.1]
    exact (ContinuousAt.comp (g := Afun) (f := fun p : ℝ × ℝ => (p.1 : ℂ) + p.2 * I) (x := (x, y))
      (F1_analyticAt_Afun hRH hre).continuousAt (by fun_prop)).continuousWithinAt
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hcont
  set L : ℝ := |a| + |b| + 1 with hL
  refine ⟨max B 0 + L * max C₀ 0, by positivity, fun w hwa hwb => ?_⟩
  have hy0 : 0 ≤ |w.im| := abs_nonneg _
  have h1y : 1 ≤ (1 + |w.im|) ^ 2 := one_le_pow₀ (by linarith)
  by_cases hy : |w.im| ≤ 4
  · have hw := hB (w.re, w.im) ⟨⟨hwa, hwb⟩, abs_le.mp hy⟩
    simp only [re_add_im] at hw
    calc ‖Afun w‖ ≤ max B 0 := hw.trans (le_max_left _ _)
      _ ≤ max B 0 * (1 + |w.im|) ^ 2 := le_mul_of_one_le_right (le_max_right _ _) h1y
      _ ≤ (max B 0 + L * max C₀ 0) * (1 + |w.im|) ^ 2 := by
          gcongr
          have : 0 ≤ L * max C₀ 0 := by positivity
          linarith
  · push Not at hy
    have hw1 : w ≠ 1 := fun h => by rw [h, one_im, abs_zero] at hy; norm_num at hy
    have hAw : Afun w = (w - 1) * Qcont w := by simp [Afun, hw1]
    have hQ := hC₀ w (by linarith) hy.le
    have hlog : Real.log |w.im| ≤ 1 + |w.im| := by
      have := Real.log_le_sub_one_of_pos (by linarith : 0 < |w.im|)
      linarith
    have hlog0 : 0 ≤ Real.log |w.im| := Real.log_nonneg (by linarith)
    have hQ' : ‖Qcont w‖ ≤ max C₀ 0 * (1 + |w.im|) :=
      hQ.trans ((mul_le_mul_of_nonneg_right (le_max_left _ _) hlog0).trans
        (mul_le_mul_of_nonneg_left hlog (le_max_right _ _)))
    have hw1n : ‖w - 1‖ ≤ L * (1 + |w.im|) := by
      have h := norm_le_abs_re_add_abs_im (w - 1)
      have hre : |(w - 1).re| ≤ |a| + |b| + 1 := by
        rw [sub_re, one_re]
        refine (abs_sub _ _).trans ?_
        rw [abs_one]
        have : |w.re| ≤ |a| + |b| := abs_le.mpr ⟨by linarith [neg_abs_le a, abs_nonneg b],
          by linarith [le_abs_self b, abs_nonneg a]⟩
        linarith
      have him : (w - 1).im = w.im := by simp
      rw [him] at h
      have hL1 : 1 ≤ L := by rw [hL]; linarith [abs_nonneg a, abs_nonneg b]
      nlinarith
    rw [hAw, norm_mul]
    calc ‖w - 1‖ * ‖Qcont w‖ ≤ (L * (1 + |w.im|)) * (max C₀ 0 * (1 + |w.im|)) :=
          mul_le_mul hw1n hQ' (norm_nonneg _) (by positivity)
      _ = L * max C₀ 0 * (1 + |w.im|) ^ 2 := by ring
      _ ≤ (max B 0 + L * max C₀ 0) * (1 + |w.im|) ^ 2 := by
          gcongr
          linarith [le_max_right B 0]

/-- **`gA` is `O((1 + |Im z|)^{-2})` on strips, uniformly on compacts** (RH). -/
theorem F1_norm_gA_le (hRH : RiemannHypothesis) (H : MvPolynomial (Fin 2) ℂ) {K : Set ℂ} (hK : IsCompact K)
    {c₁ c₂ : ℝ} (hc₁ : 1 / 2 < c₁) (hc₁₂ : c₁ ≤ c₂) (hc₂ : ∀ s ∈ K, c₂ + 1 / 2 < s.re) :
    ∃ M : ℝ, ∀ s ∈ K, ∀ z : ℂ, c₁ ≤ z.re → z.re ≤ c₂ → ‖gA H s z‖ ≤ M / (1 + |z.im|) ^ 2 := by
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · exact ⟨0, fun s hs => by simp [hKe] at hs⟩
  obtain ⟨s₀, hs₀K, hmin⟩ := hK.exists_isMinOn hKne continuous_re.continuousOn
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  have hR0 : 0 ≤ R := (norm_nonneg _).trans (hR s₀ hs₀K)
  have hσ₁ : c₂ + 1 / 2 < s₀.re := hc₂ s₀ hs₀K
  obtain ⟨CG, d, hCG0, hCG⟩ := F1_norm_evalH_le (Gpoly H)
  obtain ⟨CK, hCK⟩ := norm_KerS_mul_pow_le (x₁ := c₁) (x₂ := c₂) (σ₁ := s₀.re) (σ₂ := R) (τ₀ := R)
    (by linarith) (by linarith) (d + 6)
  obtain ⟨CA, hCA0, hCA⟩ := F1_norm_Afun_le hRH (a := c₁) (b := c₂) hc₁
  obtain ⟨CA', hCA'0, hCA'⟩ := F1_norm_Afun_le hRH (a := s₀.re - c₂) (b := R - c₁) (by linarith)
  set B : ℝ := 1 + 2 * c₂ + R with hB
  set P : ℝ := CG * B ^ d * CA * (CA' * (1 + R) ^ 2) with hP
  have hB0 : 0 ≤ B := by rw [hB]; linarith
  have hP0 : 0 ≤ P := by positivity
  refine ⟨CK * P, fun s hs z hz1 hz2 => ?_⟩
  set y : ℝ := |z.im| with hy
  have hy0 : 0 ≤ y := abs_nonneg _
  have hsR : ‖s‖ ≤ R := hR s hs
  have hsre : s.re ≤ R := (re_le_norm s).trans hsR
  have hsim : |s.im| ≤ R := (abs_im_le_norm s).trans hsR
  have hs₀s : s₀.re ≤ s.re := hmin hs
  -- the kernel
  have hKz : ‖KerS s z‖ * (1 + y) ^ (d + 6) ≤ CK := hCK s hs₀s hsre hsim z hz1 hz2
  -- the polynomial
  have hzn : ‖z‖ ≤ c₂ + y := by
    have h := norm_le_abs_re_add_abs_im z
    rw [abs_of_pos (by linarith : 0 < z.re)] at h
    linarith
  have hszn : ‖s - z‖ ≤ R + c₂ + y := (norm_sub_le s z).trans (by linarith)
  have hbase : 1 + ‖z‖ + ‖s - z‖ ≤ B * (1 + y) := by
    rw [hB]; nlinarith
  have hGz : ‖evalH (Gpoly H) z (s - z)‖ ≤ CG * B ^ d * (1 + y) ^ d := by
    refine (hCG z (s - z)).trans ?_
    rw [mul_assoc, ← mul_pow]
    gcongr
  -- `A(z)` and `A(s - z)`
  have hAz : ‖Afun z‖ ≤ CA * (1 + y) ^ 2 := hCA z hz1 hz2
  have hAsz : ‖Afun (s - z)‖ ≤ CA' * (1 + R) ^ 2 * (1 + y) ^ 2 := by
    have h := hCA' (s - z) (by rw [sub_re]; linarith) (by rw [sub_re]; linarith)
    have him : 1 + |(s - z).im| ≤ (1 + R) * (1 + y) := by
      rw [sub_im]
      have := abs_sub s.im z.im
      nlinarith
    refine h.trans ?_
    rw [mul_assoc, ← mul_pow]
    gcongr
  -- assemble
  have hpos : 0 < (1 + y) ^ 2 := by positivity
  rw [le_div_iff₀ hpos]
  unfold gA
  rw [norm_mul, norm_mul, norm_mul]
  calc ‖KerS s z‖ * ‖evalH (Gpoly H) z (s - z)‖ * ‖Afun z‖ * ‖Afun (s - z)‖ * (1 + y) ^ 2
      ≤ ‖KerS s z‖ * (CG * B ^ d * (1 + y) ^ d) * (CA * (1 + y) ^ 2) *
          (CA' * (1 + R) ^ 2 * (1 + y) ^ 2) * (1 + y) ^ 2 := by gcongr
    _ = (‖KerS s z‖ * (1 + y) ^ (d + 6)) * P := by rw [hP]; ring
    _ ≤ CK * P := mul_le_mul_of_nonneg_right hKz hP0

/-! ## Line integrals -/

/-- `M (1 + |y|)^{-2}` is integrable. -/
theorem F1_integrable_inv_sq (M : ℝ) : Integrable (fun y : ℝ => M / (1 + |y|) ^ 2) := by
  refine ((integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by simp)).const_mul M).congr
    (Eventually.of_forall fun y => ?_)
  have hpos : 0 < 1 + |y| := by positivity
  show M * (1 + ‖y‖) ^ (-(2 : ℝ)) = M / (1 + |y|) ^ 2
  rw [Real.norm_eq_abs, Real.rpow_neg hpos.le, div_eq_mul_inv]
  norm_cast

/-- Joint continuity of `(s, y) ↦ gA H s (c + iy)` for `Re s > c + 1/2`. -/
theorem F1_continuousAt_gA_line (hRH : RiemannHypothesis) (H : MvPolynomial (Fin 2) ℂ) {c : ℝ}
    (hc : 1 / 2 < c) {s : ℂ} (hs : c + 1 / 2 < s.re) (y : ℝ) :
    ContinuousAt (fun p : ℂ × ℝ => gA H p.1 (c + p.2 * I)) (s, y) := by
  have hz : 1 / 2 < ((c : ℂ) + y * I).re := by simp; linarith
  have hsz : 1 / 2 < (s - ((c : ℂ) + y * I)).re := by simp; linarith
  exact ContinuousAt.comp (g := fun q : ℂ × ℂ => gA H q.1 q.2) (f := fun p : ℂ × ℝ => (p.1, (c : ℂ) + p.2 * I))
    (x := (s, y)) (F1_analyticAt_gA hRH H hz hsz).continuousAt (by fun_prop)

/-- **Holomorphy of `FilLine H c` and integrability on its line** (RH). -/
theorem F1_differentiableOn_FilLine (hRH : RiemannHypothesis) (H : MvPolynomial (Fin 2) ℂ) {c : ℝ}
    (hc : 1 / 2 < c) :
    DifferentiableOn ℂ (FilLine H c) {s | c + 1 / 2 < s.re} ∧
      ∀ s : ℂ, c + 1 / 2 < s.re → Integrable (fun y : ℝ => gA H s (c + y * I)) := by
  set U : Set ℂ := {s | c + 1 / 2 < s.re} with hUdef
  have hU : IsOpen U := isOpen_lt continuous_const continuous_re
  have hre : ∀ y : ℝ, ((c : ℂ) + y * I).re = c := fun y => by simp
  have hcont : ContinuousOn (fun p : ℂ × ℝ => gA H p.1 (c + p.2 * I)) (U ×ˢ univ) := by
    rintro ⟨s, y⟩ ⟨hs, -⟩
    exact (F1_continuousAt_gA_line hRH H hc hs y).continuousWithinAt
  have hhol : ∀ y : ℝ, DifferentiableOn ℂ (fun s => gA H s (c + y * I)) U := by
    intro y s hs
    have hs' : c + 1 / 2 < s.re := hs
    refine (F1_differentiableAt_gA_s hRH H (by rw [hre]; linarith) ?_).differentiableWithinAt
    rw [sub_re, hre]; linarith
  have hdom : ∀ K ⊆ U, IsCompact K → ∃ g : ℝ → ℝ, Integrable g ∧
      ∀ s ∈ K, ∀ y : ℝ, ‖gA H s (c + y * I)‖ ≤ g y := by
    intro K hKU hK
    obtain ⟨M, hM⟩ := F1_norm_gA_le hRH H hK hc le_rfl fun s hs => hKU hs
    refine ⟨fun y => M / (1 + |y|) ^ 2, F1_integrable_inv_sq M, fun s hs y => ?_⟩
    have h := hM s hs ((c : ℂ) + y * I) (by rw [hre]) (by rw [hre])
    simpa using h
  refine ⟨differentiableOn_verticalIntegral' hU hcont hhol hdom, fun s hs => ?_⟩
  obtain ⟨g, hg, hgb⟩ := hdom {s} (singleton_subset_iff.mpr hs) isCompact_singleton
  have hcl : Continuous (fun y : ℝ => gA H s (c + y * I)) := by
    rw [continuous_iff_continuousAt]
    intro y
    exact ContinuousAt.comp (g := fun p : ℂ × ℝ => gA H p.1 (c + p.2 * I)) (f := fun y : ℝ => (s, y))
      (F1_continuousAt_gA_line hRH H hc hs y) (by fun_prop)
  exact hg.mono' hcl.aestronglyMeasurable (Eventually.of_forall (hgb s rfl))

/-- `M / (1 + |y|)^2 → 0` along any filter on which `|y| → ∞`. -/
theorem F1_tendsto_div_sq {l : Filter ℝ} (hl : Tendsto (fun y : ℝ => |y|) l atTop) (M : ℝ) :
    Tendsto (fun y : ℝ => M / (1 + |y|) ^ 2) l (𝓝 0) := by
  have h1 : Tendsto (fun y : ℝ => (1 + |y|) ^ 2) l atTop :=
    (tendsto_pow_atTop two_ne_zero).comp (tendsto_atTop_add_const_left _ 1 hl)
  have h2 := h1.inv_tendsto_atTop.const_mul M
  rw [mul_zero] at h2
  exact h2.congr fun y => (div_eq_mul_inv _ _).symm

/-- **`FilLine H c s` does not depend on `c ∈ (1/2, σ - 1/2)`** (RH). -/
theorem F1_FilLine_eq_of_le (hRH : RiemannHypothesis) (H : MvPolynomial (Fin 2) ℂ) {s : ℂ} {c c' : ℝ}
    (hc : 1 / 2 < c) (hcc' : c ≤ c') (hc' : c' + 1 / 2 < s.re) : FilLine H c' s = FilLine H c s := by
  obtain ⟨M, hM⟩ := F1_norm_gA_le hRH H (K := {s}) isCompact_singleton hc hcc'
    (fun t ht => by rw [mem_singleton_iff.mp ht]; exact hc')
  have hhor : ∀ y : ℝ, ‖∫ x in c..c', gA H s (x + y * I)‖ ≤ M / (1 + |y|) ^ 2 * |c' - c| := by
    intro y
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
    rw [uIoc_of_le hcc'] at hx
    have h := hM s rfl ((x : ℂ) + y * I) (by simp; exact hx.1.le) (by simp; exact hx.2)
    simpa using h
  have hlim : ∀ {l : Filter ℝ}, Tendsto (fun y : ℝ => |y|) l atTop →
      Tendsto (fun y : ℝ => ∫ x in c..c', gA H s (x + y * I)) l (𝓝 0) := by
    intro l hl
    refine squeeze_zero_norm hhor ?_
    simpa using (F1_tendsto_div_sq hl M).mul_const |c' - c|
  have hS : ∀ p ∈ (∅ : Finset ℂ), c < p.re ∧ p.re < c' := by simp
  have hf : DifferentiableOn ℂ (gA H s) (Icc c c' ×ℂ univ \ ((∅ : Finset ℂ) : Set ℂ)) := by
    rintro z ⟨hz, -⟩
    rw [mem_reProdIm] at hz
    refine (F1_differentiableAt_gA_z hRH H (by linarith [hz.1.1]) ?_).differentiableWithinAt
    rw [sub_re]; linarith [hz.1.2]
  have h := verticalIntegral'_eq_add_sum_of_simplePoles (f := gA H s) ∅ (fun _ => 0) hcc' hS hf (by simp)
    (hlim tendsto_abs_atBot_atTop) (hlim tendsto_abs_atTop_atTop)
    ((F1_differentiableOn_FilLine hRH H hc).2 s (by linarith))
    ((F1_differentiableOn_FilLine hRH H (by linarith)).2 s hc')
  simpa [FilLine] using h

/-- **`Fil` is holomorphic on `ℍ`** (RH). -/
theorem F1_differentiableOn_Fil (hRH : RiemannHypothesis) (H : MvPolynomial (Fin 2) ℂ) :
    DifferentiableOn ℂ (Fil H) HH := by
  intro s₀ hs₀
  have hs₀' : 1 < s₀.re := hs₀
  set c : ℝ := s₀.re / 2 with hcdef
  have hc : 1 / 2 < c := by rw [hcdef]; linarith
  set V : Set ℂ := {s | c + 1 / 2 < s.re} with hVdef
  have hV : IsOpen V := isOpen_lt continuous_const continuous_re
  have hs₀V : s₀ ∈ V := by show c + 1 / 2 < s₀.re; rw [hcdef]; linarith
  have heq : EqOn (Fil H) (FilLine H c) V := by
    intro s hs
    have hs' : c + 1 / 2 < s.re := hs
    have h1 : 1 < s.re := by linarith
    show FilLine H (s.re / 2) s = FilLine H c s
    rcases le_total c (s.re / 2) with hle | hle
    · exact F1_FilLine_eq_of_le hRH H hc hle (by linarith)
    · exact (F1_FilLine_eq_of_le hRH H (by linarith) hle (by linarith)).symm
  have hd : DifferentiableAt ℂ (FilLine H c) s₀ :=
    ((F1_differentiableOn_FilLine hRH H hc).1 s₀ hs₀V).differentiableAt (hV.mem_nhds hs₀V)
  exact (hd.congr_of_eventuallyEq (heq.eventuallyEq_of_mem (hV.mem_nhds hs₀V))).differentiableWithinAt

/-! ## `H₀` -/

/-- `H₀ = (z - 1)(w - 1) Gpoly H₀`, from the explicit factor `G = 1` (no appeal to `exists_factor_H`). -/
theorem F1_evalH_H0f_eq_Gpoly (z w : ℂ) :
    evalH H0f z w = (z - 1) * (w - 1) * evalH (Gpoly H0f) z w := by
  have h : ∃ G : MvPolynomial (Fin 2) ℂ, ∀ z w, evalH H0f z w = (z - 1) * (w - 1) * evalH G z w :=
    ⟨1, fun z w => by simp [evalH, H0f]⟩
  unfold Gpoly
  rw [dite_eq_left h]
  exact h.choose_spec z w

/-- **`Fil H₀ = D_{H₀}` on `σ > 2`** (as `Fil_eq_DH`, with the explicit factor of `H₀`). -/
theorem F1_Fil_eq_DH_H0f : EqOn (Fil H0f) (DH H0f) (halfPlane 2) := by
  intro s hs
  have hs' : 2 < s.re := hs
  unfold Fil FilLine DH VerticalIntegral' VerticalIntegral
  congr 3
  funext y
  set z : ℂ := (s.re / 2 : ℝ) + y * I with hz
  have hzre : z.re = s.re / 2 := by simp [hz]
  have hszre : (s - z).re = s.re / 2 := by simp [hz]; ring
  have hz1 : z ≠ 1 := fun h => by rw [h, one_re] at hzre; linarith
  have hsz1 : s - z ≠ 1 := fun h => by rw [h, one_re] at hszre; linarith
  unfold gA kH Afun
  show _ = KerS s z * evalH H0f z (s - z) * Q z * Q (s - z)
  rw [ite_eq_right hz1, ite_eq_right hsz1, F1_evalH_H0f_eq_Gpoly z (s - z),
    TIdentity.Qcont_eq_Q_of_one_lt (by rw [hzre]; linarith),
    TIdentity.Qcont_eq_Q_of_one_lt (by rw [hszre]; linarith)]
  ring

end GoldbachBoundaries.Paper2.M5
