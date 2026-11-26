import GoldbachBoundaries.Paper2.M5.Qleft

/-!
# Fill, group T2: shared helpers for the line integrals `TkLine` of Theorem G

* `T2.differentiableAt_KerS_joint`, `T2.differentiableAt_KerS_slice`: `K_s(w)` is holomorphic in `(w, s)` where
  `Re w > 0` and `Re(s - w) > 0`.
* `T2.differentiableAt_integrand`: the integrand `K_s(w) F(w) Qcont(s - w)` is jointly holomorphic off the poles.
* `T2.norm_far`: the proof of `norm_TkIntegrand_le_far` (M4b's `norm_integrand_le_far` with `F` in place of the first
  `Q` factor: field 8 of the package bounds `F` polynomially, and the kernel decay absorbs it).
* `T2.line_facts`: the hypotheses of M1's `differentiableOn_verticalIntegral'` on the open set
  `{c + 1/2 < σ, σ - c ≠ 1}` (as M4b's `Ilog_line_facts`).
* `T2.shift`: M1's `verticalIntegral'_eq_add_sum_of_simplePoles` for `TkLine` with tails and integrability discharged
  (as M4b's `Ilog_shift`).
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2

lemma T2.differentiableAt_KerS_joint {w s : ℂ} (hw : 0 < w.re) (hsw : 0 < (s - w).re) :
    DifferentiableAt ℂ (fun p : ℂ × ℂ => KerS p.2 p.1) (w, s) := by
  have hs : 0 < s.re := by simp at hsw; linarith
  unfold KerS
  have h1 : DifferentiableAt ℂ (fun p : ℂ × ℂ => Gamma p.1) (w, s) :=
    DifferentiableAt.comp (f := fun p : ℂ × ℂ => p.1) (w, s)
      (TIdentity.differentiableAt_Gamma_of_re_pos hw) differentiableAt_fst
  have h2 : DifferentiableAt ℂ (fun p : ℂ × ℂ => Gamma (p.2 - p.1)) (w, s) :=
    DifferentiableAt.comp (f := fun p : ℂ × ℂ => p.2 - p.1) (w, s)
      (TIdentity.differentiableAt_Gamma_of_re_pos hsw) (differentiableAt_snd.sub differentiableAt_fst)
  have h3 : DifferentiableAt ℂ (fun p : ℂ × ℂ => Gamma p.2) (w, s) :=
    DifferentiableAt.comp (f := fun p : ℂ × ℂ => p.2) (w, s)
      (TIdentity.differentiableAt_Gamma_of_re_pos hs) differentiableAt_snd
  simp only [div_eq_mul_inv]
  exact (h1.mul h2).mul (h3.inv (Complex.Gamma_ne_zero_of_re_pos hs))

lemma T2.differentiableAt_KerS_slice {w s : ℂ} (hw : 0 < w.re) (hsw : 0 < (s - w).re) :
    DifferentiableAt ℂ (fun z => KerS s z) w :=
  DifferentiableAt.comp (f := fun z : ℂ => (z, s)) w (T2.differentiableAt_KerS_joint hw hsw) (by fun_prop)

/-- The integrand is jointly holomorphic in `(w, s)` off the poles `w = m` and `s - w = 1`. -/
lemma T2.differentiableAt_integrand (hRH : RiemannHypothesis) {m : ℕ} (hm : 1 ≤ m) {F H : ℂ → ℂ}
    (hP : TkPack m F H) {w s : ℂ} (hw : (m : ℝ) - 1 / 2 < w.re) (hwm : w ≠ m) (hsw : 1 / 2 < (s - w).re)
    (hsw1 : s - w ≠ 1) :
    DifferentiableAt ℂ (fun p : ℂ × ℂ => KerS p.2 p.1 * F p.1 * Qcont (p.2 - p.1)) (w, s) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hK := T2.differentiableAt_KerS_joint (w := w) (s := s) (by linarith) (by linarith)
  have hF : DifferentiableAt ℂ (fun p : ℂ × ℂ => F p.1) (w, s) :=
    DifferentiableAt.comp (f := fun p : ℂ × ℂ => p.1) (w, s)
      (hP.2.2.2.2.1 w hw hwm).differentiableAt differentiableAt_fst
  have hQ : DifferentiableAt ℂ (fun p : ℂ × ℂ => Qcont (p.2 - p.1)) (w, s) :=
    DifferentiableAt.comp (f := fun p : ℂ × ℂ => p.2 - p.1) (w, s)
      (TIdentity.analyticAt_Qcont_of_RH hRH hsw hsw1).differentiableAt
      (differentiableAt_snd.sub differentiableAt_fst)
  exact (hK.mul hF).mul hQ

lemma T2.differentiableAt_integrand_slice (hRH : RiemannHypothesis) {m : ℕ} (hm : 1 ≤ m) {F H : ℂ → ℂ}
    (hP : TkPack m F H) {w s : ℂ} (hw : (m : ℝ) - 1 / 2 < w.re) (hwm : w ≠ m) (hsw : 1 / 2 < (s - w).re)
    (hsw1 : s - w ≠ 1) :
    DifferentiableAt ℂ (fun w => KerS s w * F w * Qcont (s - w)) w :=
  DifferentiableAt.comp (f := fun z : ℂ => (z, s)) w
    (T2.differentiableAt_integrand hRH hm hP hw hwm hsw hsw1) (by fun_prop)

/-- The proof of `norm_TkIntegrand_le_far`. -/
theorem T2.norm_far (hRH : RiemannHypothesis) {m : ℕ} (hm : 1 ≤ m) {F H : ℂ → ℂ} (hP : TkPack m F H)
    {K : Set ℂ} (hK : IsCompact K) {c₁ c₂ : ℝ} (hc₁ : (m : ℝ) - 1 / 2 < c₁) (hc₁₂ : c₁ ≤ c₂)
    (hc₂ : ∀ s ∈ K, c₂ + 1 / 2 < s.re) :
    ∃ M Y : ℝ, ∀ s ∈ K, ∀ w : ℂ, c₁ ≤ w.re → w.re ≤ c₂ → Y ≤ |w.im| →
      ‖KerS s w * F w * Qcont (s - w)‖ ≤ M / (1 + |w.im|) ^ 2 := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, 0, fun s hs => absurd hs (Set.notMem_empty s)⟩
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  obtain ⟨N, CF, y₀, hF⟩ := hP.2.2.2.2.2.2.2 c₁ c₂ hc₁ hc₁₂
  obtain ⟨s₀, hs₀K, hs₀min⟩ := hK.exists_isMinOn hne Complex.continuous_re.continuousOn
  obtain ⟨s₁, hs₁K, hs₁max⟩ := hK.exists_isMaxOn hne Complex.continuous_re.continuousOn
  obtain ⟨T, hT⟩ := hK.exists_bound_of_continuousOn Complex.continuous_im.continuousOn
  set T' : ℝ := max T 0 with hT'
  have hT'0 : 0 ≤ T' := le_max_right _ _
  set ε : ℝ := s₀.re - c₂ - 1 / 2 with hε
  have hεpos : 0 < ε := by linarith [hc₂ s₀ hs₀K]
  obtain ⟨CQ, hCQ⟩ := TIdentity.norm_Qcont_le_log hRH hεpos
  set n₀ : ℕ := ⌈max N 0⌉₊ with hn₀
  obtain ⟨CK, hCK⟩ := M1.norm_KerS_mul_pow_le (x₁ := c₁) (x₂ := c₂) (σ₁ := s₀.re) (σ₂ := s₁.re)
    (τ₀ := T') (by linarith) (by linarith [hc₂ s₀ hs₀K]) (n₀ + 3)
  set CF' : ℝ := max CF 0 with hCF'
  set CQ' : ℝ := max CQ 0 with hCQ'
  set CK' : ℝ := max CK 0 with hCK'
  have hCF'0 : 0 ≤ CF' := le_max_right _ _
  have hCQ'0 : 0 ≤ CQ' := le_max_right _ _
  have hCK'0 : 0 ≤ CK' := le_max_right _ _
  refine ⟨CK' * CF' * CQ' * (1 + T'), max (max y₀ 1) (T' + 4), ?_⟩
  intro s hs w hw1 hw2 hY
  set y : ℝ := w.im with hy
  have hy0 : y₀ ≤ |y| := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hY
  have hy1 : 1 ≤ |y| := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hY
  have hyT : T' + 4 ≤ |y| := le_trans (le_max_right _ _) hY
  set u : ℝ := 1 + |y| with hu
  have hu1 : 1 ≤ u := by linarith [abs_nonneg y]
  have hu0 : 0 < u := by linarith
  have hT's : |s.im| ≤ T' := le_trans (by simpa using hT s hs) (le_max_left _ _)
  -- `F`
  have hFw : ‖F w‖ ≤ CF' * u ^ n₀ := by
    have h := hF w.re ⟨hw1, hw2⟩ w.im hy0
    rw [Complex.re_add_im] at h
    have hpow1 : |y| ^ N ≤ |y| ^ (max N 0) :=
      Real.rpow_le_rpow_of_exponent_le hy1 (le_max_left _ _)
    have hpow2 : |y| ^ (max N 0) ≤ |y| ^ (n₀ : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hy1 (Nat.le_ceil _)
    have hpow3 : |y| ^ (n₀ : ℝ) ≤ u ^ n₀ := by
      rw [Real.rpow_natCast]
      exact pow_le_pow_left₀ (abs_nonneg _) (by linarith) _
    have hpos : 0 ≤ |y| ^ N := Real.rpow_nonneg (abs_nonneg _) _
    calc ‖F w‖ ≤ CF * |y| ^ N := h
      _ ≤ CF' * |y| ^ N := mul_le_mul_of_nonneg_right (le_max_left _ _) hpos
      _ ≤ CF' * u ^ n₀ := mul_le_mul_of_nonneg_left (hpow1.trans (hpow2.trans hpow3)) hCF'0
  -- the kernel
  have hKw : ‖KerS s w‖ ≤ CK' / u ^ (n₀ + 3) := by
    have h := hCK s (hs₀min hs) (hs₁max hs) hT's w hw1 hw2
    rw [le_div_iff₀ (by positivity)]
    exact h.trans (le_max_left _ _)
  -- `Qcont(s - w)`
  have hre : 1 / 2 + ε ≤ (s - w).re := by
    have := hs₀min hs
    simp only [Complex.sub_re]
    simp only [mem_ofPred_eq] at this
    linarith
  have him : (s - w).im = s.im - y := by simp [hy]
  have him_lo : 4 ≤ |(s - w).im| := by
    rw [him]
    have := abs_sub_abs_le_abs_sub y s.im
    rw [abs_sub_comm y] at this
    linarith
  have him_hi : |(s - w).im| ≤ (1 + T') * u := by
    rw [him]
    have := abs_sub s.im y
    nlinarith [abs_nonneg y]
  have hQw : ‖Qcont (s - w)‖ ≤ CQ' * ((1 + T') * u) := by
    refine (hCQ _ hre him_lo).trans ?_
    have hl0 : 0 ≤ Real.log |(s - w).im| := Real.log_nonneg (by linarith)
    have hl1 : Real.log |(s - w).im| ≤ |(s - w).im| := by
      have := Real.log_le_sub_one_of_pos (x := |(s - w).im|) (by linarith)
      linarith
    calc CQ * Real.log |(s - w).im| ≤ CQ' * Real.log |(s - w).im| :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hl0
      _ ≤ CQ' * ((1 + T') * u) := mul_le_mul_of_nonneg_left (hl1.trans him_hi) hCQ'0
  rw [norm_mul, norm_mul]
  calc ‖KerS s w‖ * ‖F w‖ * ‖Qcont (s - w)‖
      ≤ (CK' / u ^ (n₀ + 3)) * (CF' * u ^ n₀) * (CQ' * ((1 + T') * u)) :=
        mul_le_mul (mul_le_mul hKw hFw (norm_nonneg _) (by positivity)) hQw (norm_nonneg _)
          (by positivity)
    _ = CK' * CF' * CQ' * (1 + T') / u ^ 2 := by
        rw [pow_add]
        field_simp

/-- The facts M1's `differentiableOn_verticalIntegral'` needs for `TkLine F c`. -/
lemma T2.line_facts (hRH : RiemannHypothesis) {m : ℕ} (hm : 1 ≤ m) {F H : ℂ → ℂ} (hP : TkPack m F H)
    {c : ℝ} (hc : (m : ℝ) - 1 / 2 < c) (hcm : c ≠ m) :
    let U := {s : ℂ | c + 1 / 2 < s.re ∧ s.re - c ≠ 1}
    let G : ℂ → ℂ → ℂ := fun s w => KerS s w * F w * Qcont (s - w)
    IsOpen U ∧ ContinuousOn (fun p : ℂ × ℝ => G p.1 (c + p.2 * I)) (U ×ˢ univ) ∧
      (∀ y : ℝ, DifferentiableOn ℂ (fun s => G s (c + y * I)) U) ∧
      ∀ K ⊆ U, IsCompact K → ∃ g : ℝ → ℝ, Integrable g ∧
        ∀ s ∈ K, ∀ y : ℝ, ‖G s (c + y * I)‖ ≤ g y := by
  intro U G
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_ne_fun (Complex.continuous_re.sub continuous_const) continuous_const)
  have hpt : ∀ s ∈ U, ∀ y : ℝ, DifferentiableAt ℂ
      (fun p : ℂ × ℂ => KerS p.2 p.1 * F p.1 * Qcont (p.2 - p.1)) ((c : ℂ) + y * I, s) := by
    intro s hs y
    obtain ⟨hcs, hne⟩ := hs
    apply T2.differentiableAt_integrand hRH hm hP
    · simpa using hc
    · intro h; have := congrArg Complex.re h; simp at this; exact hcm this
    · have h : (s - ((c : ℂ) + y * I)).re = s.re - c := by simp
      rw [h]; linarith
    · intro h; have := congrArg Complex.re h; simp at this; exact hne (by linarith)
  have hcont : ContinuousOn (fun p : ℂ × ℝ => G p.1 (c + p.2 * I)) (U ×ˢ univ) := by
    intro p hp
    have := (hpt p.1 hp.1 p.2).continuousAt.comp
      (f := fun q : ℂ × ℝ => ((c : ℂ) + q.2 * I, q.1)) (by fun_prop)
    exact this.continuousWithinAt
  have hhol : ∀ y : ℝ, DifferentiableOn ℂ (fun s => G s (c + y * I)) U := by
    intro y s hs
    exact (DifferentiableAt.comp (f := fun s : ℂ => ((c : ℂ) + y * I, s)) s (hpt s hs y)
      (by fun_prop)).differentiableWithinAt
  refine ⟨hUo, hcont, hhol, ?_⟩
  intro K hKU hK
  obtain ⟨M, Y, hMY⟩ := T2.norm_far hRH hm hP hK hc le_rfl (fun s hs => (hKU hs).1)
  obtain ⟨B, hB⟩ := (hK.prod (isCompact_Icc (a := -Y) (b := Y))).exists_bound_of_continuousOn
    (hcont.mono (prod_mono hKU (subset_univ _)))
  refine ⟨fun y => Set.indicator (Icc (-Y) Y) (fun _ => max B 0) y + |M| * (1 + ‖y‖) ^ (-(2 : ℝ)),
    ?_, ?_⟩
  · refine Integrable.add ?_ ?_
    · exact (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
    · exact (integrable_one_add_norm (by norm_num)).const_mul _
  · intro s hs y
    have hind0 : 0 ≤ Set.indicator (Icc (-Y) Y) (fun _ => max B 0) y :=
      Set.indicator_nonneg (fun _ _ => le_max_right _ _) _
    have hpos : 0 < 1 + |y| := by positivity
    have htail0 : 0 ≤ |M| * (1 + ‖y‖) ^ (-(2 : ℝ)) := by positivity
    by_cases hy : Y ≤ |y|
    · have h1 := hMY s hs ((c : ℂ) + y * I) (by simp) (by simp) (by simpa using hy)
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
        zero_add] at h1
      have h2 : M / (1 + |y|) ^ 2 ≤ |M| * (1 + ‖y‖) ^ (-(2 : ℝ)) := by
        rw [Real.norm_eq_abs, Real.rpow_neg hpos.le, ← div_eq_mul_inv, Real.rpow_two]
        exact div_le_div_of_nonneg_right (le_abs_self M) (by positivity)
      show ‖G s (c + y * I)‖ ≤ _
      linarith
    · have hyI : y ∈ Icc (-Y) Y := by
        rw [mem_Icc, ← abs_le]; exact (lt_of_not_ge hy).le
      have h1 := hB (s, y) ⟨hs, hyI⟩
      show ‖G s (c + y * I)‖ ≤ Set.indicator (Icc (-Y) Y) (fun _ => max B 0) y + _
      rw [Set.indicator_of_mem hyI]
      have : ‖G s (c + y * I)‖ ≤ max B 0 := h1.trans (le_max_left _ _)
      linarith

/-- The proof of `TkLine_differentiableOn`. -/
theorem T2.differentiableOn (hRH : RiemannHypothesis) {m : ℕ} (hm : 1 ≤ m) {F H : ℂ → ℂ}
    (hP : TkPack m F H) {c : ℝ} (hc : (m : ℝ) - 1 / 2 < c) (hcm : c ≠ m) :
    DifferentiableOn ℂ (TkLine F c) {s | c + 1 / 2 < s.re ∧ s.re - c ≠ 1} ∧
      ∀ s : ℂ, c + 1 / 2 < s.re → s.re - c ≠ 1 →
        Integrable (fun y : ℝ => KerS s (c + y * I) * F (c + y * I) * Qcont (s - (c + y * I))) := by
  obtain ⟨hUo, hcont, hhol, hdom⟩ := T2.line_facts hRH hm hP hc hcm
  refine ⟨M1.differentiableOn_verticalIntegral' hUo hcont hhol hdom, ?_⟩
  intro s hcs hne
  have hsU : s ∈ {s : ℂ | c + 1 / 2 < s.re ∧ s.re - c ≠ 1} := ⟨hcs, hne⟩
  obtain ⟨g, hg, hgb⟩ := hdom {s} (singleton_subset_iff.mpr hsU) isCompact_singleton
  have hcy : Continuous fun y : ℝ =>
      KerS s (c + y * I) * F (c + y * I) * Qcont (s - (c + y * I)) := by
    have := hcont.comp_continuous (f := fun y : ℝ => (s, y)) (by fun_prop) (fun y => ⟨hsU, trivial⟩)
    exact this
  exact hg.mono' hcy.aestronglyMeasurable (ae_of_all _ fun y => hgb s rfl y)

/-- The common frame of the three line moves of `TkLine`. -/
lemma T2.shift (hRH : RiemannHypothesis) {m : ℕ} (hm : 1 ≤ m) {F H : ℂ → ℂ} (hP : TkPack m F H)
    {s : ℂ} {c c' : ℝ} (hc : (m : ℝ) - 1 / 2 < c) (hcc' : c ≤ c') (hc' : c' + 1 / 2 < s.re)
    (hcm : c ≠ m) (hc'm : c' ≠ m) (hcs : s.re - c ≠ 1) (hc's : s.re - c' ≠ 1) (S : Finset ℂ)
    (Af : ℂ → ℂ) (hS : ∀ p ∈ S, c < p.re ∧ p.re < c')
    (hf : DifferentiableOn ℂ (fun w => KerS s w * F w * Qcont (s - w)) (Icc c c' ×ℂ univ \ (S : Set ℂ)))
    (hpole : ∀ p ∈ S, ((fun w => KerS s w * F w * Qcont (s - w)) - fun w => Af p / (w - p))
      =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    TkLine F c' s = ∑ p ∈ S, Af p + TkLine F c s := by
  obtain ⟨M, Y, hMY⟩ := T2.norm_far hRH hm hP isCompact_singleton hc hcc'
    (by rintro _ rfl; exact hc')
  have hb : ∀ w : ℂ, c ≤ w.re → w.re ≤ c' → Y ≤ |w.im| →
      ‖KerS s w * F w * Qcont (s - w)‖ ≤ |M| / (1 + |w.im|) ^ (3 / 2 : ℝ) := by
    intro w h1 h2 h3
    have hu1 : 1 ≤ 1 + |w.im| := by linarith [abs_nonneg w.im]
    have hle : (1 + |w.im|) ^ (3 / 2 : ℝ) ≤ (1 + |w.im|) ^ 2 := by
      rw [← Real.rpow_two]; exact Real.rpow_le_rpow_of_exponent_le hu1 (by norm_num)
    calc ‖KerS s w * F w * Qcont (s - w)‖ ≤ M / (1 + |w.im|) ^ 2 := hMY s rfl w h1 h2 h3
      _ ≤ |M| / (1 + |w.im|) ^ 2 := div_le_div_of_nonneg_right (le_abs_self M) (by positivity)
      _ ≤ |M| / (1 + |w.im|) ^ (3 / 2 : ℝ) :=
          div_le_div_of_nonneg_left (abs_nonneg M) (by positivity) hle
  have htails := M4b.tendsto_hInt_of_bound (f := fun w => KerS s w * F w * Qcont (s - w)) hcc' hb
  have hleft := (T2.differentiableOn hRH hm hP hc hcm).2 s (by linarith) hcs
  have hright := (T2.differentiableOn hRH hm hP (by linarith) hc'm).2 s hc' hc's
  exact M1.verticalIntegral'_eq_add_sum_of_simplePoles S Af hcc' hS hf hpole htails.1 htails.2
    hleft hright

end GoldbachBoundaries.Paper2.M5
