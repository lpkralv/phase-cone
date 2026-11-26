import GoldbachBoundaries.Paper2.M5.Fill.F2Common

/-!
# Fill: `filter_rect_limit` (group F2)

The rectangle `[2/5, (1 + η)/2] × [-Y', Y']` integral of `gH H s`, `s = 1 + iτ₀ + η`, minus `Fil H s - Jfil H s`, splits
into the two horizontal sides and the two differences "truncated line integral minus full line integral".

* Right side `Re z = (1 + η)/2`: `gH = gA` there (`gA_eq_gH`), integrable (`differentiableOn_FilLine`), and the full
  line integral is `Fil H s` (`Fil`'s line is `σ/2 = (1 + η)/2`).
* Left side `Re z = 2/5`: `gH` is continuous on the line and `≤ K(1 + |y|)^{-2}` (`Qleft_i`, the linear bound
  `F2_norm_Qcont_strip_le` for `Qcont(s - z)`, and the kernel decay `norm_kH_mul_pow_le`), so integrable; its full
  line integral is `Jfil H s`.
* Horizontal sides: `|gH| ≤ K(1 + Y')^{-4} · C log² Y' · B(1 + |τ₀|)(1 + Y') ≤ M/(1 + Y')`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics
open scoped Interval

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- Linear growth of `Qcont` on a closed strip inside `1/2 < Re < 1` (RH): `norm_Qcont_le_log` for `|Im| ≥ 4`,
continuity on the compact rectangle `|Im| ≤ 4`. -/
lemma F2_norm_Qcont_strip_le (hRH : RiemannHypothesis) {a b : ℝ} (ha : 1 / 2 < a) (hb : b < 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ w : ℂ, a ≤ w.re → w.re ≤ b → ‖Qcont w‖ ≤ B * (1 + |w.im|) := by
  obtain ⟨C₁, hC₁⟩ := TIdentity.norm_Qcont_le_log hRH (ε := a - 1 / 2) (by linarith)
  have hK : IsCompact (Icc a b ×ℂ Icc (-4 : ℝ) 4) := isCompact_Icc.reProdIm isCompact_Icc
  have hcont : ContinuousOn Qcont (Icc a b ×ℂ Icc (-4 : ℝ) 4) := by
    intro w hw
    have hw1 : a ≤ w.re := (mem_reProdIm.mp hw).1.1
    have hw2 : w.re ≤ b := (mem_reProdIm.mp hw).1.2
    refine (TIdentity.analyticAt_Qcont_of_RH hRH (by linarith) ?_).continuousAt.continuousWithinAt
    intro h
    rw [h, one_re] at hw2
    linarith
  obtain ⟨B₀, hB₀⟩ := hK.exists_bound_of_continuousOn hcont
  have hB0' : 0 ≤ max B₀ 0 := le_max_right _ _
  have hC0' : 0 ≤ max C₁ 0 := le_max_right _ _
  refine ⟨max B₀ 0 + max C₁ 0, by positivity, fun w hw1 hw2 => ?_⟩
  have hy0 := abs_nonneg w.im
  by_cases hy : 4 ≤ |w.im|
  · have h1 := hC₁ w (by linarith) hy
    have hlog0 : 0 ≤ Real.log |w.im| := Real.log_nonneg (by linarith)
    have hlog : Real.log |w.im| ≤ |w.im| := Real.log_le_self hy0
    calc ‖Qcont w‖ ≤ C₁ * Real.log |w.im| := h1
      _ ≤ max C₁ 0 * Real.log |w.im| := mul_le_mul_of_nonneg_right (le_max_left _ _) hlog0
      _ ≤ max C₁ 0 * (1 + |w.im|) := mul_le_mul_of_nonneg_left (by linarith) hC0'
      _ ≤ _ := by nlinarith
  · push Not at hy
    have hw : w ∈ Icc a b ×ℂ Icc (-4 : ℝ) 4 := by
      refine mem_reProdIm.mpr ⟨⟨hw1, hw2⟩, ?_⟩
      have := abs_lt.mp hy
      exact ⟨this.1.le, this.2.le⟩
    calc ‖Qcont w‖ ≤ B₀ := hB₀ w hw
      _ ≤ max B₀ 0 := le_max_left _ _
      _ ≤ _ := by nlinarith

/-- `1 + |t - y| ≤ (1 + |t|)(1 + |y|)`. -/
lemma F2_one_add_abs_sub_le (t y : ℝ) : 1 + |t - y| ≤ (1 + |t|) * (1 + |y|) := by
  have h := abs_sub t y
  have := abs_nonneg t
  have := abs_nonneg y
  nlinarith [mul_nonneg (abs_nonneg t) (abs_nonneg y)]

/-- **`gH` is integrable on the line `Re z = 2/5`** (RH, (Z1)-(Z3)), for `s = 1 + iτ₀ + η`, `0 < η ≤ 1/4`. -/
lemma F2_integrable_gH_left (hRH : RiemannHypothesis) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3)
    (H : MvPolynomial (Fin 2) ℂ) {τ₀ η : ℝ} (hη : 0 < η) (hη' : η ≤ 1 / 4) :
    Integrable (fun y : ℝ => gH H (1 + τ₀ * I + η) (((2 / 5 : ℝ) : ℂ) + y * I)) := by
  set s : ℂ := 1 + τ₀ * I + η with hs
  have hsre : s.re = 1 + η := by simp [hs]
  have hsim : s.im = τ₀ := by simp [hs]
  obtain ⟨K, hK⟩ := norm_kH_mul_pow_le H (x₁ := 2 / 5) (x₂ := 2 / 5) (σ₁ := 1 + η) (σ₂ := 1 + η)
    (τ := |τ₀|) (by norm_num) (by linarith) 4
  obtain ⟨C₀, hC₀⟩ := Qleft_i hRH hZ1 hZ2 hZ3 (2 / 5) (by norm_num) (by norm_num)
  obtain ⟨B, hB0, hB⟩ := F2_norm_Qcont_strip_le hRH (a := 3 / 5 + η) (b := 3 / 5 + η) (by linarith)
    (by linarith)
  have hzre : ∀ y : ℝ, (((2 / 5 : ℝ) : ℂ) + y * I).re = 2 / 5 := fun y => by simp
  have hzim : ∀ y : ℝ, (((2 / 5 : ℝ) : ℂ) + y * I).im = y := fun y => by simp
  have hszre : ∀ y : ℝ, (s - (((2 / 5 : ℝ) : ℂ) + y * I)).re = 3 / 5 + η := fun y => by
    simp [hsre]; ring
  have hszim : ∀ y : ℝ, (s - (((2 / 5 : ℝ) : ℂ) + y * I)).im = τ₀ - y := fun y => by
    simp [hsim]
  -- continuity
  have hcK : Continuous fun y : ℝ => kH H (((2 / 5 : ℝ) : ℂ) + y * I) s := by
    unfold kH
    refine (continuous_KerS_line (by norm_num) (by rw [hsre]; linarith)).mul ?_
    have hd := differentiable_evalH H (f := fun z => z) (g := fun z => s - z) differentiable_id
      (differentiable_const _ |>.sub differentiable_id)
    exact hd.continuous.comp (by fun_prop)
  have hcQ1 : Continuous fun y : ℝ => Qcont (((2 / 5 : ℝ) : ℂ) + y * I) := by
    rw [continuous_iff_continuousAt]
    intro y
    have hpos : (((2 / 5 : ℝ) : ℂ) + y * I) ∈ halfPlane 0 := by
      show (0 : ℝ) < (((2 / 5 : ℝ) : ℂ) + y * I).re
      rw [hzre]; norm_num
    exact (M2.isQCont_Qcont.2.2 _ ⟨hpos, (hC₀ y).1⟩).continuousAt.comp
      (f := fun y : ℝ => ((2 / 5 : ℝ) : ℂ) + y * I) (by fun_prop)
  have hcQ2 : Continuous fun y : ℝ => Qcont (s - (((2 / 5 : ℝ) : ℂ) + y * I)) := by
    rw [continuous_iff_continuousAt]
    intro y
    have h1 : 1 / 2 < (s - (((2 / 5 : ℝ) : ℂ) + y * I)).re := by rw [hszre]; linarith
    have h2 : s - (((2 / 5 : ℝ) : ℂ) + y * I) ≠ 1 := by
      intro h
      have := hszre y
      rw [h, one_re] at this
      linarith
    exact (TIdentity.analyticAt_Qcont_of_RH hRH h1 h2).continuousAt.comp
      (f := fun y : ℝ => s - (((2 / 5 : ℝ) : ℂ) + y * I)) (by fun_prop)
  have hcont : Continuous fun y : ℝ => gH H s (((2 / 5 : ℝ) : ℂ) + y * I) := by
    unfold gH
    exact (hcK.mul hcQ1).mul hcQ2
  -- the bound
  set M : ℝ := max K 0 * (2 * max C₀ 0) * (B * (1 + |τ₀|)) with hM
  refine Integrable.mono' ((integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by simp)).const_mul M)
    hcont.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  have hy0 := abs_nonneg y
  have hpos : 0 < 1 + |y| := by linarith
  have hrpow : (1 + ‖y‖) ^ (-(2 : ℝ)) = ((1 + |y|) ^ 2)⁻¹ := by
    rw [Real.norm_eq_abs, Real.rpow_neg hpos.le]
    norm_cast
  rw [hrpow]
  have hk := hK s (le_of_eq hsre.symm) (le_of_eq hsre) (by rw [hsim]) _ (le_of_eq (hzre y).symm)
    (le_of_eq (hzre y))
  rw [hzim y] at hk
  have hk' : ‖kH H (((2 / 5 : ℝ) : ℂ) + y * I) s‖ ≤ max K 0 / (1 + |y|) ^ 4 := by
    rw [le_div_iff₀ (by positivity)]
    exact hk.trans (le_max_left _ _)
  have hq1 : ‖Qcont (((2 / 5 : ℝ) : ℂ) + y * I)‖ ≤ 2 * max C₀ 0 * (1 + |y|) := by
    have h := (hC₀ y).2
    have hlog0 : 0 ≤ Real.log (|y| + 3) := Real.log_nonneg (by linarith)
    have hlog : Real.log (|y| + 3) ≤ |y| + 2 := by
      have := Real.log_le_sub_one_of_pos (show 0 < |y| + 3 by linarith)
      linarith
    calc _ ≤ C₀ * Real.log (|y| + 3) := h
      _ ≤ max C₀ 0 * Real.log (|y| + 3) := mul_le_mul_of_nonneg_right (le_max_left _ _) hlog0
      _ ≤ max C₀ 0 * (2 * (1 + |y|)) := mul_le_mul_of_nonneg_left (by linarith) (le_max_right _ _)
      _ = _ := by ring
  have hq2 : ‖Qcont (s - (((2 / 5 : ℝ) : ℂ) + y * I))‖ ≤ B * (1 + |τ₀|) * (1 + |y|) := by
    have h := hB _ (le_of_eq (hszre y).symm) (le_of_eq (hszre y))
    rw [hszim y] at h
    calc _ ≤ B * (1 + |τ₀ - y|) := h
      _ ≤ B * ((1 + |τ₀|) * (1 + |y|)) := mul_le_mul_of_nonneg_left (F2_one_add_abs_sub_le τ₀ y) hB0
      _ = _ := by ring
  have hK0 : 0 ≤ max K 0 := le_max_right _ _
  have hC0 : 0 ≤ max C₀ 0 := le_max_right _ _
  unfold gH
  rw [norm_mul, norm_mul]
  calc ‖kH H (((2 / 5 : ℝ) : ℂ) + y * I) s‖ * ‖Qcont (((2 / 5 : ℝ) : ℂ) + y * I)‖ *
        ‖Qcont (s - (((2 / 5 : ℝ) : ℂ) + y * I))‖
      ≤ max K 0 / (1 + |y|) ^ 4 * (2 * max C₀ 0 * (1 + |y|)) * (B * (1 + |τ₀|) * (1 + |y|)) := by
        gcongr
    _ = M * ((1 + |y|) ^ 2)⁻¹ := by
        rw [hM]
        field_simp

/-- **The horizontal sides** (RH): along heights with the bound of `cl:lem:Qleft`(ii), both horizontal integrals of
`gH H s` over `[2/5, (1 + η)/2]` are eventually `< ε`. -/
lemma F2_horizontal (hRH : RiemannHypothesis) (H : MvPolynomial (Fin 2) ℂ) {τ₀ η : ℝ} (hη : 0 < η)
    (hη' : η ≤ 1 / 4) (C : ℝ) :
    ∀ ε > 0, ∃ Y₀ : ℝ, ∀ Y' : ℝ, Y₀ ≤ Y' →
      (∀ x ∈ Icc (1 / 3 : ℝ) 1, ‖Qcont (x + Y' * I)‖ ≤ C * Real.log Y' ^ 2 ∧
        ‖Qcont (x - Y' * I)‖ ≤ C * Real.log Y' ^ 2) →
      ‖HIntegral (gH H (1 + τ₀ * I + η)) (2 / 5) ((1 + η) / 2) (-Y')‖ < ε ∧
        ‖HIntegral (gH H (1 + τ₀ * I + η)) (2 / 5) ((1 + η) / 2) Y'‖ < ε := by
  intro ε hε
  set s : ℂ := 1 + τ₀ * I + η with hs
  have hsre : s.re = 1 + η := by simp [hs]
  have hsim : s.im = τ₀ := by simp [hs]
  obtain ⟨K, hK⟩ := norm_kH_mul_pow_le H (x₁ := 2 / 5) (x₂ := (1 + η) / 2) (σ₁ := 1 + η) (σ₂ := 1 + η)
    (τ := |τ₀|) (by norm_num) (by linarith) 4
  obtain ⟨B, hB0, hB⟩ := F2_norm_Qcont_strip_le hRH (a := (1 + η) / 2) (b := 3 / 5 + η) (by linarith)
    (by linarith)
  have hK0 : 0 ≤ max K 0 := le_max_right _ _
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  set M : ℝ := max K 0 * max C 0 * (B * (1 + |τ₀|)) with hM
  have hM0 : 0 ≤ M := by positivity
  -- the generic estimate on a horizontal line at height `y`, `|y| = Y ≥ 1`
  have key : ∀ Y : ℝ, 1 ≤ Y → ∀ y : ℝ, |y| = Y →
      (∀ x ∈ Icc (2 / 5 : ℝ) ((1 + η) / 2), ‖Qcont (x + y * I)‖ ≤ max C 0 * (1 + Y) ^ 2) →
      ‖HIntegral (gH H s) (2 / 5) ((1 + η) / 2) y‖ ≤ M / (1 + Y) := by
    intro Y hY y hyY hQ
    have hY0 : 0 < 1 + Y := by linarith
    have hpt : ∀ x ∈ Ι (2 / 5 : ℝ) ((1 + η) / 2), ‖gH H s (x + y * I)‖ ≤ M / (1 + Y) := by
      intro x hx
      rw [uIoc_of_le (by linarith)] at hx
      have hx1 : 2 / 5 ≤ x := hx.1.le
      have hx2 : x ≤ (1 + η) / 2 := hx.2
      have hzre : ((x : ℂ) + y * I).re = x := by simp
      have hzim : ((x : ℂ) + y * I).im = y := by simp
      have hszre : (s - ((x : ℂ) + y * I)).re = 1 + η - x := by simp [hsre]
      have hszim : (s - ((x : ℂ) + y * I)).im = τ₀ - y := by simp [hsim]
      have hk := hK s (le_of_eq hsre.symm) (le_of_eq hsre) (by rw [hsim]) _ (by rw [hzre]; exact hx1)
        (by rw [hzre]; exact hx2)
      rw [hzim, hyY] at hk
      have hk' : ‖kH H ((x : ℂ) + y * I) s‖ ≤ max K 0 / (1 + Y) ^ 4 := by
        rw [le_div_iff₀ (by positivity)]
        exact hk.trans (le_max_left _ _)
      have hq1 := hQ x ⟨hx1, hx2⟩
      have hq2 : ‖Qcont (s - ((x : ℂ) + y * I))‖ ≤ B * (1 + |τ₀|) * (1 + Y) := by
        have h := hB _ (by rw [hszre]; linarith) (by rw [hszre]; linarith)
        rw [hszim] at h
        calc _ ≤ B * (1 + |τ₀ - y|) := h
          _ ≤ B * ((1 + |τ₀|) * (1 + |y|)) :=
              mul_le_mul_of_nonneg_left (F2_one_add_abs_sub_le τ₀ y) hB0
          _ = _ := by rw [hyY]; ring
      unfold gH
      rw [norm_mul, norm_mul]
      calc ‖kH H ((x : ℂ) + y * I) s‖ * ‖Qcont ((x : ℂ) + y * I)‖ * ‖Qcont (s - ((x : ℂ) + y * I))‖
          ≤ max K 0 / (1 + Y) ^ 4 * (max C 0 * (1 + Y) ^ 2) * (B * (1 + |τ₀|) * (1 + Y)) := by
            gcongr
        _ = M / (1 + Y) := by
            rw [hM]
            field_simp
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hpt
    have hlen : |(1 + η) / 2 - 2 / 5| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith
    have hMY : 0 ≤ M / (1 + Y) := div_nonneg hM0 hY0.le
    calc ‖HIntegral (gH H s) (2 / 5) ((1 + η) / 2) y‖ ≤ M / (1 + Y) * |(1 + η) / 2 - 2 / 5| := h
      _ ≤ M / (1 + Y) * 1 := mul_le_mul_of_nonneg_left hlen hMY
      _ = _ := mul_one _
  refine ⟨max 1 (M / ε), fun Y' hY' hbd => ?_⟩
  have hY1 : 1 ≤ Y' := le_trans (le_max_left _ _) hY'
  have hYM : M / ε ≤ Y' := le_trans (le_max_right _ _) hY'
  have hlt : M / (1 + Y') < ε := by
    rw [div_lt_iff₀ (by linarith)]
    rw [div_le_iff₀ hε] at hYM
    nlinarith
  have hlog0 : 0 ≤ Real.log Y' := Real.log_nonneg hY1
  have hlog : Real.log Y' ^ 2 ≤ (1 + Y') ^ 2 :=
    pow_le_pow_left₀ hlog0 (by linarith [Real.log_le_self (show (0 : ℝ) ≤ Y' by linarith)]) 2
  have hCl : C * Real.log Y' ^ 2 ≤ max C 0 * (1 + Y') ^ 2 :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)).trans
      (mul_le_mul_of_nonneg_left hlog hC0)
  have hx13 : ∀ x ∈ Icc (2 / 5 : ℝ) ((1 + η) / 2), x ∈ Icc (1 / 3 : ℝ) 1 := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  constructor
  · refine lt_of_le_of_lt (key Y' hY1 (-Y') (by rw [abs_neg]; exact abs_of_nonneg (by linarith))
      fun x hx => ?_) hlt
    have h := (hbd x (hx13 x hx)).2
    have he : ((x : ℂ) + ((-Y' : ℝ) : ℂ) * I) = (x : ℂ) - Y' * I := by push_cast; ring
    rw [he]
    exact h.trans hCl
  · refine lt_of_le_of_lt (key Y' hY1 Y' (abs_of_nonneg (by linarith)) fun x hx => ?_) hlt
    exact (hbd x (hx13 x hx)).1.trans hCl

/-- `filter_rect_limit` of `FilterII.lean`, statement verbatim. -/
theorem filter_rect_limit (hRH : RiemannHypothesis) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3)
    (H : MvPolynomial (Fin 2) ℂ)
    (hHs : ∀ z w, evalH H z w = evalH H w z) (hH1 : ∀ w, evalH H 1 w = 0) {τ₀ η : ℝ} (hη : 0 < η)
    (hη' : η ≤ 1 / 4) (C : ℝ) :
    ∀ ε > 0, ∃ Y₀ : ℝ, ∀ Y' : ℝ, Y₀ ≤ Y' →
      (∀ x ∈ Icc (1 / 3 : ℝ) 1, ‖Qcont (x + Y' * I)‖ ≤ C * Real.log Y' ^ 2 ∧
        ‖Qcont (x - Y' * I)‖ ≤ C * Real.log Y' ^ 2) →
      ‖RectangleIntegral' (gH H (1 + τ₀ * I + η)) (((2 / 5 : ℝ) : ℂ) - I * Y') ((((1 + η) / 2 : ℝ) : ℂ) + I * Y') -
          (Fil H (1 + τ₀ * I + η) - Jfil H (1 + τ₀ * I + η))‖ < ε := by
  intro ε hε
  have hε4 : 0 < ε / 4 := by positivity
  obtain ⟨Y₁, hYh⟩ := F2_horizontal hRH H (τ₀ := τ₀) hη hη' C (ε / 4) hε4
  set s : ℂ := 1 + τ₀ * I + η with hs
  have hsre : s.re = 1 + η := by simp [hs]
  -- (a) the right line
  have hintA : Integrable (fun y : ℝ => gA H s ((((1 + η) / 2 : ℝ) : ℂ) + y * I)) :=
    (differentiableOn_FilLine hRH H (c := (1 + η) / 2) (by linarith)).2 s (by rw [hsre]; linarith)
  have hA : Tendsto (fun Y : ℝ => ∫ y in -Y..Y, gH H s ((((1 + η) / 2 : ℝ) : ℂ) + y * I)) atTop
      (𝓝 (∫ y : ℝ, gA H s ((((1 + η) / 2 : ℝ) : ℂ) + y * I))) := by
    have hcongr : ∀ Y : ℝ, (∫ y in -Y..Y, gH H s ((((1 + η) / 2 : ℝ) : ℂ) + y * I)) =
        ∫ y in -Y..Y, gA H s ((((1 + η) / 2 : ℝ) : ℂ) + y * I) := by
      intro Y
      refine intervalIntegral.integral_congr fun y _ => ?_
      have hzre : ((((1 + η) / 2 : ℝ) : ℂ) + y * I).re = (1 + η) / 2 := by simp
      have hszre : (s - ((((1 + η) / 2 : ℝ) : ℂ) + y * I)).re = (1 + η) / 2 := by
        simp only [sub_re, hzre, hsre]; ring
      refine (gA_eq_gH H hHs hH1 ?_ ?_).symm
      · intro h; rw [h, one_re] at hzre; linarith
      · intro h; rw [h, one_re] at hszre; linarith
    simp_rw [hcongr]
    exact intervalIntegral_tendsto_integral hintA tendsto_neg_atTop_atBot tendsto_id
  -- (b) the left line
  have hintB := F2_integrable_gH_left hRH hZ1 hZ2 hZ3 H (τ₀ := τ₀) hη hη'
  have hB : Tendsto (fun Y : ℝ => ∫ y in -Y..Y, gH H s (((2 / 5 : ℝ) : ℂ) + y * I)) atTop
      (𝓝 (∫ y : ℝ, gH H s (((2 / 5 : ℝ) : ℂ) + y * I))) :=
    intervalIntegral_tendsto_integral hintB tendsto_neg_atTop_atBot tendsto_id
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp hA (ε / 4) hε4
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.mp hB (ε / 4) hε4
  refine ⟨max Y₁ (max N₁ N₂), fun Y' hY' hbd => ?_⟩
  have hY₁ : Y₁ ≤ Y' := le_trans (le_max_left _ _) hY'
  have hN₁' : N₁ ≤ Y' := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hY'
  have hN₂' : N₂ ≤ Y' := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hY'
  obtain ⟨hbot, htop⟩ := hYh Y' hY₁ hbd
  have ha := hN₁ Y' hN₁'
  have hb := hN₂ Y' hN₂'
  rw [dist_eq_norm] at ha hb
  -- the identity
  set Hb := HIntegral (gH H s) (2 / 5) ((1 + η) / 2) (-Y') with hHb
  set Ht := HIntegral (gH H s) (2 / 5) ((1 + η) / 2) Y' with hHt
  set A1 := ∫ y in -Y'..Y', gH H s ((((1 + η) / 2 : ℝ) : ℂ) + y * I) with hA1
  set L1 := ∫ y : ℝ, gA H s ((((1 + η) / 2 : ℝ) : ℂ) + y * I) with hL1
  set A2 := ∫ y in -Y'..Y', gH H s (((2 / 5 : ℝ) : ℂ) + y * I) with hA2
  set L2 := ∫ y : ℝ, gH H s (((2 / 5 : ℝ) : ℂ) + y * I) with hL2
  have hid : RectangleIntegral' (gH H s) (((2 / 5 : ℝ) : ℂ) - I * Y') ((((1 + η) / 2 : ℝ) : ℂ) + I * Y') -
      (Fil H s - Jfil H s) =
      (1 / (2 * Real.pi * I)) * (Hb - Ht + I * (A1 - L1) - I * (A2 - L2)) := by
    have hzre : (((2 / 5 : ℝ) : ℂ) - I * Y').re = 2 / 5 := by simp
    have hzim : (((2 / 5 : ℝ) : ℂ) - I * Y').im = -Y' := by simp
    have hwre : ((((1 + η) / 2 : ℝ) : ℂ) + I * Y').re = (1 + η) / 2 := by simp
    have hwim : ((((1 + η) / 2 : ℝ) : ℂ) + I * Y').im = Y' := by simp
    have hFil : Fil H s = VerticalIntegral' (gA H s) ((1 + η) / 2) := by
      rw [Fil, FilLine, hsre]
    rw [hFil, Jfil, RectangleIntegral', RectangleIntegral, hzre, hzim, hwre, hwim, VerticalIntegral',
      VerticalIntegral', VerticalIntegral, VerticalIntegral, VIntegral, VIntegral]
    simp only [smul_eq_mul]
    rw [hHb, hHt, hA1, hL1, hA2, hL2]
    ring
  rw [hid, norm_mul]
  have hc : ‖(1 / (2 * Real.pi * I) : ℂ)‖ ≤ 1 := by
    rw [norm_div, norm_one, norm_mul, norm_mul, norm_I, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le, mul_one, div_le_one (by positivity)]
    linarith [Real.pi_gt_three]
  have hX : ‖Hb - Ht + I * (A1 - L1) - I * (A2 - L2)‖ < ε := by
    calc ‖Hb - Ht + I * (A1 - L1) - I * (A2 - L2)‖
        ≤ ‖Hb‖ + ‖Ht‖ + ‖A1 - L1‖ + ‖A2 - L2‖ := by
          have h1 := norm_sub_le (Hb - Ht + I * (A1 - L1)) (I * (A2 - L2))
          have h2 := norm_add_le (Hb - Ht) (I * (A1 - L1))
          have h3 := norm_sub_le Hb Ht
          rw [norm_mul, norm_I, one_mul] at h1 h2
          linarith
      _ < ε / 4 + ε / 4 + ε / 4 + ε / 4 := by gcongr
      _ = ε := by ring
  calc ‖(1 / (2 * Real.pi * I) : ℂ)‖ * ‖Hb - Ht + I * (A1 - L1) - I * (A2 - L2)‖
      ≤ 1 * ‖Hb - Ht + I * (A1 - L1) - I * (A2 - L2)‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)
    _ < ε := by rw [one_mul]; exact hX

end GoldbachBoundaries.Paper2.M5
