import GoldbachBoundaries.Paper2.M5.Fill.F3Common

/-!
# Fill, group F3: `differentiableOn_Jfil`

M1's `differentiableOn_verticalIntegral'` on `U = {9/10 < σ < 7/5}`, line `c = 2/5`. With `z = 2/5 + iy`:
`Qcont(z)` is analytic (`2/5 + iy ∉ Σ_Q`, `lem_Qleft_proof`(i)) and `≤ C log(|y| + 3)`; `Re(s - z) = σ - 2/5 ∈ (1/2, 1)`, so
`Qcont(s - z)` is analytic (paper 1's `analyticAt_Qcont_of_RH`) and, on a compact `K ⊆ U`, `≪ 1 + |y|` (paper 1's
`norm_Qcont_le_log` for `|Im(s - z)| ≥ 4`, continuity on a compact rectangle below); `|H(z, s - z)| ≪ (1 + |y|)^d`; and
`|K_s(z)| ≪ (1 + |y|)^{-(d+4)}` (M1's `norm_KerS_mul_pow_le`). So the integrand is `≪ (1 + y²)⁻¹` on `K`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- Arithmetic of the majorant: `k t^{d+4} ≤ C_k`, `p ≤ P' t^d`, `q₁ ≤ A₁ t`, `q₂ ≤ A₂ t` give
`k p q₁ q₂ ≤ C_k P' A₁ A₂ / t²` for `t ≥ 1`. -/
lemma F3_prod_bound {k p q1 q2 t Ck P' A1 A2 : ℝ} (d : ℕ) (hp : 0 ≤ p) (hq1 : 0 ≤ q1)
    (hq2 : 0 ≤ q2) (ht1 : 1 ≤ t) (hCk : 0 ≤ Ck) (hP' : 0 ≤ P') (hA1 : 0 ≤ A1)
    (hkb : k * t ^ (d + 4) ≤ Ck) (hpb : p ≤ P' * t ^ d) (hq1b : q1 ≤ A1 * t) (hq2b : q2 ≤ A2 * t) :
    k * p * q1 * q2 ≤ Ck * P' * A1 * A2 / t ^ 2 := by
  have ht0 : 0 < t := by linarith
  have hmain : k * p * q1 * q2 * t ^ (d + 4) ≤ Ck * P' * A1 * A2 * t ^ (d + 2) := by
    have e1 : k * p * q1 * q2 * t ^ (d + 4) = (k * t ^ (d + 4)) * p * q1 * q2 := by ring
    have e2 : Ck * P' * A1 * A2 * t ^ (d + 2) = Ck * (P' * t ^ d) * (A1 * t) * (A2 * t) := by ring
    rw [e1, e2]
    have hPt : 0 ≤ P' * t ^ d := by positivity
    have hA1t : 0 ≤ A1 * t := by positivity
    exact mul_le_mul (mul_le_mul (mul_le_mul hkb hpb hp hCk) hq1b hq1 (mul_nonneg hCk hPt)) hq2b hq2
      (mul_nonneg (mul_nonneg hCk hPt) hA1t)
  rw [le_div_iff₀ (by positivity)]
  have htd : 0 < t ^ (d + 2) := by positivity
  have : k * p * q1 * q2 * t ^ 2 * t ^ (d + 2) ≤ Ck * P' * A1 * A2 * t ^ (d + 2) := by
    calc k * p * q1 * q2 * t ^ 2 * t ^ (d + 2) = k * p * q1 * q2 * t ^ (d + 4) := by ring
      _ ≤ _ := hmain
  exact le_of_mul_le_mul_right this htd

lemma F3_sq_le (y : ℝ) : 1 + y ^ 2 ≤ (1 + |y|) ^ 2 := by
  nlinarith [abs_nonneg y, sq_abs y]

/-- The majorant of `gH` on the line `Re z = 2/5`, uniformly on compacts of the strip. -/
lemma F3_Jfil_dom (hRH : RiemannHypothesis) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (H : MvPolynomial (Fin 2) ℂ) :
    ∀ K ⊆ {s : ℂ | 9 / 10 < s.re ∧ s.re < 7 / 5}, IsCompact K → ∃ g : ℝ → ℝ, Integrable g ∧
      ∀ s ∈ K, ∀ y : ℝ, ‖gH H s (((2 / 5 : ℝ) : ℂ) + y * I)‖ ≤ g y := by
  obtain ⟨CQ, hCQ⟩ := (lem_Qleft_proof hRH hZ1 hZ2 hZ3).1 (2 / 5) (by norm_num) (by norm_num)
  have hQline : ∀ y : ℝ, (((2 / 5 : ℝ) : ℂ) + y * I : ℂ) ∉ PoleSetQ ∧
      ‖Qcont (((2 / 5 : ℝ) : ℂ) + y * I)‖ ≤ CQ * Real.log (|y| + 3) :=
    hCQ Qcont M2.isQCont_Qcont
  have hzre : ∀ y : ℝ, (((2 / 5 : ℝ) : ℂ) + y * I).re = 2 / 5 := by intro y; simp
  have hzim : ∀ y : ℝ, (((2 / 5 : ℝ) : ℂ) + y * I).im = y := by intro y; simp
  have hszre : ∀ s : ℂ, ∀ y : ℝ, (s - (((2 / 5 : ℝ) : ℂ) + y * I)).re = s.re - 2 / 5 := by
    intro s y; simp
  have hQz : ∀ y : ℝ, AnalyticAt ℂ Qcont (((2 / 5 : ℝ) : ℂ) + y * I) := fun y =>
    M2.isQCont_Qcont.2.2 _ ⟨by show (0 : ℝ) < _; rw [hzre]; norm_num, (hQline y).1⟩
  have hQw : ∀ w : ℂ, 1 / 2 < w.re → w.re < 1 → AnalyticAt ℂ Qcont w := by
    intro w h1 h2
    refine TIdentity.analyticAt_Qcont_of_RH hRH h1 fun h => ?_
    rw [h] at h2; norm_num at h2
  intro K hKU hK
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · exact ⟨fun _ => 0, integrable_zero _ _ _, fun s hs => by rw [hKe] at hs; exact absurd hs (notMem_empty s)⟩
  obtain ⟨s₁, hs₁K, hs₁⟩ := hK.exists_isMinOn hKne Complex.continuous_re.continuousOn
  obtain ⟨s₂, hs₂K, hs₂⟩ := hK.exists_isMaxOn hKne Complex.continuous_re.continuousOn
  obtain ⟨B₀, hB₀⟩ := hK.isBounded.exists_norm_le
  set B : ℝ := max B₀ 0 with hB
  have hB0 : 0 ≤ B := le_max_right _ _
  have hBK : ∀ s ∈ K, ‖s‖ ≤ B := fun s hs => (hB₀ s hs).trans (le_max_left _ _)
  set a : ℝ := s₁.re with ha
  set b : ℝ := s₂.re with hb
  have ha9 : 9 / 10 < a := (hKU hs₁K).1
  have hb7 : b < 7 / 5 := (hKU hs₂K).2
  have hKa : ∀ s ∈ K, a ≤ s.re := fun s hs => hs₁ hs
  have hKb : ∀ s ∈ K, s.re ≤ b := fun s hs => hs₂ hs
  -- polynomial
  obtain ⟨Cp, d, hCp, hP⟩ := F3_norm_evalH_le H
  -- kernel
  obtain ⟨Ck, hCk⟩ := norm_KerS_mul_pow_le (x₁ := 2 / 5) (x₂ := 2 / 5) (σ₁ := a) (σ₂ := b) (τ₀ := B)
    (by norm_num) (by linarith) (d + 4)
  -- `Qcont(s - z)` for large imaginary part
  obtain ⟨CL, hCL⟩ := TIdentity.norm_Qcont_le_log hRH (ε := a - 9 / 10) (by linarith)
  -- and on a compact rectangle
  have hRc : IsCompact (Icc (a - 2 / 5) (b - 2 / 5) ×ℂ Icc (-4 : ℝ) 4) :=
    isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨MR, hMR⟩ := hRc.exists_bound_of_continuousOn (f := Qcont) (fun w hw => by
    have h1 : a - 2 / 5 ≤ w.re := hw.1.1
    have h2 : w.re ≤ b - 2 / 5 := hw.1.2
    exact (hQw w (by linarith) (by linarith)).continuousAt.continuousWithinAt)
  set Ck' : ℝ := max Ck 0 with hCk'
  set P' : ℝ := Cp * (3 + B) ^ d with hP'
  set A1 : ℝ := 3 * |CQ| with hA1
  set A2 : ℝ := |MR| + |CL| * (B + 1) with hA2
  set M : ℝ := Ck' * P' * A1 * A2 with hM
  have hP'0 : 0 ≤ P' := by positivity
  have hA10 : 0 ≤ A1 := by positivity
  have hA20 : 0 ≤ A2 := by positivity
  have hCk'0 : 0 ≤ Ck' := le_max_right _ _
  have hM0 : 0 ≤ M := by positivity
  refine ⟨fun y => M * (1 + y ^ 2)⁻¹, integrable_inv_one_add_sq.const_mul M, fun s hs y => ?_⟩
  set z : ℂ := ((2 / 5 : ℝ) : ℂ) + y * I with hz
  set t : ℝ := 1 + |y| with ht
  have ht1 : 1 ≤ t := by rw [ht]; linarith [abs_nonneg y]
  have ht0 : 0 < t := by linarith
  have hsU := hKU hs
  have hsre1 := hKa s hs
  have hsre2 := hKb s hs
  have hsB := hBK s hs
  have hsim : |s.im| ≤ B := (Complex.abs_im_le_norm s).trans hsB
  -- kernel bound
  have hKb' : ‖KerS s z‖ * t ^ (d + 4) ≤ Ck' := by
    have := hCk s hsre1 hsre2 hsim z (by rw [hz, hzre]) (by rw [hz, hzre])
    rw [hz, hzim] at this
    exact this.trans (le_max_left _ _)
  -- polynomial bound
  have hznorm : ‖z‖ ≤ 2 / 5 + |y| := by
    calc ‖z‖ ≤ ‖((2 / 5 : ℝ) : ℂ)‖ + ‖(y : ℂ) * I‖ := norm_add_le _ _
      _ = 2 / 5 + |y| := by
        rw [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Complex.norm_real]
        norm_num
  have hPb : ‖evalH H z (s - z)‖ ≤ P' * t ^ d := by
    have h1 := hP z (s - z)
    have h2 : ‖s - z‖ ≤ B + (2 / 5 + |y|) := (norm_sub_le _ _).trans (add_le_add hsB hznorm)
    have h3 : 1 + ‖z‖ + ‖s - z‖ ≤ (3 + B) * t := by
      rw [ht]; nlinarith [abs_nonneg y]
    have h4 : (1 + ‖z‖ + ‖s - z‖) ^ d ≤ ((3 + B) * t) ^ d :=
      pow_le_pow_left₀ (by positivity) h3 d
    calc ‖evalH H z (s - z)‖ ≤ Cp * (1 + ‖z‖ + ‖s - z‖) ^ d := h1
      _ ≤ Cp * ((3 + B) * t) ^ d := mul_le_mul_of_nonneg_left h4 hCp
      _ = P' * t ^ d := by rw [hP', mul_pow]; ring
  -- `Qcont(z)`
  have hQ1 : ‖Qcont z‖ ≤ A1 * t := by
    have h1 := (hQline y).2
    have hlog0 : 0 ≤ Real.log (|y| + 3) := Real.log_nonneg (by linarith [abs_nonneg y])
    have hlog : Real.log (|y| + 3) ≤ |y| + 3 := Real.log_le_self (by positivity)
    calc ‖Qcont z‖ ≤ CQ * Real.log (|y| + 3) := h1
      _ ≤ |CQ| * Real.log (|y| + 3) := mul_le_mul_of_nonneg_right (le_abs_self _) hlog0
      _ ≤ |CQ| * (|y| + 3) := mul_le_mul_of_nonneg_left hlog (abs_nonneg _)
      _ ≤ A1 * t := by rw [hA1, ht]; nlinarith [abs_nonneg CQ, abs_nonneg y]
  -- `Qcont(s - z)`
  have hQ2 : ‖Qcont (s - z)‖ ≤ A2 * t := by
    have hwre : (s - z).re = s.re - 2 / 5 := by rw [hz, hszre]
    have hwim : (s - z).im = s.im - y := by rw [hz]; simp
    have hwimle : |(s - z).im| ≤ B + |y| := by
      rw [hwim]
      calc |s.im - y| ≤ |s.im| + |y| := abs_sub _ _
        _ ≤ B + |y| := by linarith
    have hByt : B + |y| ≤ (B + 1) * t := by rw [ht]; nlinarith [mul_nonneg hB0 (abs_nonneg y)]
    by_cases h4 : 4 ≤ |(s - z).im|
    · have h1 := hCL (s - z) (by rw [hwre]; linarith) h4
      have hlog0 : 0 ≤ Real.log |(s - z).im| := Real.log_nonneg (by linarith)
      have hlog : Real.log |(s - z).im| ≤ |(s - z).im| := Real.log_le_self (abs_nonneg _)
      calc ‖Qcont (s - z)‖ ≤ CL * Real.log |(s - z).im| := h1
        _ ≤ |CL| * Real.log |(s - z).im| := mul_le_mul_of_nonneg_right (le_abs_self _) hlog0
        _ ≤ |CL| * (B + |y|) := mul_le_mul_of_nonneg_left (hlog.trans hwimle) (abs_nonneg _)
        _ ≤ |CL| * ((B + 1) * t) := mul_le_mul_of_nonneg_left hByt (abs_nonneg _)
        _ = (|CL| * (B + 1)) * t := by ring
        _ ≤ A2 * t := mul_le_mul_of_nonneg_right (by rw [hA2]; linarith [abs_nonneg MR]) ht0.le
    · have hmem : s - z ∈ Icc (a - 2 / 5) (b - 2 / 5) ×ℂ Icc (-4 : ℝ) 4 := by
        refine ⟨⟨by rw [hwre]; linarith, by rw [hwre]; linarith⟩, ?_⟩
        have : |(s - z).im| ≤ 4 := (not_le.mp h4).le
        exact ⟨(abs_le.mp this).1, (abs_le.mp this).2⟩
      calc ‖Qcont (s - z)‖ ≤ MR := hMR _ hmem
        _ ≤ |MR| := le_abs_self _
        _ ≤ A2 := by rw [hA2]; linarith [mul_nonneg (abs_nonneg CL) (by linarith : (0 : ℝ) ≤ B + 1)]
        _ ≤ A2 * t := le_mul_of_one_le_right hA20 ht1
  have hnorm : ‖gH H s z‖ = ‖KerS s z‖ * ‖evalH H z (s - z)‖ * ‖Qcont z‖ * ‖Qcont (s - z)‖ := by
    rw [show gH H s z = KerS s z * evalH H z (s - z) * Qcont z * Qcont (s - z) from rfl, norm_mul, norm_mul,
      norm_mul]
  rw [hnorm]
  calc _ ≤ Ck' * P' * A1 * A2 / t ^ 2 := F3_prod_bound d (norm_nonneg _) (norm_nonneg _)
        (norm_nonneg _) ht1 hCk'0 hP'0 hA10 hKb' hPb hQ1 hQ2
    _ ≤ M / (1 + y ^ 2) := div_le_div_of_nonneg_left hM0 (by positivity) (F3_sq_le y)
    _ = M * (1 + y ^ 2)⁻¹ := div_eq_mul_inv _ _

theorem differentiableOn_Jfil (hRH : RiemannHypothesis) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3)
    (H : MvPolynomial (Fin 2) ℂ) : DifferentiableOn ℂ (Jfil H) {s | 9 / 10 < s.re ∧ s.re < 7 / 5} := by
  set U : Set ℂ := {s | 9 / 10 < s.re ∧ s.re < 7 / 5} with hUdef
  have hU : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt Complex.continuous_re continuous_const)
  obtain ⟨CQ, hCQ⟩ := (lem_Qleft_proof hRH hZ1 hZ2 hZ3).1 (2 / 5) (by norm_num) (by norm_num)
  have hQline : ∀ y : ℝ, (((2 / 5 : ℝ) : ℂ) + y * I : ℂ) ∉ PoleSetQ ∧
      ‖Qcont (((2 / 5 : ℝ) : ℂ) + y * I)‖ ≤ CQ * Real.log (|y| + 3) :=
    hCQ Qcont M2.isQCont_Qcont
  have hzre : ∀ y : ℝ, (((2 / 5 : ℝ) : ℂ) + y * I).re = 2 / 5 := by intro y; simp
  have hzim : ∀ y : ℝ, (((2 / 5 : ℝ) : ℂ) + y * I).im = y := by intro y; simp
  have hszre : ∀ s : ℂ, ∀ y : ℝ, (s - (((2 / 5 : ℝ) : ℂ) + y * I)).re = s.re - 2 / 5 := by
    intro s y; simp
  have hQz : ∀ y : ℝ, AnalyticAt ℂ Qcont (((2 / 5 : ℝ) : ℂ) + y * I) := fun y =>
    M2.isQCont_Qcont.2.2 _ ⟨by show (0 : ℝ) < _; rw [hzre]; norm_num, (hQline y).1⟩
  have hQw : ∀ w : ℂ, 1 / 2 < w.re → w.re < 1 → AnalyticAt ℂ Qcont w := by
    intro w h1 h2
    refine TIdentity.analyticAt_Qcont_of_RH hRH h1 fun h => ?_
    rw [h] at h2; norm_num at h2
  have hQsz : ∀ s ∈ U, ∀ y : ℝ, AnalyticAt ℂ Qcont (s - (((2 / 5 : ℝ) : ℂ) + y * I)) := by
    intro s hs y
    have hs' : 9 / 10 < s.re ∧ s.re < 7 / 5 := hs
    exact hQw _ (by rw [hszre]; linarith) (by rw [hszre]; linarith)
  have hsre : ∀ s ∈ U, 0 < s.re := fun s hs => by
    have hs' : 9 / 10 < s.re ∧ s.re < 7 / 5 := hs
    linarith
  have hszpos : ∀ s ∈ U, ∀ y : ℝ, 0 < (s - (((2 / 5 : ℝ) : ℂ) + y * I)).re := fun s hs y => by
    have hs' : 9 / 10 < s.re ∧ s.re < 7 / 5 := hs
    rw [hszre]; linarith
  refine differentiableOn_verticalIntegral' (F := gH H) (c := 2 / 5) hU ?_ ?_ ?_
  · -- joint continuity on `U × ℝ`
    intro p hp
    apply ContinuousAt.continuousWithinAt
    have hs : p.1 ∈ U := hp.1
    have hzf : Continuous (fun q : ℂ × ℝ => ((2 / 5 : ℝ) : ℂ) + (q.2 : ℂ) * I) :=
      continuous_const.add ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)
    have hszf : Continuous (fun q : ℂ × ℝ => q.1 - (((2 / 5 : ℝ) : ℂ) + (q.2 : ℂ) * I)) :=
      continuous_fst.sub hzf
    have h1 : ContinuousAt (fun q : ℂ × ℝ => Gamma (((2 / 5 : ℝ) : ℂ) + (q.2 : ℂ) * I)) p :=
      ContinuousAt.comp (g := Gamma)
        (F3_differentiableAt_Gamma (by rw [hzre]; norm_num)).continuousAt hzf.continuousAt
    have h2 : ContinuousAt (fun q : ℂ × ℝ => Gamma (q.1 - (((2 / 5 : ℝ) : ℂ) + (q.2 : ℂ) * I))) p :=
      ContinuousAt.comp (g := Gamma) (F3_differentiableAt_Gamma (hszpos p.1 hs p.2)).continuousAt
        hszf.continuousAt
    have h3 : ContinuousAt (fun q : ℂ × ℝ => Gamma q.1) p :=
      ContinuousAt.comp (g := Gamma) (F3_differentiableAt_Gamma (hsre p.1 hs)).continuousAt
        continuous_fst.continuousAt
    have h4 : ContinuousAt (fun q : ℂ × ℝ => evalH H (((2 / 5 : ℝ) : ℂ) + (q.2 : ℂ) * I)
        (q.1 - (((2 / 5 : ℝ) : ℂ) + (q.2 : ℂ) * I))) p :=
      (F3_continuous_evalH H hzf hszf).continuousAt
    have h5 : ContinuousAt (fun q : ℂ × ℝ => Qcont (((2 / 5 : ℝ) : ℂ) + (q.2 : ℂ) * I)) p :=
      ContinuousAt.comp (g := Qcont) (hQz p.2).continuousAt hzf.continuousAt
    have h6 : ContinuousAt (fun q : ℂ × ℝ => Qcont (q.1 - (((2 / 5 : ℝ) : ℂ) + (q.2 : ℂ) * I))) p :=
      ContinuousAt.comp (g := Qcont) (hQsz p.1 hs p.2).continuousAt hszf.continuousAt
    exact ((((h1.mul h2).div h3 (Complex.Gamma_ne_zero_of_re_pos (hsre p.1 hs))).mul h4).mul h5).mul h6
  · -- holomorphy in `s`
    intro y s hs
    have hK := F3_differentiableAt_KerS (w := ((2 / 5 : ℝ) : ℂ) + y * I) (hsre s hs) (hszpos s hs y)
    have hP : DifferentiableAt ℂ (fun t : ℂ => evalH H (((2 / 5 : ℝ) : ℂ) + y * I)
        (t - (((2 / 5 : ℝ) : ℂ) + y * I))) s :=
      (F3_differentiable_evalH H (differentiable_const _) (differentiable_id.sub_const _)) s
    have hQ2 : DifferentiableAt ℂ (fun t : ℂ => Qcont (t - (((2 / 5 : ℝ) : ℂ) + y * I))) s :=
      (hQsz s hs y).differentiableAt.comp s (differentiableAt_id.sub_const _)
    exact (((hK.mul hP).mul (differentiableAt_const _)).mul hQ2).differentiableWithinAt
  · exact F3_Jfil_dom hRH hZ1 hZ2 hZ3 H

end GoldbachBoundaries.Paper2.M5
