import GoldbachBoundaries.Paper2.M6.Defs

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M6

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- A point lies off the leftward ray `α - [0, ∞)` iff `s - α` is in the slit plane. -/
lemma exG_not_mem_leftRay_iff {α s : ℂ} : (¬ ∃ t : ℝ, 0 ≤ t ∧ s = α - t) ↔ s - α ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  constructor
  · intro hs
    by_contra hc
    push Not at hc
    obtain ⟨hre, him⟩ := hc
    apply hs
    refine ⟨-(s - α).re, by simpa using hre, ?_⟩
    apply Complex.ext
    · simp
    · simp only [sub_im] at him; simp; linarith
  · rintro h ⟨t, ht, rfl⟩
    simp at h
    linarith

lemma exG_slitDiscL_eq (α : ℂ) (r : ℝ) :
    slitDiscL α r = ball α r ∩ (fun s => s - α) ⁻¹' slitPlane := by
  ext s
  simp only [slitDiscL, Set.mem_sdiff, Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]
  rw [exG_not_mem_leftRay_iff]

lemma exG_isOpen_slitDiscL (α : ℂ) (r : ℝ) : IsOpen (slitDiscL α r) := by
  rw [exG_slitDiscL_eq]
  exact isOpen_ball.inter (isOpen_slitPlane.preimage (by fun_prop))

lemma exG_sub_mem_slitPlane_of_mem_slitDiscL {α s : ℂ} {r : ℝ} (hs : s ∈ slitDiscL α r) :
    s - α ∈ slitPlane := by
  rw [exG_slitDiscL_eq] at hs; exact hs.2

/-- Off both cuts, `Log(s - α) - Log((s - α)/v)` is locally constant. -/
lemma exG_log_sub_logAt_eventually_const {κ : ℝ} {α s₂ : ℂ} (h1 : s₂ - α ∈ slitPlane)
    (h2 : (s₂ - α) / slantDir κ ∈ slitPlane) :
    ∃ c : ℂ, ∀ᶠ s in 𝓝 s₂, logAt (slantDir κ) α s = Complex.log (s - α) - c := by
  set v := slantDir κ with hvdef
  have hv : v ≠ 0 := ThmA.slantDir_ne_zero κ
  let U : Set ℂ := {s | s - α ∈ slitPlane} ∩ {s | (s - α) / v ∈ slitPlane}
  have hU : IsOpen U :=
    (isOpen_slitPlane.preimage (by fun_prop)).inter (isOpen_slitPlane.preimage (by fun_prop))
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hU s₂ ⟨h1, h2⟩
  let D : ℂ → ℂ := fun s => Complex.log (s - α) - Complex.log ((s - α) / v)
  have hD : ∀ s ∈ U, HasDerivAt D 0 s := by
    intro s hs
    have hsα : s - α ≠ 0 := slitPlane_ne_zero hs.1
    have e1 := ((hasDerivAt_id' s).sub_const α).clog hs.1
    have e2 := (((hasDerivAt_id' s).sub_const α).div_const v).clog hs.2
    convert e1.sub e2 using 1
    field_simp
    ring
  refine ⟨D s₂, ?_⟩
  filter_upwards [ball_mem_nhds s₂ hδ] with s hs
  have := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball s₂ δ).isPreconnected
    (fun z hz => (hD z (hball hz)).differentiableAt.differentiableWithinAt)
    (fun z hz => (hD z (hball hz)).deriv) hs (mem_ball_self hδ)
  simp only [logAt, D] at this ⊢
  rw [← this]; ring

/-- **Moving the slit from paper 1's slanted cut to the leftward radius.** Off the slanted cut the two logarithms
differ by a local constant, absorbed into `H` as a multiple of `X₀`; at a point of the slanted cut, pass to a nearby
point off it inside a ball where `g` is analytic and admissible, and carry the formula back by the identity theorem. -/
theorem local_form_slitDiscL_of_slitDisc {κ : ℝ} {α : ℂ} {r : ℝ} (hr : 0 < r) (hrα : r ≤ α.re - 1)
    {X₀ : ℂ → ℂ} (hX : DifferentiableOn ℂ X₀ (ball α r)) {Adm : ℂ → (ℂ → ℂ) → Prop}
    (hAan : ∀ s g, Adm s g → AnalyticAt ℂ g s) (hAnear : ∀ s g, Adm s g → ∀ᶠ s' in 𝓝 s, Adm s' g)
    (hloc : ∀ s₁ ∈ slitDisc (slantDir κ) α r, ∀ g : ℂ → ℂ, Adm s₁ g →
      ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (ball α r) ∧
        g =ᶠ[𝓝 s₁] fun s => X₀ s * logAt (slantDir κ) α s + h s) :
    ∀ s₁ ∈ slitDiscL α r, ∀ g : ℂ → ℂ, Adm s₁ g →
      ∃ H : ℂ → ℂ, DifferentiableOn ℂ H (ball α r) ∧
        g =ᶠ[𝓝 s₁] fun s => X₀ s * Complex.log (s - α) + H s := by
  intro s₁ hs₁ g hg
  set v := slantDir κ with hvdef
  have hv : v ≠ 0 := ThmA.slantDir_ne_zero κ
  -- Off the slanted cut: the two logarithms differ by a local constant.
  have key : ∀ s₂ ∈ slitDiscL α r, s₂ ∉ cut v α → Adm s₂ g → ∃ H : ℂ → ℂ,
      DifferentiableOn ℂ H (ball α r) ∧ g =ᶠ[𝓝 s₂] fun s => X₀ s * Complex.log (s - α) + H s := by
    intro s₂ hs₂ hcut hA
    obtain ⟨h, hh, hgh⟩ := hloc s₂ ⟨hs₂.1, hcut⟩ g hA
    have h2 : (s₂ - α) / v ∈ slitPlane := ((ThmA.slitDisc_facts κ hr hrα).2.2 s₂ hs₂.1).1 hcut
    obtain ⟨c, hc⟩ := exG_log_sub_logAt_eventually_const (exG_sub_mem_slitPlane_of_mem_slitDiscL hs₂) h2
    refine ⟨fun s => h s - c * X₀ s, hh.sub (hX.const_mul c), ?_⟩
    filter_upwards [hgh, hc] with s e1 e2
    rw [e1, e2]; ring
  -- A ball around `s₁` inside the slit disc on which `g` is analytic and admissible.
  obtain ⟨ε, hε, hB⟩ := Metric.eventually_nhds_iff_ball.1
    (((hAan _ _ hg).eventually_analyticAt.and (hAnear _ _ hg)).and
      ((exG_isOpen_slitDiscL α r).mem_nhds hs₁))
  -- A point of that ball off the slanted cut.
  obtain ⟨s₂, hs₂B, hs₂cut⟩ : ∃ s₂ ∈ ball s₁ ε, s₂ ∉ cut v α := by
    by_cases hc : s₁ ∈ cut v α
    · have hvn : 0 < ‖v‖ := norm_pos_iff.2 hv
      set η : ℝ := ε / 2 / ‖v‖ with hη
      have hηpos : 0 < η := by positivity
      refine ⟨s₁ + (η : ℂ) * I * v, ?_, ?_⟩
      · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, norm_mul, Complex.norm_I,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos hηpos, hη]
        field_simp
        linarith
      · rintro ⟨t, -, -, ht⟩
        obtain ⟨t₀, -, -, ht₀⟩ := hc
        rw [ht₀] at ht
        have h0 : (((t - t₀ : ℝ) : ℂ) + (η : ℂ) * I) * v = 0 := by
          push_cast; linear_combination ht
        rcases mul_eq_zero.1 h0 with h | h
        · have := congrArg Complex.im h
          simp at this
          linarith
        · exact hv h
    · exact ⟨s₁, mem_ball_self hε, hc⟩
  obtain ⟨H, hH, hgH⟩ := key s₂ (hB s₂ hs₂B).2 hs₂cut (hB s₂ hs₂B).1.2
  refine ⟨H, hH, ?_⟩
  have hBsub : ball s₁ ε ⊆ slitDiscL α r := fun z hz => (hB z hz).2
  have hBball : ball s₁ ε ⊆ ball α r := fun z hz => (hBsub hz).1
  have hgA : AnalyticOnNhd ℂ g (ball s₁ ε) := fun z hz => (hB z hz).1.1
  have hX' : AnalyticOnNhd ℂ X₀ (ball α r) := hX.analyticOnNhd isOpen_ball
  have hH' : AnalyticOnNhd ℂ H (ball α r) := hH.analyticOnNhd isOpen_ball
  have hRA : AnalyticOnNhd ℂ (fun s => X₀ s * Complex.log (s - α) + H s) (ball s₁ ε) := by
    intro z hz
    have hlog : AnalyticAt ℂ (fun s => Complex.log (s - α)) z :=
      (analyticAt_id.sub analyticAt_const).clog (exG_sub_mem_slitPlane_of_mem_slitDiscL (hBsub hz))
    exact ((hX' z (hBball hz)).mul hlog).add (hH' z (hBball hz))
  have heq := hgA.eqOn_of_preconnected_of_eventuallyEq hRA (convex_ball s₁ ε).isPreconnected hs₂B hgH
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hε)] with z hz
  exact heq hz

end GoldbachBoundaries.Paper2.M6
