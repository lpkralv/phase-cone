import GoldbachBoundaries.Paper2.M5.FilterII

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics
namespace GoldbachBoundaries.Paper2.M5
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

theorem noMeromorphicExtensionAt_of_line_blowup {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F HH) {τ : ℝ}
    (h : ∀ ε > 0, ∃ τ₀ : ℝ, τ₀ ≠ τ ∧ |τ₀ - τ| < ε ∧ ∃ c : ℂ, c ≠ 0 ∧
      Tendsto (fun η : ℝ => (η : ℂ) * F (1 + τ₀ * I + η)) (𝓝[>] 0) (𝓝 c)) :
    NoMeromorphicExtensionAt F HH (1 + τ * I) := by
  rintro r hr ⟨f, hf, hfF⟩
  set s₁ : ℂ := 1 + τ * I with hs₁
  obtain ⟨δ, hδ, hδan⟩ : ∃ δ > 0, ∀ z ∈ ball s₁ δ, z ≠ s₁ → AnalyticAt ℂ f z := by
    have hev := (hf s₁ (mem_ball_self hr)).eventually_analyticAt
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff_ball] at hev
    obtain ⟨δ, hδ, hev⟩ := hev
    exact ⟨δ, hδ, fun z hz hne => hev z hz hne⟩
  obtain ⟨τ₀, hne, hlt, c, hc, hlim⟩ := h (min δ (r / 2)) (lt_min hδ (by linarith))
  set s₀ : ℂ := 1 + τ₀ * I with hs₀
  have hdist : dist s₀ s₁ = |τ₀ - τ| := by
    rw [dist_eq_norm]
    have heq : s₀ - s₁ = ((τ₀ - τ : ℝ) : ℂ) * I := by
      rw [hs₀, hs₁]; push_cast; ring
    rw [heq, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
  have hnot : s₀ ≠ s₁ := by
    intro heq
    apply hne
    have him := congrArg Complex.im heq
    simpa [hs₀, hs₁] using him
  have hsub : ball s₀ (r / 2) ⊆ ball s₁ r := by
    intro z hz
    rw [mem_ball] at hz ⊢
    calc dist z s₁ ≤ dist z s₀ + dist s₀ s₁ := dist_triangle _ _ _
      _ < r / 2 + r / 2 := add_lt_add hz (by rw [hdist]; exact hlt.trans_le (min_le_right _ _))
      _ = r := by ring
  have hpole := order_residue_of_codiscrete_line hF (s₀ := s₀)
    (by simp [hs₀]) (by linarith : 0 < r / 2) (hf.mono_set hsub)
    (hfF.filter_mono (Filter.codiscreteWithin_mono (inter_subset_inter_left HH hsub))) hc hlim
  have han := hδan s₀ (by rw [mem_ball, hdist]; exact hlt.trans_le (min_le_left _ _)) hnot
  have hnonneg := han.meromorphicOrderAt_nonneg
  rw [hpole.1] at hnonneg
  have hneg : (-1 : WithTop ℤ) < 0 := by decide
  exact (not_le_of_gt hneg) hnonneg

end GoldbachBoundaries.Paper2.M5
