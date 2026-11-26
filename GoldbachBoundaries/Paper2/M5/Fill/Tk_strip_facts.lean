import GoldbachBoundaries.Paper2.M5.TkStep

/-! Filler for `Tk_strip_facts` (M5, group T1). On the strip `k - 1 < σ < k`, field 4 of the package writes `F` as
`H + g · Qcont(L(·) - 1)` off the locally finite set `Σ_Q + (k - 1)`, with `L(s) = s - k + 2` and
`g(s) = kΓ(s - k + 1)/Γ(s)` analytic and non-zero; M4b's `FillC2.add_mul_Qcont_app_facts` (the argument of M4b's
`Fmero_strip_facts`) gives the residues, and `R_b ≠ 0` under RH (M4a's `cP_ne_zero_of_RH`). -/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

namespace FillT1

lemma analyticAt_Gamma_T1 {z : ℂ} (hz : 0 < z.re) : AnalyticAt ℂ Gamma z := by
  have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const continuous_re
  refine DifferentiableOn.analyticAt (s := {w : ℂ | 0 < w.re}) (fun w hw => ?_) (hopen.mem_nhds hz)
  refine (Complex.differentiableAt_Gamma w fun m h => ?_).differentiableWithinAt
  have h1 : w.re = -(m : ℝ) := by rw [h]; simp
  have h2 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have h3 : 0 < w.re := hw
  linarith

/-- Off a punctured neighbourhood of `s₀`, `s - k + 1 ∉ Σ_Q` (`Σ_Q` is locally finite in `Re > 0`). -/
lemma eventually_nhdsNE_notMem_poleSetQ_T1 (k : ℕ) {s₀ : ℂ} (hs : 0 < (s₀ - (k : ℂ) + 1).re) :
    ∀ᶠ s : ℂ in 𝓝[≠] s₀, s - (k : ℂ) + 1 ∉ PoleSetQ := by
  obtain ⟨U, hU, hfin⟩ := poleSetQ_locallyFinite (s₀ - k + 1) hs
  set φ : ℂ → ℂ := fun s => s - (k : ℂ) + 1 with hφdef
  have hφ : Continuous φ := by fun_prop
  have hV : φ ⁻¹' U ∈ 𝓝 s₀ := hφ.continuousAt.preimage_mem_nhds hU
  have hinj : Function.Injective φ := fun a b h => by
    simp only [hφdef] at h
    linear_combination h
  have hfin' : (φ ⁻¹' (U ∩ PoleSetQ)).Finite := hfin.preimage hinj.injOn
  have hcl : IsClosed (φ ⁻¹' (U ∩ PoleSetQ) \ {s₀}) := (hfin'.sdiff).isClosed
  have hop : (φ ⁻¹' (U ∩ PoleSetQ) \ {s₀})ᶜ ∈ 𝓝 s₀ := hcl.isOpen_compl.mem_nhds (by simp)
  filter_upwards [nhdsWithin_le_nhds (inter_mem hV hop), self_mem_nhdsWithin] with s hs hne
  intro hP
  exact hs.2 ⟨⟨hs.1, hP⟩, hne⟩

end FillT1

open FillT1 in
theorem Tk_strip_facts (hRH : RiemannHypothesis) {k : ℕ} (hk : 2 ≤ k) {F H : ℂ → ℂ} (hP : TkPack k F H) :
    (∀ s : ℂ, (k : ℝ) - 1 < s.re → s.re < k →
      (meromorphicOrderAt F s < 0 ↔ s - (k - 1) ∈ PoleSetQ \ {1})) ∧
    ∀ b ∈ PoleSetQ \ {1}, meromorphicOrderAt F (k - 1 + b) = -1 ∧
      HasResidue F (k - 1 + b) (k * Rcoef b * Gamma b / Gamma (k - 1 + b)) ∧
      (k : ℂ) * Rcoef b * Gamma b / Gamma (k - 1 + b) ≠ 0 := by
  obtain ⟨-, -, hH, hFeq, -⟩ := hP
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  let A : Aff := ⟨1, 2 - (k : ℝ), one_pos⟩
  have happ : ∀ s : ℂ, A.app s - 1 = s - k + 1 := by
    intro s
    simp only [Aff.app, A]
    push_cast
    ring
  have hell : ((A.ell : ℝ) : ℂ) = 1 := by simp [A]
  set g : ℂ → ℂ := fun s => (k : ℂ) * (Gamma (s - k + 1) / Gamma s) with hg
  set G : ℂ → ℂ := fun s => H s + g s * Qcont (A.app s - 1) with hG
  have hstrip : IsOpen {s : ℂ | (k : ℝ) - 1 < s.re ∧ s.re < k} :=
    (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)
  -- local structure at a point of the strip
  have core : ∀ s₀ : ℂ, (k : ℝ) - 1 < s₀.re → s₀.re < k →
      F =ᶠ[𝓝[≠] s₀] G ∧ AnalyticAt ℂ H s₀ ∧ AnalyticAt ℂ g s₀ := by
    intro s₀ h1 h2
    have hmem : {s : ℂ | (k : ℝ) - 1 < s.re ∧ s.re < k} ∈ 𝓝 s₀ := hstrip.mem_nhds ⟨h1, h2⟩
    have hre : 0 < (s₀ - k + 1).re := by simp; linarith
    refine ⟨?_, hH.analyticAt hmem, ?_⟩
    · filter_upwards [nhdsWithin_le_nhds hmem, eventually_nhdsNE_notMem_poleSetQ_T1 k hre] with s hs hsP
      rw [hFeq s hs.1 hs.2 hsP, hG]
      simp only [happ, hg]
    · have hΓ1 : AnalyticAt ℂ (fun s => Gamma (s - k + 1)) s₀ :=
        (analyticAt_Gamma_T1 hre).comp_of_eq (by fun_prop) rfl
      have hΓ2 : AnalyticAt ℂ Gamma s₀ := analyticAt_Gamma_T1 (by linarith)
      have hne : Gamma s₀ ≠ 0 := Gamma_ne_zero_of_re_pos (by linarith)
      exact analyticAt_const.mul (hΓ1.div hΓ2 hne)
  -- the facts at a point `s₀` with `s₀ - k + 1 ∈ Σ_Q`
  have atPole : ∀ s₀ : ℂ, (k : ℝ) - 1 < s₀.re → s₀.re < k → s₀ - k + 1 ∈ PoleSetQ →
      MeromorphicAt F s₀ ∧ HasResidue F s₀ (g s₀ * Rcoef (s₀ - k + 1)) ∧ g s₀ * Rcoef (s₀ - k + 1) ≠ 0 := by
    intro s₀ h1 h2 hb
    obtain ⟨hev, hHa, hga⟩ := core s₀ h1 h2
    have hα : A.app s₀ = 1 + (s₀ - k + 1) := by rw [← happ]; ring
    obtain ⟨hm, hr⟩ := M4b.FillC2.add_mul_Qcont_app_facts A hHa hga hb hα
    rw [hell, div_one] at hr
    refine ⟨hm.congr hev.symm, M4b.hasResidue_congr_nhdsNE hr hev.symm, ?_⟩
    have hR : Rcoef (s₀ - k + 1) ≠ 0 := fun h => M4a.cP_ne_zero_of_RH hRH hb (by simp [cP, h])
    have hre : 0 < (s₀ - k + 1).re := by simp; linarith
    have hgne : g s₀ ≠ 0 := by
      simp only [hg]
      exact mul_ne_zero hk0 (div_ne_zero (Gamma_ne_zero_of_re_pos hre)
        (Gamma_ne_zero_of_re_pos (by linarith)))
    exact mul_ne_zero hgne hR
  refine ⟨fun s₀ h1 h2 => ?_, fun b hb => ?_⟩
  · have hsub : s₀ - ((k : ℂ) - 1) = s₀ - k + 1 := by ring
    rw [hsub]
    by_cases hb : s₀ - k + 1 ∈ PoleSetQ
    · obtain ⟨hm, hr, hc⟩ := atPole s₀ h1 h2 hb
      have hb1 : s₀ - k + 1 ≠ 1 := fun h => by
        have := congrArg Complex.re h
        simp at this
        linarith
      exact ⟨fun _ => ⟨hb, hb1⟩, fun _ => (M4b.FillC2.order_neg_iff_of_hasResidue hm hr).2 hc⟩
    · obtain ⟨hev, hHa, hga⟩ := core s₀ h1 h2
      have hre : 0 < (A.app s₀ - 1).re := by rw [happ]; simp; linarith
      have hQ : AnalyticAt ℂ Qcont (A.app s₀ - 1) :=
        M2.isQCont_Qcont.2.2 _ ⟨hre, by rw [happ]; exact hb⟩
      have hap : AnalyticAt ℂ (fun t => A.app t - 1) s₀ := by unfold Aff.app; fun_prop
      have han : AnalyticAt ℂ G s₀ := hHa.add (hga.mul (hQ.comp_of_eq hap rfl))
      have h0 : 0 ≤ meromorphicOrderAt F s₀ := by
        rw [meromorphicOrderAt_congr hev]
        exact han.meromorphicOrderAt_nonneg
      exact ⟨fun h => absurd h (not_lt.mpr h0), fun h => absurd h.1 hb⟩
  · obtain ⟨hb0, hbh⟩ := M4b.FillC2.re_le_half hRH hb
    set s₀ : ℂ := (k : ℂ) - 1 + b with hs₀
    have hres0 : s₀.re = (k : ℝ) - 1 + b.re := by simp [hs₀]
    have h1 : (k : ℝ) - 1 < s₀.re := by linarith
    have h2 : s₀.re < k := by linarith
    have hbe : s₀ - k + 1 = b := by rw [hs₀]; ring
    obtain ⟨hm, hr, hc⟩ := atPole s₀ h1 h2 (by rw [hbe]; exact hb.1)
    have hval : g s₀ * Rcoef (s₀ - k + 1) = (k : ℂ) * Rcoef b * Gamma b / Gamma ((k : ℂ) - 1 + b) := by
      simp only [hg, hbe]
      rw [hs₀]
      ring
    rw [hval] at hr hc
    refine ⟨?_, hr, hc⟩
    rw [hr.meromorphicOrderAt_eq_neg_one hm hc]
    rfl

end GoldbachBoundaries.Paper2.M5
