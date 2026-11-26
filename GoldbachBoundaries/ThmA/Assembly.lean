import GoldbachBoundaries.ThmA.G20_Branches
import GoldbachBoundaries.ThmA.Fill.Dc_access_two
import GoldbachBoundaries.ThmA.Fill.Dc_eq_diag
import GoldbachBoundaries.ThmA.Fill.Dc_local_two
import GoldbachBoundaries.ThmA.Fill.F0_mellin
import GoldbachBoundaries.ThmA.Fill.F0_split
import GoldbachBoundaries.ThmA.Fill.Gb_spec
import GoldbachBoundaries.ThmA.Fill.Gnat_access
import GoldbachBoundaries.ThmA.Fill.Gnat_local
import GoldbachBoundaries.ThmA.Fill.Gnat_spec
import GoldbachBoundaries.ThmA.Fill.J_spec
import GoldbachBoundaries.ThmA.Fill.M0_identity
import GoldbachBoundaries.ThmA.Fill.N1A_access
import GoldbachBoundaries.ThmA.Fill.N1A_local
import GoldbachBoundaries.ThmA.Fill.PsegA_split
import GoldbachBoundaries.ThmA.Fill.Pv_eq_Eb_add
import GoldbachBoundaries.ThmA.Fill.Pv_spec
import GoldbachBoundaries.ThmA.Fill.Qcont_pole_split
import GoldbachBoundaries.ThmA.Fill.X_deriv_spec
import GoldbachBoundaries.ThmA.Fill.analyticAt_N1A
import GoldbachBoundaries.ThmA.Fill.analyticOn_Dc
import GoldbachBoundaries.ThmA.Fill.catalogue_countable
import GoldbachBoundaries.ThmA.Fill.catalogue_locallyFinite
import GoldbachBoundaries.ThmA.Fill.cauchyEnd
import GoldbachBoundaries.ThmA.Fill.cauchyInt
import GoldbachBoundaries.ThmA.Fill.cutDisc_facts
import GoldbachBoundaries.ThmA.Fill.cuts_locallyFinite
import GoldbachBoundaries.ThmA.Fill.decomp_exists
import GoldbachBoundaries.ThmA.Fill.differentiableOn_intervalIntegral_of_continuousOn
import GoldbachBoundaries.ThmA.Fill.exists_Eaux
import GoldbachBoundaries.ThmA.Fill.exists_component_reaching_line
import GoldbachBoundaries.ThmA.Fill.exists_continuationAlong_of_uniform
import GoldbachBoundaries.ThmA.Fill.exists_goodSlant_of_countable
import GoldbachBoundaries.ThmA.Fill.exists_good_discs
import GoldbachBoundaries.ThmA.Fill.exists_path_into
import GoldbachBoundaries.ThmA.Fill.germ_unique
import GoldbachBoundaries.ThmA.Fill.isBranch_uniform_cut
import GoldbachBoundaries.ThmA.Fill.isContinuationAlong_concat
import GoldbachBoundaries.ThmA.Fill.isPreconnected_Omega_inter
import GoldbachBoundaries.ThmA.Fill.jump_of_access
import GoldbachBoundaries.ThmA.Fill.logEnd
import GoldbachBoundaries.ThmA.Fill.logInt
import GoldbachBoundaries.ThmA.Fill.no_analytic_across_log
import GoldbachBoundaries.ThmA.Fill.norm_Eaux_le
import GoldbachBoundaries.ThmA.Fill.slitDisc_facts
import GoldbachBoundaries.ThmA.Fill.verticalIntegral_CauchyS_shift
import GoldbachBoundaries.ThmA.Fill.verticalIntegral_Eb_shift

/-!
# Theorem A: the 46 lemmas, assembled

Imports the proof of each of the 46 lemmas of `G13`–`G20` (`Fill/<name>.lean`, one theorem `<name>`
per file, statement verbatim from the skeleton) and proves the real lemmas of the skeleton that use
them: `continuationAlong_preserve` (from `G13_Continuation`), `isPrincipalSheet_Gnat` (from
`G18_LocalAccess`), `isBranch_uniform_omega`, `isBranch_uniform`, `isBranch_of_admissible` (from
`G20_Branches`). The other real lemmas that use one of the 46 sit at the end of the fill file of the
lemma they use: `Eaux_spec` in `Fill/exists_Eaux.lean`; `X_differentiableOn`, `Mon_analyticOn`,
`MSpan_analyticOn` in `Fill/J_spec.lean`; `Htil_spec` in `Fill/decomp_exists.lean`.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open scoped Interval

namespace GoldbachBoundaries.ThmA

/-! From `G13_Continuation.lean`. -/

/-- **Preservation.** Along any continuation in `U` that starts in a uniform, germ-invariant family,
every germ is in the family (existence plus uniqueness). -/
theorem continuationAlong_preserve {B : ℂ → (ℂ → ℂ) → Prop} {U : Set ℂ}
    (hB : UniformFamily B U) (hcongr : ∀ p f g, B p f → f =ᶠ[𝓝 p] g → B p g)
    {γ : C(unitInterval, ℂ)} (hγ : ∀ t, γ t ∈ U) {f : unitInterval → ℂ → ℂ}
    (hf : IsContinuationAlong γ f) (h0 : B (γ 0) (f 0)) (t : unitInterval) : B (γ t) (f t) := by
  obtain ⟨g, hg, hg0, hgB⟩ := exists_continuationAlong_of_uniform hB hγ h0
  exact hcongr _ _ _ (hgB t) (germ_unique hg hf hg0 t)

/-! From `G18_LocalAccess.lean`. -/

/-- The principal sheet `G^♮` has all the properties used downstream. -/
theorem isPrincipalSheet_Gnat (hRH : RiemannHypothesis) {κ : ℝ} (hκ : IsGoodSlant κ) :
    IsPrincipalSheet κ (Gnat κ) where
  analyticOn := (Gnat_spec hRH κ).1
  eq_G := (Gnat_spec hRH κ).2.1
  local_form _ hα := Gnat_local hRH hκ hα
  access _ hα _ hs₀ hne := Gnat_access hRH hκ hα hs₀ hne

/-! From `G20_Branches.lean`. -/

/-- **G20a'. `prop:branches`, the discs `V_p` for `p ∈ Ω_ℍ`.** -/
theorem isBranch_uniform_omega {κ : ℝ} {Gn : ℂ → ℂ} (hP : IsPrincipalSheet κ Gn) {p : ℂ}
    (hp : p ∈ Omega κ) :
    ∃ r : ℝ, 0 < r ∧ ∀ q ∈ ball p r, ∀ f : ℂ → ℂ, IsBranch κ Gn q f →
      ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F (ball p r) ∧ F =ᶠ[𝓝 q] f ∧
        ∀ q' ∈ ball p r, IsBranch κ Gn q' F := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (cuts_locallyFinite κ).2 p hp
  refine ⟨r, hr, fun q hq f hf => ?_⟩
  obtain ⟨m, hm, hfm⟩ := hf.2.self_of_nhds (hball hq)
  have hmA := MSpan_analyticOn hm
  have hFA : AnalyticOnNhd ℂ (fun s => Gn s + m s) (ball p r) := fun z hz =>
    (hP.analyticOn z (hball hz)).add (hmA z (Omega_subset (hball hz)).1)
  refine ⟨fun s => Gn s + m s, hFA, hfm.symm, fun q' hq' => ⟨hFA q' hq', ?_⟩⟩
  exact Eventually.of_forall fun _ _ => ⟨m, hm, EventuallyEq.rfl⟩

/-! From `G20_Branches.lean`. -/

/-- **`prop:branches`, uniformity on `ℍ ∖ 𝒞`.** -/
theorem isBranch_uniform {κ : ℝ} (hκ : IsGoodSlant κ) {Gn : ℂ → ℂ}
    (hP : IsPrincipalSheet κ Gn) : UniformFamily (IsBranch κ Gn) (HH \ catalogue) := by
  intro p hp
  rcases mem_Omega_or_mem_cut (κ := κ) hp with h | ⟨α, hα, hpα, hne⟩
  · exact isBranch_uniform_omega hP h
  · exact isBranch_uniform_cut hκ hP hα hpα hne

/-! From `G20_Branches.lean`. -/

/-- Every admissible germ is a branch (preservation of the uniform family along the path). -/
theorem isBranch_of_admissible {κ : ℝ} (hκ : IsGoodSlant κ) {Gn : ℂ → ℂ}
    (hP : IsPrincipalSheet κ Gn) {g : ℂ → ℂ} {s₁ : ℂ} (hg : IsAdmissibleGerm g s₁) :
    IsBranch κ Gn s₁ g := by
  obtain ⟨γ, hγ, h2, h1, f, hf, hf0, hg1⟩ := hg
  have h0 : IsBranch κ Gn (γ 0) (f 0) := isBranch_congr (isBranch_G hP h2) hf0.symm
  have h := continuationAlong_preserve (isBranch_uniform hκ hP)
    (fun _ _ _ h e => isBranch_congr h e) hγ hf h0 1
  rw [← h1]; exact isBranch_congr h hg1.symm

end GoldbachBoundaries.ThmA
