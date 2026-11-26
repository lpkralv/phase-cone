import GoldbachBoundaries.Paper2.M3.Fill.Gamma_mul_Qcont_eq_of_mem

/-!
# Fill: `Rcoef_eq_zero_of_mem_mellinConvSet` (filler group F)

Near `a` (punctured, `Σ_Q` locally finite) `Qcont = (1/(z-1) + m₁ + e₁)/Γ` (`Gamma_mul_Qcont_eq_of_mem`), a
function analytic at `a`; so the order of `Qcont` at `a` is `≥ 0` and M1's `meromorphicOrderAt_Qcont_neg_iff` gives
`R_a = 0`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M3

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **Step 3, no pole of `Q` right of `x/2`** (unconditional). Let `a ∈ Σ_Q`, `Re a > x/2`, `a ≠ 1`. `Σ_Q` is locally
finite (M1's `poleSetQ_locallyFinite`), so on a punctured neighbourhood of `a` inside `H` (as in
`Gamma_mul_Qcont_eq_of_mem`) `Qcont = (1/(z - 1) + m₁(z) + e₁(z))/Γ(z)`, a function analytic at `a` (`1/Γ` entire,
`a ≠ 1`). So `meromorphicOrderAt Qcont a ≥ 0` (`meromorphicOrderAt_congr`, `AnalyticAt.meromorphicOrderAt_nonneg`),
and M1's `meromorphicOrderAt_Qcont_neg_iff` gives `R_a = 0`. Size: 100–200 lines. -/
theorem Rcoef_eq_zero_of_mem_mellinConvSet {x : ℝ} (hx : x ∈ mellinConvSet) {a : ℂ} (ha : a ∈ PoleSetQ)
    (hax : x / 2 < a.re) (ha1 : a ≠ 1) : Rcoef a = 0 := by
  by_contra hR
  have hneg : meromorphicOrderAt Qcont a < 0 := (meromorphicOrderAt_Qcont_neg_iff ha).mpr hR
  have ha0 : 0 < a.re := re_pos_of_mem_poleSetQ ha
  set G : ℂ → ℂ := fun w => (Gamma w)⁻¹ * (1 / (w - 1) + TIdentity.m1 w + TIdentity.e1 w) with hG
  have hGa : AnalyticAt ℂ G a := by
    have hinv : AnalyticAt ℂ (fun w => (Gamma w)⁻¹) a := by
      have := Complex.differentiable_one_div_Gamma.analyticAt a
      simpa [one_div] using this
    have h1 : AnalyticAt ℂ (fun w : ℂ => 1 / (w - 1)) a :=
      analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr ha1)
    have hm1 : AnalyticAt ℂ TIdentity.m1 a :=
      (differentiableOn_m1_of_mem hx).analyticAt ((isOpen_lt continuous_const continuous_re).mem_nhds hax)
    exact hinv.mul ((h1.add hm1).add (TIdentity.differentiable_e1.analyticAt a))
  -- punctured neighbourhood of `a` free of `Σ_Q`, inside `Re > max(0, x/2)`
  obtain ⟨U, hU, hUf⟩ := poleSetQ_locallyFinite a ha0
  have hfin : ((U ∩ PoleSetQ) \ {a}).Finite := hUf.sdiff
  have hcl : (((U ∩ PoleSetQ) \ {a})ᶜ) ∈ 𝓝 a :=
    hfin.isClosed.isOpen_compl.mem_nhds (fun h => h.2 rfl)
  have hre : {w : ℂ | max 0 (x / 2) < w.re} ∈ 𝓝 a :=
    (isOpen_lt continuous_const continuous_re).mem_nhds (max_lt ha0 hax)
  have heq : Qcont =ᶠ[𝓝[≠] a] G := by
    have h := (inter_mem (inter_mem hU hcl) hre)
    filter_upwards [nhdsWithin_le_nhds h, self_mem_nhdsWithin] with w hw hwa
    obtain ⟨⟨hwU, hwc⟩, hwre⟩ := hw
    have hwre' : max 0 (x / 2) < w.re := hwre
    have hw0 : 0 < w.re := lt_of_le_of_lt (le_max_left _ _) hwre'
    have hwx : x / 2 < w.re := lt_of_le_of_lt (le_max_right _ _) hwre'
    have hwP : w ∉ PoleSetQ := fun hP => hwc ⟨⟨hwU, hP⟩, hwa⟩
    have hΓ : Gamma w ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hw0
    have := Gamma_mul_Qcont_eq_of_mem hx hw0 hwx hwP
    simp only [hG]
    rw [← this, ← mul_assoc, inv_mul_cancel₀ hΓ, one_mul]
  have hnn : 0 ≤ meromorphicOrderAt Qcont a := by
    rw [meromorphicOrderAt_congr heq]
    exact hGa.meromorphicOrderAt_nonneg
  exact absurd hneg (not_lt.mpr hnn)

end GoldbachBoundaries.Paper2.M3
