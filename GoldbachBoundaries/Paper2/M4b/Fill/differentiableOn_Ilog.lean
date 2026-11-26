import GoldbachBoundaries.Paper2.M4b.Fill.norm_integrand_le_far
import GoldbachBoundaries.Paper2.M4b.Fill.differentiableAt_integrand

/-!
# Fill: `differentiableOn_Ilog`

M1's `differentiableOn_verticalIntegral'` with `F s z = k(z,s)Q(z)Q(L(s)-z)` on the open set
`U = {s ∈ D_L : c + 1/2 < Re L(s), Re L(s) - c ≠ 1}`. On the line `Re z = c` the integrand has no pole (`c ≠ 1`,
`Re L(s) - c ≠ 1`), so `differentiableAt_integrand` gives joint continuity and holomorphy in `s`. Domination on a
compact `K ⊆ U`: `M(1+|y|)^{-3/2}` for `|y| ≥ Y` (`norm_integrand_le_far` with `c₁ = c₂ = c`) and a constant on
`K × [-Y, Y]` (compactness). Integrability on the line: the same bound with `K = {s}`.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M4b

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- The domination and continuity facts for the integrand on the line `Re z = c`, packaged for reuse. -/
lemma Ilog_line_facts (hRH : RiemannHypothesis) (A : Aff) (k : ℂ → ℂ → ℂ) (hK1 : K1 A k)
    (hK2 : K2 A k) {c : ℝ} (hc : 1 / 2 < c) (hc1 : c ≠ 1) :
    let U := {s | s ∈ A.DL ∧ c + 1 / 2 < (A.app s).re ∧ (A.app s).re - c ≠ 1}
    let F : ℂ → ℂ → ℂ := fun s z => k z s * Qcont z * Qcont (A.app s - z)
    IsOpen U ∧ ContinuousOn (fun p : ℂ × ℝ => F p.1 (c + p.2 * I)) (U ×ˢ univ) ∧
      (∀ y : ℝ, DifferentiableOn ℂ (fun s => F s (c + y * I)) U) ∧
      ∀ K ⊆ U, IsCompact K → ∃ g : ℝ → ℝ, Integrable g ∧
        ∀ s ∈ K, ∀ y : ℝ, ‖F s (c + y * I)‖ ≤ g y := by
  intro U F
  have hUo : IsOpen U :=
    (M4a.isOpen_DL A).inter ((isOpen_lt continuous_const (continuous_app_re' A)).inter
      (isOpen_ne_fun ((continuous_app_re' A).sub continuous_const) continuous_const))
  have hpt : ∀ s ∈ U, ∀ y : ℝ, DifferentiableAt ℂ
      (fun p : ℂ × ℂ => k p.1 p.2 * Qcont p.1 * Qcont (A.app p.2 - p.1)) ((c : ℂ) + y * I, s) := by
    intro s hs y
    obtain ⟨hsD, hcs, hne⟩ := hs
    apply differentiableAt_integrand hRH A k hK1 hsD
    · simpa using hc
    · simp; linarith
    · intro h; have := congrArg Complex.re h; simp at this; exact hc1 this
    · intro h; have := congrArg Complex.re h; simp at this; exact hne (by linarith)
  have hcont : ContinuousOn (fun p : ℂ × ℝ => F p.1 (c + p.2 * I)) (U ×ˢ univ) := by
    intro p hp
    have := (hpt p.1 hp.1 p.2).continuousAt.comp
      (f := fun q : ℂ × ℝ => ((c : ℂ) + q.2 * I, q.1)) (by fun_prop)
    exact this.continuousWithinAt
  have hhol : ∀ y : ℝ, DifferentiableOn ℂ (fun s => F s (c + y * I)) U := by
    intro y s hs
    exact (DifferentiableAt.comp (f := fun s : ℂ => ((c : ℂ) + y * I, s)) s (hpt s hs y)
      (by fun_prop)).differentiableWithinAt
  refine ⟨hUo, hcont, hhol, ?_⟩
  intro K hKU hK
  obtain ⟨M, Y, hMY⟩ := norm_integrand_le_far hRH A k hK2 hK (fun s hs => (hKU hs).1) hc le_rfl
    (fun s hs => (hKU hs).2.1)
  obtain ⟨B, hB⟩ := (hK.prod (isCompact_Icc (a := -Y) (b := Y))).exists_bound_of_continuousOn
    (hcont.mono (prod_mono hKU (subset_univ _)))
  refine ⟨fun y => Set.indicator (Icc (-Y) Y) (fun _ => max B 0) y + |M| * (1 + ‖y‖) ^ (-(3 / 2 : ℝ)),
    ?_, ?_⟩
  · refine Integrable.add ?_ ?_
    · exact (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
    · exact (integrable_one_add_norm (by norm_num)).const_mul _
  · intro s hs y
    have hind0 : 0 ≤ Set.indicator (Icc (-Y) Y) (fun _ => max B 0) y :=
      Set.indicator_nonneg (fun _ _ => le_max_right _ _) _
    have hpos : 0 < 1 + |y| := by positivity
    have htail0 : 0 ≤ |M| * (1 + ‖y‖) ^ (-(3 / 2 : ℝ)) := by positivity
    by_cases hy : Y ≤ |y|
    · have h1 := hMY s hs ((c : ℂ) + y * I) (by simp) (by simp) (by simpa using hy)
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
        zero_add] at h1
      have h2 : M / (1 + |y|) ^ (3 / 2 : ℝ) ≤ |M| * (1 + ‖y‖) ^ (-(3 / 2 : ℝ)) := by
        rw [Real.norm_eq_abs, Real.rpow_neg hpos.le, ← div_eq_mul_inv]
        exact div_le_div_of_nonneg_right (le_abs_self M) (by positivity)
      show ‖F s (c + y * I)‖ ≤ _
      linarith
    · have hyI : y ∈ Icc (-Y) Y := by
        rw [mem_Icc, ← abs_le]; exact (lt_of_not_ge hy).le
      have h1 := hB (s, y) ⟨hs, hyI⟩
      show ‖F s (c + y * I)‖ ≤ Set.indicator (Icc (-Y) Y) (fun _ => max B 0) y + _
      rw [Set.indicator_of_mem hyI]
      have : ‖F s (c + y * I)‖ ≤ max B 0 := h1.trans (le_max_left _ _)
      linarith

/-- **Holomorphy of `I_c` and integrability on its line** (RH, (K1), (K2); Step 1). The set `U_c` is open. On the
line `Re z = c` the integrand has no pole: `z = 1` only if `c = 1`, `L(s) - z = 1` only if `Re L(s) - c = 1`. Apply
M1's `differentiableOn_verticalIntegral'` with `F s z = k(z,s)Q(z)Q(L(s)-z)`: joint continuity and holomorphy in `s`
from `differentiableAt_integrand`; domination on a compact `K ⊆ U_c` by `M(1+|y|)^{-3/2}` for `|y| ≥ Y`
(`norm_integrand_le_far` with `c₁ = c₂ = c`, `K`) and by a constant for `|y| ≤ Y` (continuity on the compact
`K × [-Y, Y]`, `IsCompact.exists_bound_of_continuousOn`). Integrability on the line: the same two bounds. Size:
150–250 lines. -/
theorem differentiableOn_Ilog (hRH : RiemannHypothesis) (A : Aff) (k : ℂ → ℂ → ℂ) (hK1 : K1 A k)
    (hK2 : K2 A k) {c : ℝ} (hc : 1 / 2 < c) (hc1 : c ≠ 1) :
    DifferentiableOn ℂ (Ilog A k c)
        {s | s ∈ A.DL ∧ c + 1 / 2 < (A.app s).re ∧ (A.app s).re - c ≠ 1} ∧
      ∀ s, s ∈ A.DL → c + 1 / 2 < (A.app s).re → (A.app s).re - c ≠ 1 →
        Integrable (fun y : ℝ => k (c + y * I) s * Qcont (c + y * I) * Qcont (A.app s - (c + y * I))) := by
  obtain ⟨hUo, hcont, hhol, hdom⟩ := Ilog_line_facts hRH A k hK1 hK2 hc hc1
  refine ⟨M1.differentiableOn_verticalIntegral' hUo hcont hhol hdom, ?_⟩
  intro s hsD hcs hne
  have hsU : s ∈ {s | s ∈ A.DL ∧ c + 1 / 2 < (A.app s).re ∧ (A.app s).re - c ≠ 1} := ⟨hsD, hcs, hne⟩
  obtain ⟨g, hg, hgb⟩ := hdom {s} (singleton_subset_iff.mpr hsU) isCompact_singleton
  have hcy : Continuous fun y : ℝ =>
      k (c + y * I) s * Qcont (c + y * I) * Qcont (A.app s - (c + y * I)) := by
    have := hcont.comp_continuous (f := fun y : ℝ => (s, y)) (by fun_prop) (fun y => ⟨hsU, trivial⟩)
    exact this
  exact hg.mono' hcy.aestronglyMeasurable (ae_of_all _ fun y => hgb s rfl y)

end GoldbachBoundaries.Paper2.M4b
