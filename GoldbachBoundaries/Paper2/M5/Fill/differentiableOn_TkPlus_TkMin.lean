import GoldbachBoundaries.Paper2.M5.Fill.T3Common

/-!
# M5 filler T3: `differentiableOn_TkPlus_TkMin`

Near `s₀`, the moving line `cPlusK m s` (resp. `cMinK m s`) is replaced by the fixed line through `s₀` without crossing a
pole (`TkLine_eq_of_no_pole`, through `FillT3.TkLine_eq_of_lines`), and the fixed-line integral is holomorphic
(`TkLine_differentiableOn`). As M4b's `differentiableOn_Iminus_Iplus`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

theorem differentiableOn_TkPlus_TkMin (hRH : RiemannHypothesis) {m : ℕ} (hm : 1 ≤ m) {F H : ℂ → ℂ}
    (hP : TkPack m F H) :
    DifferentiableOn ℂ (fun s => TkLine F (cPlusK m s) s) {s | (m : ℝ) + 1 / 2 < s.re} ∧
      DifferentiableOn ℂ (fun s => TkLine F (cMinK m s) s) {s | (m : ℝ) < s.re ∧ s.re < m + 1} := by
  have hcont := Complex.continuous_re
  constructor
  · intro s₀ hs₀
    have hs₀' : (m : ℝ) + 1 / 2 < s₀.re := hs₀
    set c : ℝ := cPlusK m s₀ with hc
    obtain ⟨hc1, hc2, hc3⟩ := FillT3.cPlusK_bounds m hs₀'
    set V : Set ℂ := {s | (m : ℝ) + 1 / 2 < s.re ∧ c + 1 < s.re} with hV
    have hVo : IsOpen V :=
      (isOpen_lt continuous_const hcont).inter (isOpen_lt continuous_const hcont)
    have hV0 : s₀ ∈ V := ⟨hs₀', by linarith⟩
    have hd := (TkLine_differentiableOn hRH hm hP (c := c) hc1 (ne_of_lt hc2)).1
    have hsub : V ⊆ {s | c + 1 / 2 < s.re ∧ s.re - c ≠ 1} := by
      rintro s ⟨hs1, hs2⟩
      exact ⟨by linarith, by intro h; linarith⟩
    have hda : DifferentiableAt ℂ (TkLine F c) s₀ :=
      hd.differentiableAt (Filter.mem_of_superset (hVo.mem_nhds hV0) hsub)
    have heq : (fun s => TkLine F (cPlusK m s) s) =ᶠ[𝓝 s₀] TkLine F c := by
      filter_upwards [hVo.mem_nhds hV0] with s hs
      obtain ⟨hs1, hs2⟩ := hs
      obtain ⟨ha1, ha2, ha3⟩ := FillT3.cPlusK_bounds m hs1
      exact FillT3.TkLine_eq_of_lines hRH hm hP ha1 hc1 (by linarith) (by linarith) ha2 hc2
        (Or.inl ⟨ha3, by linarith⟩)
    exact (heq.differentiableAt_iff.mpr hda).differentiableWithinAt
  · intro s₀ hs₀
    obtain ⟨h1, h2⟩ := hs₀
    set c : ℝ := cMinK m s₀ with hc
    obtain ⟨hc1, hc2, hc3, hc4⟩ := FillT3.cMinK_bounds m h1 h2
    set V : Set ℂ := {s | (m : ℝ) < s.re ∧ s.re < m + 1 ∧ s.re - 1 < c ∧ c + 1 / 2 < s.re} with hV
    have hVo : IsOpen V :=
      (isOpen_lt continuous_const hcont).inter ((isOpen_lt hcont continuous_const).inter
        ((isOpen_lt (hcont.sub continuous_const) continuous_const).inter
          (isOpen_lt continuous_const hcont)))
    have hV0 : s₀ ∈ V := ⟨h1, h2, hc2, hc4⟩
    have hd := (TkLine_differentiableOn hRH hm hP (c := c) hc1 (ne_of_lt hc3)).1
    have hsub : V ⊆ {s | c + 1 / 2 < s.re ∧ s.re - c ≠ 1} := by
      rintro s ⟨hs1, hs2, hs3, hs4⟩
      exact ⟨hs4, by intro h; linarith⟩
    have hda : DifferentiableAt ℂ (TkLine F c) s₀ :=
      hd.differentiableAt (Filter.mem_of_superset (hVo.mem_nhds hV0) hsub)
    have heq : (fun s => TkLine F (cMinK m s) s) =ᶠ[𝓝 s₀] TkLine F c := by
      filter_upwards [hVo.mem_nhds hV0] with s hs
      obtain ⟨hs1, hs2, hs3, hs4⟩ := hs
      obtain ⟨ha1, ha2, ha3, ha4⟩ := FillT3.cMinK_bounds m hs1 hs2
      exact FillT3.TkLine_eq_of_lines hRH hm hP ha1 hc1 ha4 hs4 ha3 hc3 (Or.inr ⟨ha2, hs3⟩)
    exact (heq.differentiableAt_iff.mpr hda).differentiableWithinAt

end GoldbachBoundaries.Paper2.M5
