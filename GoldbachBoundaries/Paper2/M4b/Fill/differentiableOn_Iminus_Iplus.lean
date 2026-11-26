import GoldbachBoundaries.Paper2.M4b.Fill.C1Common
import GoldbachBoundaries.Paper2.M4b.Fill.differentiableOn_Ilog

/-!
# M4b filler C1: `differentiableOn_Iminus_Iplus`

Near `s₀`, the moving line `cMinus A s` (resp. `cPlus A s`) is replaced by the fixed line through `s₀` without crossing
a pole (`Ilog_eq_of_no_pole`, through `FillC1.Ilog_eq_of_lines`), and the fixed-line integral is holomorphic
(`differentiableOn_Ilog`).
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M4b

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **`I` and `I⁺` are holomorphic** (RH, (K1), (K2); Step 1). Near `s₀ ∈ stripL`, with `c = Re L(s₀)/2`, on the open
`V = {1 < Re L < 2, Re L - 1 < c, c + 1/2 < Re L}` we have `Iminus = Ilog c` (both lines in `(1/2, 1)`, right of
`Re L - 1`), and `Ilog c` is holomorphic there. Near `s₀ ∈ upperL`, with `c = cPlus A s₀`, on
`V = {3/2 < Re L < 3, c + 1 < Re L}` we have `Iplus = Ilog c` (both lines in `(1/2, 3/4]`, left of `Re L - 1`). -/
theorem differentiableOn_Iminus_Iplus (hRH : RiemannHypothesis) (A : Aff) (k : ℂ → ℂ → ℂ) (hK1 : K1 A k)
    (hK2 : K2 A k) :
    DifferentiableOn ℂ (Iminus A k) (stripL A) ∧ DifferentiableOn ℂ (Iplus A k) (upperL A) := by
  have hcont := continuous_app_re' A
  constructor
  · intro s₀ hs₀
    obtain ⟨h1, h2⟩ := hs₀
    set c : ℝ := (A.app s₀).re / 2 with hc
    set V : Set ℂ := {s | 1 < (A.app s).re ∧ (A.app s).re < 2 ∧ (A.app s).re - 1 < c ∧
      c + 1 / 2 < (A.app s).re} with hV
    have hVo : IsOpen V :=
      (isOpen_lt continuous_const hcont).inter ((isOpen_lt hcont continuous_const).inter
        ((isOpen_lt (hcont.sub continuous_const) continuous_const).inter
          (isOpen_lt continuous_const hcont)))
    have hV0 : s₀ ∈ V := ⟨h1, h2, by linarith, by linarith⟩
    have hd := (differentiableOn_Ilog hRH A k hK1 hK2 (c := c) (by linarith) (by intro h; linarith)).1
    have hsub : V ⊆ {s | s ∈ A.DL ∧ c + 1 / 2 < (A.app s).re ∧ (A.app s).re - c ≠ 1} := by
      rintro s ⟨hs1, hs2, hs3, hs4⟩
      exact ⟨⟨hs1, by linarith⟩, hs4, by intro h; linarith⟩
    have hda : DifferentiableAt ℂ (Ilog A k c) s₀ :=
      hd.differentiableAt (Filter.mem_of_superset (hVo.mem_nhds hV0) hsub)
    have heq : Iminus A k =ᶠ[𝓝 s₀] Ilog A k c := by
      filter_upwards [hVo.mem_nhds hV0] with s hs
      obtain ⟨hs1, hs2, hs3, hs4⟩ := hs
      show Ilog A k (cMinus A s) s = Ilog A k c s
      unfold cMinus
      exact FillC1.Ilog_eq_of_lines hRH A k hK1 hK2 ⟨hs1, by linarith⟩ (by linarith) (by linarith)
        (by linarith) hs4 (by linarith) (by linarith) (Or.inr ⟨by linarith, hs3⟩)
    exact (heq.differentiableAt_iff.mpr hda).differentiableWithinAt
  · intro s₀ hs₀
    obtain ⟨h1, h2⟩ := hs₀
    set c : ℝ := cPlus A s₀ with hc
    have hc1 : 1 / 2 < c := FillC1.half_lt_cPlus A h1
    have hc2 : c ≤ 3 / 4 := FillC1.cPlus_le_left A s₀
    have hc3 : c ≤ ((A.app s₀).re - 1 / 2) / 2 := FillC1.cPlus_le_right A s₀
    set V : Set ℂ := {s | 3 / 2 < (A.app s).re ∧ (A.app s).re < 3 ∧ c + 1 < (A.app s).re} with hV
    have hVo : IsOpen V :=
      (isOpen_lt continuous_const hcont).inter ((isOpen_lt hcont continuous_const).inter
        (isOpen_lt continuous_const hcont))
    have hV0 : s₀ ∈ V := ⟨h1, h2, by linarith⟩
    have hd := (differentiableOn_Ilog hRH A k hK1 hK2 (c := c) hc1 (by intro h; linarith)).1
    have hsub : V ⊆ {s | s ∈ A.DL ∧ c + 1 / 2 < (A.app s).re ∧ (A.app s).re - c ≠ 1} := by
      rintro s ⟨hs1, hs2, hs3⟩
      exact ⟨⟨by linarith, hs2⟩, by linarith, by intro h; linarith⟩
    have hda : DifferentiableAt ℂ (Ilog A k c) s₀ :=
      hd.differentiableAt (Filter.mem_of_superset (hVo.mem_nhds hV0) hsub)
    have heq : Iplus A k =ᶠ[𝓝 s₀] Ilog A k c := by
      filter_upwards [hVo.mem_nhds hV0] with s hs
      obtain ⟨hs1, hs2, hs3⟩ := hs
      show Ilog A k (cPlus A s) s = Ilog A k c s
      have ha1 : 1 / 2 < cPlus A s := FillC1.half_lt_cPlus A hs1
      have ha2 : cPlus A s ≤ 3 / 4 := FillC1.cPlus_le_left A s
      have ha3 : cPlus A s ≤ ((A.app s).re - 1 / 2) / 2 := FillC1.cPlus_le_right A s
      exact FillC1.Ilog_eq_of_lines hRH A k hK1 hK2 ⟨by linarith, hs2⟩ ha1 hc1 (by linarith) (by linarith)
        (by linarith) (by linarith) (Or.inl ⟨by linarith, by linarith⟩)
    exact (heq.differentiableAt_iff.mpr hda).differentiableWithinAt

end GoldbachBoundaries.Paper2.M4b
