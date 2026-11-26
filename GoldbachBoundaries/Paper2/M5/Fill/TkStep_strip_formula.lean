import GoldbachBoundaries.Paper2.M5.Fill.TkStep_eq_strip
import GoldbachBoundaries.Paper2.M5.Fill.differentiableOn_TkPlus_TkMin

/-!
# M5 filler T3: `TkStep_strip_formula`

`HkStep m F H s = I(s) + H(s-1)/(s-1)` is holomorphic on the strip, and region (c)'s formula (`TkStep_eq_strip`) with
field 4 of the package at `s - 1`, `(s - 1)Γ(s - 1) = Γ(s)` and `r_m K_s(m) = Γ(s - m)/Γ(s)` gives the coefficient
`m + 1`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

theorem TkStep_strip_formula (hRH : RiemannHypothesis) {m : ℕ} (hm : 1 ≤ m) {F H : ℂ → ℂ}
    (hP : TkPack m F H) :
    DifferentiableOn ℂ (HkStep m F H) {s | ((m + 1 : ℕ) : ℝ) - 1 < s.re ∧ s.re < ((m + 1 : ℕ) : ℝ)} ∧
      ∀ s : ℂ, ((m + 1 : ℕ) : ℝ) - 1 < s.re → s.re < ((m + 1 : ℕ) : ℝ) →
        s - ((m + 1 : ℕ) : ℂ) + 1 ∉ PoleSetQ →
          TkStep m F s = HkStep m F H s +
            ((m + 1 : ℕ) : ℂ) * (Gamma (s - ((m + 1 : ℕ) : ℂ) + 1) / Gamma s) * Qcont (s - ((m + 1 : ℕ) : ℂ) + 1) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hset : {s : ℂ | ((m + 1 : ℕ) : ℝ) - 1 < s.re ∧ s.re < ((m + 1 : ℕ) : ℝ)} =
      {s : ℂ | (m : ℝ) < s.re ∧ s.re < m + 1} := by
    ext s; simp only [mem_ofPred_eq]; push_cast; constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, h2⟩
  refine ⟨?_, fun s hs1 hs2 hsQ => ?_⟩
  · rw [hset]
    have hI := (differentiableOn_TkPlus_TkMin hRH hm hP).2
    have hH : DifferentiableOn ℂ (fun s => H (s - 1)) {s : ℂ | (m : ℝ) < s.re ∧ s.re < m + 1} := by
      refine hP.2.2.1.comp (f := fun s : ℂ => s - 1) (by fun_prop) ?_
      rintro s ⟨h1, h2⟩
      simp only [mem_ofPred_eq, sub_re, one_re]
      exact ⟨by linarith, by linarith⟩
    have hden : DifferentiableOn ℂ (fun s : ℂ => s - 1) {s : ℂ | (m : ℝ) < s.re ∧ s.re < m + 1} := by fun_prop
    have hne : ∀ s ∈ {s : ℂ | (m : ℝ) < s.re ∧ s.re < m + 1}, s - 1 ≠ 0 := by
      rintro s ⟨h1, _⟩ h
      have : (s - 1).re = 0 := by rw [h]; simp
      simp at this; linarith
    exact hI.add (hH.div hden hne)
  · have hs1' : (m : ℝ) < s.re := by push_cast at hs1; linarith
    have hs2' : s.re < (m : ℝ) + 1 := by push_cast at hs2; exact hs2
    have hcast : s - ((m + 1 : ℕ) : ℂ) + 1 = s - m := by push_cast; ring
    rw [hcast] at hsQ ⊢
    rw [TkStep_eq_strip hRH hm hP s hs1' hs2']
    have hre1 : (m : ℝ) - 1 < (s - 1).re := by simp; linarith
    have hre2 : (s - 1).re < m := by simp; linarith
    have hQ' : s - 1 - m + 1 ∉ PoleSetQ := by rwa [show s - 1 - m + 1 = s - m by ring]
    have h4 := hP.2.2.2.1 (s - 1) hre1 hre2 hQ'
    rw [show s - 1 - m + 1 = s - m by ring] at h4
    have hpos1 : 0 < (s - 1).re := by simp; linarith
    have hpos : 0 < s.re := by linarith
    have hG1 : Gamma (s - 1) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hpos1
    have hG : Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hpos
    have hs10 : s - 1 ≠ 0 := by
      intro h; have : (s - 1).re = 0 := by rw [h]; simp
      linarith
    have hrec : Gamma s = (s - 1) * Gamma (s - 1) := by
      have := Complex.Gamma_add_one (s - 1) hs10
      rwa [sub_add_cancel] at this
    rw [h4, FillT3.rK_mul_KerS hm]
    unfold HkStep
    rw [hrec]
    field_simp
    push_cast
    ring

end GoldbachBoundaries.Paper2.M5
