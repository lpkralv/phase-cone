import GoldbachBoundaries.Paper2.M5.TkStep
import GoldbachBoundaries.Paper2.M5.Fill.Tk_strip_facts

/-! Filler for `exists_pole_near_line_Tk` (M5, group T1). The argument of M4b's `exists_pole_near_line`: with
`L(s) = s - k + 2`, M4a's `prop_catalogue_ii_proof` puts a scaled-zero pinch `α = k - 1 + ρ/n` (`n` prime) in every
ball about a point of `σ = k - 1`; under RH `0 < Re(ρ/n) ≤ 1/2`, so `α` lies in the strip, and `Tk_strip_facts` gives a
pole there. -/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

theorem exists_pole_near_line_Tk (hRH : RiemannHypothesis) {k : ℕ} (hk : 2 ≤ k) {F H : ℂ → ℂ}
    (hP : TkPack k F H) :
    ∀ s₀ : ℂ, s₀.re = (k : ℝ) - 1 → ∀ ε > 0, ∃ a ∈ halfPlane ((k : ℝ) - 1), a ≠ s₀ ∧ a ∈ ball s₀ ε ∧
      meromorphicOrderAt F a < 0 := by
  intro s₀ hs₀ ε hε
  let A : Aff := ⟨1, 2 - (k : ℝ), one_pos⟩
  have happ : ∀ s : ℂ, A.app s = s - k + 2 := by
    intro s
    simp only [Aff.app, A]
    push_cast
    ring
  have hline : s₀ ∈ A.lineL := by
    show (A.app s₀).re = 1
    rw [happ]
    simp [hs₀]; norm_num
  obtain ⟨α, ρ, hρ, n, hn, hαe, hball⟩ := ((M4a.prop_catalogue_ii_proof hRH A s₀ hline ε hε).1).nonempty
  obtain ⟨-, -, hnline, hbS, hb1, -, -⟩ := M4a.scaledPinch_facts A hρ hn.one_lt.le hn.squarefree hαe
  have hαne : α ≠ s₀ := fun h => hnline (h ▸ hline)
  obtain ⟨hb0, hbh⟩ := M4b.FillC2.re_le_half hRH ⟨hbS, hb1⟩
  have hαeq : α = (k : ℂ) - 1 + ρ / (n : ℂ) := by
    rw [happ] at hαe
    linear_combination hαe
  have hre : α.re = (k : ℝ) - 1 + (ρ / (n : ℂ)).re := by rw [hαeq]; simp
  have h1 : (k : ℝ) - 1 < α.re := by linarith
  have h2 : α.re < k := by linarith
  have hsub : α - ((k : ℂ) - 1) = ρ / (n : ℂ) := by rw [hαeq]; ring
  refine ⟨α, h1, hαne, hball, ?_⟩
  rw [(Tk_strip_facts hRH hk hP).1 α h1 h2, hsub]
  exact ⟨hbS, hb1⟩

end GoldbachBoundaries.Paper2.M5
