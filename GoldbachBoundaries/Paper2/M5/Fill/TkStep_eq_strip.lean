import GoldbachBoundaries.Paper2.M5.Fill.TkStep_eq_upper

/-!
# M5 filler T3: `TkStep_eq_strip`

On `σ ≤ m + 1/2` it is the definition of `TkStep`. On `m + 1/2 < σ < m + 1`: region (b)'s formula
(`TkStep_eq_upper`) and the move across `w = s - 1` from `cPlusK m s < σ - 1` to `cMinK m s > σ - 1`
(`TkLine_step_sub_one`).
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

theorem TkStep_eq_strip (hRH : RiemannHypothesis) {m : ℕ} (hm : 1 ≤ m) {F H : ℂ → ℂ} (hP : TkPack m F H) :
    ∀ s : ℂ, (m : ℝ) < s.re → s.re < m + 1 →
      TkStep m F s = TkLine F (cMinK m s) s + F (s - 1) / (s - 1) + rK m * KerS s m * Qcont (s - m) := by
  intro s hs1 hs2
  by_cases hmid : (m : ℝ) + 1 / 2 < s.re
  · rw [TkStep_eq_upper hRH hm hP s hmid]
    obtain ⟨ha1, ha2, ha3⟩ := FillT3.cPlusK_bounds m hmid
    obtain ⟨hb1, hb2, hb3, hb4⟩ := FillT3.cMinK_bounds m hs1 hs2
    have hcx : cPlusK m s < s.re - 1 := by
      rw [FillT3.cPlusK_of_lt m hs2]; linarith
    rw [TkLine_step_sub_one hRH hm hP ha1 hcx hb2 hb3 hb4]
    ring
  · have hup : ¬ ((m + 1 : ℕ) : ℝ) < s.re := by push_cast; intro h; linarith
    unfold TkStep
    simp only [hup, hmid, ↓reduceIte]

end GoldbachBoundaries.Paper2.M5
