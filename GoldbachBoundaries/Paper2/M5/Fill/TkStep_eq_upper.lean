import GoldbachBoundaries.Paper2.M5.Fill.T3Common

/-!
# M5 filler T3: `TkStep_eq_upper`

On `σ > m + 1`: `T_{m+1}(s)` is the line integral at `c = (m + σ - 1)/2` (`Tk_succ_eq_verticalIntegral'`), which is
`TkLine F c s` (the integrands agree on the line); moving the line across `w = m` to `m - 1/4 = cPlusK m s`
(`TkLine_step_pole`) gives region (b)'s formula. On `m + 1/2 < σ ≤ m + 1` it is the definition.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

theorem TkStep_eq_upper (hRH : RiemannHypothesis) {m : ℕ} (hm : 1 ≤ m) {F H : ℂ → ℂ} (hP : TkPack m F H) :
    ∀ s : ℂ, (m : ℝ) + 1 / 2 < s.re →
      TkStep m F s = TkLine F (cPlusK m s) s + rK m * KerS s m * Qcont (s - m) := by
  intro s hs
  by_cases hup : ((m + 1 : ℕ) : ℝ) < s.re
  · have hup' : (m : ℝ) + 1 < s.re := by push_cast at hup; exact hup
    rw [TkStep_eqOn m F hup]
    set c : ℝ := ((m : ℝ) + (s.re - 1)) / 2 with hc
    have hc1 : (m : ℝ) < c := by rw [hc]; linarith
    have hc2 : c < s.re - 1 := by rw [hc]; linarith
    rw [(Tk_succ_eq_verticalIntegral' hm).2 s c hc1 hc2]
    have hline : VerticalIntegral' (fun w => KerS s w * Tk m w * Q (s - w)) c = TkLine F c s := by
      unfold TkLine VerticalIntegral' VerticalIntegral
      congr 2
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      simp only
      have hw : (m : ℝ) < ((c : ℂ) + t * I).re := by simp; exact hc1
      have hq : 1 < (s - ((c : ℂ) + t * I)).re := by simp; linarith
      rw [← hP.2.1 hw, TIdentity.Qcont_eq_Q_of_one_lt hq]
    rw [hline, TkLine_step_pole hRH hm hP (c := (m : ℝ) - 1 / 4) (by linarith) (by linarith) hc1 (by linarith),
      FillT3.cPlusK_of_le m hup'.le]
    ring
  · by_cases hmid : (m : ℝ) + 1 / 2 < s.re
    · unfold TkStep
      simp only [hup, hmid, ↓reduceIte]
    · exact absurd hs hmid

end GoldbachBoundaries.Paper2.M5
