import GoldbachBoundaries.Paper2.M4b.Fill.C1Common
import GoldbachBoundaries.Paper2.M4b.Fill.Ilog_step_one

/-!
# M4b filler C1: `Fmero_eq_upper`

`(cl:eq:Iplus)` on all of `upperL`: by definition for `Re L ≤ 2`; for `2 < Re L < 3`, (R) on the line `Re L(s)/2`,
where `Q = Qcont` on both factors, then Step 2 (`Ilog_step_one`) moves that line to `cPlus` across `z = 1`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M4b

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **`(cl:eq:Iplus)`** (RH, (K1), (K2), (R); Step 2). For `3/2 < Re L(s) ≤ 2` this is the definition of `Fmero`. For
`2 < Re L(s) < 3`: (R) with `c₀ = Re L(s)/2 ∈ (1, Re L(s) - 1)` gives `D^log(s) = (1/2πi)∫_{(c₀)} k Q Q`; on that line
both arguments have real part `c₀ > 1`, where `Q = Qcont` (`TIdentity.Qcont_eq_Q_of_one_lt`), so
`D^log(s) = Ilog A k c₀ s`; `Ilog_step_one` (`1/2 < cPlus A s ≤ 3/4 < 1 < c₀ < Re L(s) - 1`) gives
`Ilog A k c₀ s = k(1,s)Q(L(s)-1) + Iplus A k s`. -/
theorem Fmero_eq_upper (hRH : RiemannHypothesis) (A : Aff) (k : ℂ → ℂ → ℂ) (W : ℂ → ℕ → ℕ → ℂ)
    (hK1 : K1 A k) (hK2 : K2 A k) (hR : HypR A k W Q) {s : ℂ} (hs : s ∈ upperL A) :
    Fmero A k W s = Iplus A k s + k 1 s * Qcont (A.app s - 1) := by
  obtain ⟨h1, h2⟩ := hs
  have h3 : 3 / 2 < (A.app s).re := h1
  by_cases h4 : 2 < (A.app s).re
  · set c₀ : ℝ := (A.app s).re / 2 with hc₀
    have hD : Dser W s = VerticalIntegral' (fun z => k z s * Q z * Q (A.app s - z)) c₀ :=
      hR.2.2.2 s ⟨h4, ⟨by linarith, h2⟩⟩ c₀ (by linarith) (by linarith)
    have hline : VerticalIntegral' (fun z => k z s * Q z * Q (A.app s - z)) c₀ = Ilog A k c₀ s := by
      unfold Ilog VerticalIntegral' VerticalIntegral
      congr 2
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      have hz : 1 < ((c₀ : ℂ) + t * I).re := by simp; linarith
      have hz' : 1 < (A.app s - ((c₀ : ℂ) + t * I)).re := by simp; linarith
      simp only [TIdentity.Qcont_eq_Q_of_one_lt hz, TIdentity.Qcont_eq_Q_of_one_lt hz']
    have ha1 : 1 / 2 < cPlus A s := FillC1.half_lt_cPlus A h3
    have ha2 : cPlus A s ≤ 3 / 4 := FillC1.cPlus_le_left A s
    have hstep := Ilog_step_one hRH A k hK1 hK2 ⟨by linarith, h2⟩ (c := cPlus A s) (c' := c₀) ha1
      (by linarith) (by linarith) (by linarith)
    rw [Fmero_of_RL A k W h4, hD, hline, hstep]
    unfold Iplus
    ring
  · simp [Fmero, h4, h3]

end GoldbachBoundaries.Paper2.M4b
