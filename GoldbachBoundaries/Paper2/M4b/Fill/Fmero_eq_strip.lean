import GoldbachBoundaries.Paper2.M4b.Fill.C1Common
import GoldbachBoundaries.Paper2.M4b.Fill.Ilog_step_sub_one

/-!
# M4b filler C1: `Fmero_eq_strip`

`(cl:eq:strip)` on all of `stripL`: by definition for `Re L ≤ 3/2`; for `3/2 < Re L < 2`, Step 3
(`Ilog_step_sub_one`) moves `cPlus` to `cMinus` across `z = L(s) - 1`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M4b

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **`(cl:eq:strip)`** (RH, (K1), (K2); Step 3). For `Re L(s) ≤ 3/2` this is the definition of `Fmero`. For
`3/2 < Re L(s) < 2`: `Fmero = Iplus + k(1,s)Q(L(s)-1)`, and `Ilog_step_sub_one` with `c = cPlus A s < Re L(s) - 1`
and `c' = cMinus A s = Re L(s)/2 ∈ (Re L(s) - 1, 1)` gives `Iplus = Iminus + k(L(s)-1,s)Q(L(s)-1)`; add, and
`k(1,s) + k(L(s)-1,s) = 𝔟(s)`. -/
theorem Fmero_eq_strip (hRH : RiemannHypothesis) (A : Aff) (k : ℂ → ℂ → ℂ) (W : ℂ → ℕ → ℕ → ℂ)
    (hK1 : K1 A k) (hK2 : K2 A k) {s : ℂ} (hs : s ∈ stripL A) :
    Fmero A k W s = Iminus A k s + bracket A k s * Qcont (A.app s - 1) := by
  obtain ⟨h1, h2⟩ := hs
  have hn2 : ¬ 2 < (A.app s).re := not_lt.mpr h2.le
  by_cases h3 : 3 / 2 < (A.app s).re
  · have hF : Fmero A k W s = Iplus A k s + k 1 s * Qcont (A.app s - 1) := by
      simp [Fmero, hn2, h3]
    have ha1 : 1 / 2 < cPlus A s := FillC1.half_lt_cPlus A h3
    have ha3 : cPlus A s ≤ ((A.app s).re - 1 / 2) / 2 := FillC1.cPlus_le_right A s
    have hstep := Ilog_step_sub_one hRH A k hK1 hK2 (stripL_subset_DL A ⟨h1, h2⟩) (c := cPlus A s)
      (c' := cMinus A s) ha1 (by linarith) (by unfold cMinus; linarith) (by unfold cMinus; linarith)
      (by unfold cMinus; linarith)
    rw [hF]
    unfold Iplus Iminus
    rw [hstep]
    simp only [bracket]
    ring
  · simp [Fmero, hn2, h3]

end GoldbachBoundaries.Paper2.M4b
