import GoldbachBoundaries.Paper2.M5.Fill.F1Common

/-! # Filler F1: `FilLine_eq_of_le` (statement verbatim from `Paper2/M5/FilterI.lean`; proof in `F1Common.lean`) -/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

theorem FilLine_eq_of_le (hRH : RiemannHypothesis) (H : MvPolynomial (Fin 2) ℂ) {s : ℂ} {c c' : ℝ}
    (hc : 1 / 2 < c) (hcc' : c ≤ c') (hc' : c' + 1 / 2 < s.re) : FilLine H c' s = FilLine H c s :=
  F1_FilLine_eq_of_le hRH H hc hcc' hc'

end GoldbachBoundaries.Paper2.M5
