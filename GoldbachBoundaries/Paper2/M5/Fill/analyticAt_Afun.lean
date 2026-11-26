import GoldbachBoundaries.Paper2.M5.Fill.F1Common

/-! # Filler F1: `analyticAt_Afun` (statement verbatim from `Paper2/M5/FilterI.lean`; proof in `F1Common.lean`) -/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

theorem analyticAt_Afun (hRH : RiemannHypothesis) {z : ℂ} (hz : 1 / 2 < z.re) : AnalyticAt ℂ Afun z :=
  F1_analyticAt_Afun hRH hz

end GoldbachBoundaries.Paper2.M5
