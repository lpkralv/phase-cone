import GoldbachBoundaries.Paper2.M5.Fill.F1Common

/-! # Filler F1: `differentiableOn_Fil` (statement verbatim from `Paper2/M5/FilterI.lean`; proof in `F1Common.lean`) -/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

theorem differentiableOn_Fil (hRH : RiemannHypothesis) (H : MvPolynomial (Fin 2) ℂ) :
    DifferentiableOn ℂ (Fil H) HH :=
  F1_differentiableOn_Fil hRH H

end GoldbachBoundaries.Paper2.M5
