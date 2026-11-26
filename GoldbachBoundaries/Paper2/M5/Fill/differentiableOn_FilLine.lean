import GoldbachBoundaries.Paper2.M5.Fill.F1Common

/-! # Filler F1: `differentiableOn_FilLine` (statement verbatim from `Paper2/M5/FilterI.lean`; proof in `F1Common.lean`) -/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

theorem differentiableOn_FilLine (hRH : RiemannHypothesis) (H : MvPolynomial (Fin 2) ℂ) {c : ℝ}
    (hc : 1 / 2 < c) :
    DifferentiableOn ℂ (FilLine H c) {s | c + 1 / 2 < s.re} ∧
      ∀ s : ℂ, c + 1 / 2 < s.re → Integrable (fun y : ℝ => gA H s (c + y * I)) :=
  F1_differentiableOn_FilLine hRH H hc

end GoldbachBoundaries.Paper2.M5
