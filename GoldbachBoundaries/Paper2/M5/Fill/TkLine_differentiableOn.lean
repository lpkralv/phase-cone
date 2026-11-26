import GoldbachBoundaries.Paper2.M5.Fill.T2Common

/-!
# Fill: `TkLine_differentiableOn`

`T2.differentiableOn` (`Fill/T2Common.lean`): M1's `differentiableOn_verticalIntegral'` on
`U = {c + 1/2 < σ, σ - c ≠ 1}`, with joint holomorphy of the integrand on the line (`F` analytic off `m`, `Qcont`
analytic off `1` under RH, `Γ` on positive real parts) and domination by `T2.norm_far` far out and by continuity on
`K × [-Y, Y]`.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2

theorem TkLine_differentiableOn (hRH : RiemannHypothesis) {m : ℕ} (hm : 1 ≤ m) {F H : ℂ → ℂ} (hP : TkPack m F H) {c : ℝ}
    (hc : (m : ℝ) - 1 / 2 < c) (hcm : c ≠ m) :
    DifferentiableOn ℂ (TkLine F c) {s | c + 1 / 2 < s.re ∧ s.re - c ≠ 1} ∧
      ∀ s : ℂ, c + 1 / 2 < s.re → s.re - c ≠ 1 →
        Integrable (fun y : ℝ => KerS s (c + y * I) * F (c + y * I) * Qcont (s - (c + y * I))) :=
  T2.differentiableOn hRH hm hP hc hcm

end GoldbachBoundaries.Paper2.M5
