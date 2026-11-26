import GoldbachBoundaries.Paper2.M4a.Fill.DCommon

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M4a

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/- Filler for `integral_kernelt_le` (`Kernel.lean`): the integrand is at most
`(1 + |t|)^{2B}(φ(y) + φ(y - t) + 1_{[0,t]}(y))` with `φ(u) = (1 + |u|)^{2B}e^{-π|u|}` integrable. -/
/-- **The integral bound of `cl:lem:kernelt`** (no hypothesis). Let `S` be the segment between `0` and `t`. On `S`,
`|y| + |t - y| = |t|` and `(1 + |y|)(1 + |t - y|) ≤ (1 + |t|)²`, and `S` has length `|t|`, so that part is
`≤ (1 + |t|)^{2B+1}`. At distance `u > 0` from `S`, `|y| + |t - y| - |t| = 2u` and
`(1 + |y|)(1 + |t - y|) ≤ (1 + |t|)²(1 + u)²`; the two rays contribute `≤ 2(1 + |t|)^{2B}∫_0^∞(1 + u)^{2B}e^{-πu}du`.
Integrability: the integrand is continuous and dominated by `(1 + |t|)^{2B}(1 + d(y, S))^{2B}e^{-π d(y, S)}`, which is
integrable. Take `C = 1 + 2∫_0^∞(1 + u)^{2B}e^{-πu}du`. A filler may use the symmetry `y ↦ t - y` and split at `0` and
`t` with `intervalIntegral`/`integral_Ioi` pieces. Size: 150–300 lines. -/
theorem integral_kernelt_le :
    ∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, ∀ t : ℝ,
      Integrable (fun y : ℝ => (1 + |y|) ^ B * (1 + |t - y|) ^ B *
        Real.exp (-(Real.pi / 2 * (|y| + |t - y| - |t|)))) ∧
      ∫ y : ℝ, (1 + |y|) ^ B * (1 + |t - y|) ^ B * Real.exp (-(Real.pi / 2 * (|y| + |t - y| - |t|))) ≤
        C * (1 + |t|) ^ (2 * B + 1) :=
  fun _ hB => FillD.integral_kernelt_le' hB

end GoldbachBoundaries.Paper2.M4a
