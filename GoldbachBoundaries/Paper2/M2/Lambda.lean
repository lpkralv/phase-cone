import GoldbachBoundaries.Paper2.M2.Far
import GoldbachBoundaries.Paper2.M2.Fill.SH_finite_ncard_le
import GoldbachBoundaries.Paper2.M2.Fill.eventually_nearBad_small
import GoldbachBoundaries.Paper2.M2.Fill.nearBad_finite_ncard_le
import GoldbachBoundaries.Paper2.M2.Fill.pairSum_conj
import GoldbachBoundaries.Paper2.M2.Fill.pairSum_ne_zero_of_not_nearBad
import GoldbachBoundaries.Paper2.M2.Fill.prop_Lambda_core
import GoldbachBoundaries.Paper2.M2.Fill.prop_Lambda_of_core

/-!
# M2: non-vanishing pair sums at the points `1 + ρ/q` (`nr:prop:Lambda`)

`B < 1`, with (Z1), (Z2), (Z4), (Z5), (Z6). This is the counting core of Theorem B, done once: `thm_boundary_proof`
(`Skeleton.lean`) gets its poles from it through `thm_residue` (M1). The paper proves `nr:thm:boundary` first and then
`nr:prop:Lambda` by "running the same proof with `𝓡(s₀)` in place of `Res_{s₀} T`"; the order is reversed here, which
changes no statement.

For `y > 0`, `0 < ε < min(y, 1)`, `Y = y + 1`, `X` large, `H = 2 log X`: every good pair `(ρ, q) ∈ 𝓟(X)` gives
`u = ρ/q` with `|2R_u/u| ≥ 2/(X + 1) > X⁻² = e^{-H}`. If `u ∉ NearBad H Y`, all competing pairs have `|Im a| > H` and
`lem_far_proof` bounds their total by `e^{-H}`, so `𝓡(1 + u) ≠ 0`. The near-bad `u` are at most `|𝒮_{H+Y}|²`
(`u = a + b - 1` with `a, b ∈ 𝒮_{H+Y}`), which is `O((log X)²(log log X)²)` against the `≫ X²/log² X` good pairs.

**Integrated layout.** The seven lemmas this file stated with `sorry` (`pairSum_conj`, `SH_finite_ncard_le`,
`nearBad_finite_ncard_le`, `pairSum_ne_zero_of_not_nearBad`, `eventually_nearBad_small`, `prop_Lambda_core`,
`prop_Lambda_of_core`) are proved in `Fill/<name>.lean`, statements unchanged, each with its filler's docstring; the
fill files import `Far.lean` (and each other where needed), and this file imports them.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M2

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-! ## Target -/

/-- `prop_Lambda` of `Paper2/Statements.lean`, statement verbatim. -/
theorem prop_Lambda_proof (hZ1 : Z1) (hZ2 : Z2) (hZ4 : Z4) (hZ5 : Z5) (hZ6 : Z6) (hB : Bsup < 1)
    (y ε : ℝ) (hε : 0 < ε) :
    {s₀ : ℂ | ∃ ρ ∈ NontrivialZeros, ρ.re = 1 / 2 ∧ ∃ q : ℕ, q.Prime ∧ s₀ = 1 + ρ / (q : ℂ) ∧
      s₀ ∈ ball (1 + (y : ℂ) * I) ε ∧ pairSum s₀ ≠ 0}.Infinite :=
  prop_Lambda_of_core hZ1
    (fun _ _ hy hε hεy hε1 => prop_Lambda_core hZ1 hZ2 hZ4 hZ5 hZ6 hB hy hε hεy hε1) y ε hε

end GoldbachBoundaries.Paper2.M2
