import GoldbachBoundaries.Paper2.M4a.Kernel
import GoldbachBoundaries.Paper2.M4a.Fill.analyticOnNhd_lineCoeff
import GoldbachBoundaries.Paper2.M4a.Fill.eq_div_of_continuousAt
import GoldbachBoundaries.Paper2.M4a.Fill.exists_lineCoeff_ne_zero
import GoldbachBoundaries.Paper2.M4a.Fill.isMeromorphic₂_restrict_line

/-!
# M4a: restricting a meromorphic function of two variables to a complex line ((K4))

`IsMeromorphic₂ k`: near every `p ∈ ℂ²`, on a polydisc, `k = u/v` with `u, v` holomorphic and `v ≢ 0`, and nothing is
asked of `k` where `v = 0`. The paper's remark after `cl:thm:class` restricts `k` to the lines `{(1, s)}` and
`{(L(s) - 1, s)}` ("locally `k = u/v` with `v` not identically zero on the line"). That parenthesis is not automatic:
`v` may vanish identically on the line (local quotients need not be coprime), and then `u/v` says nothing about `k` on
the line. The fix here avoids coprimality: expand `v(·, s)` and `u(·, s)` in the transverse variable `z` about the point
`c₀ + c₁s` of the line. The coefficients `a_j(s)`, `b_j(s)` (`lineCoeff`) are holomorphic in `s`; let `m` be the least
`j` with `a_j ≢ 0` on the disc. Where `a_m(s) ≠ 0`, `v(·, s)` has order exactly `m` at the line, and if `z ↦ k(z, s)`
is continuous there (which (K1) gives on `D_L`), then `k = b_m(s)/a_m(s)` on the line. So `b_m/a_m` is the meromorphic
restriction, valid off the isolated zeros of `a_m`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M4a

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-! ## Lemmas

Proved in `Fill/`, one file per lemma (same name, same statement): `analyticOnNhd_lineCoeff`, `eq_div_of_continuousAt`, `exists_lineCoeff_ne_zero`, `isMeromorphic₂_restrict_line`. -/

end GoldbachBoundaries.Paper2.M4a
