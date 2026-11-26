import GoldbachBoundaries.Paper2.M5.Defs
import GoldbachBoundaries.Paper2.M5.Fill.poleSetQ_re_cases
import GoldbachBoundaries.Paper2.M5.Fill.eqOn_HH_of_eqOn_open
import GoldbachBoundaries.Paper2.M5.Fill.order_residue_add_analyticAt
import GoldbachBoundaries.Paper2.M5.Fill.order_residue_of_codiscrete_line

/-!
# M5: general lemmas shared by Theorems G and F

Four lemmas used by both halves of M5:

* `poleSetQ_re_cases`: under RH the points of `Σ_Q` are `1`, the points on `Re = 1/2` (`1/2` and the zeros), and points
  with `Re ≤ 1/3` (`1/k`, `k ≥ 3`, and `ρ/n`, `n ≥ 2`). This is the bookkeeping behind "the poles of `g_s` in the strip
  `c' ≤ Re z ≤ c` are `1/2` and the zeros" (Theorem F) and "`x₀ + iy ∉ Σ`" (`cl:lem:Qleft`).
* `eqOn_HH_of_eqOn_open`: the identity theorem on `ℍ` (it is how a holomorphic continuation of `D_H` or `T₀` is
  identified with the explicit `Fil`).
* `order_residue_add_analyticAt`: adding a function analytic at `α` changes neither the order (when it is negative)
  nor the residue.
* `order_residue_of_codiscrete_line`: a function meromorphic on a disc about a point `s₀` of `σ = 1`, agreeing off a
  discrete set with a holomorphic `F` on the right half of the disc, has a simple pole at `s₀` with residue `c` when
  `η F(s₀ + η) → c ≠ 0` (the step "so `f` is unbounded near `s₀` and `s₀` is a pole" of Theorem F(iii), and the last
  sentence of (iv)).
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-! ## Lemmas

Proved in `Fill/`, one file per lemma (same name, same statement): `poleSetQ_re_cases`, `eqOn_HH_of_eqOn_open`, `order_residue_add_analyticAt`, `order_residue_of_codiscrete_line`. -/

end GoldbachBoundaries.Paper2.M5
