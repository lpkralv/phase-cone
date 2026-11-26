import GoldbachBoundaries.Phi2.Proof.M3Radial
import GoldbachBoundaries.Phi2.Fill.norm_bKer
import GoldbachBoundaries.Phi2.Fill.norm_bKer_le
import GoldbachBoundaries.Phi2.Fill.bKer_cone
import GoldbachBoundaries.Phi2.Fill.sum_bKer_ne_zero
import GoldbachBoundaries.Phi2.Fill.pairAtom_eq_two_tsum
import GoldbachBoundaries.Phi2.Fill.Aidx_bin_le
import GoldbachBoundaries.Phi2.Fill.pairAtom_neg
import GoldbachBoundaries.Phi2.Fill.pairAtom_ne_zero_of_large

/-!
The analytic core is stated without zeros (`sum_bKer_ne_zero`): any family of heights `u_i ≥ u₀` with positive integer
weights, at most `K log²(v+3)` weight per unit interval, gives a non-zero `∑ q_i b_τ(u_i)` once `u₀` is large. Its
inputs are the modulus of `b_τ` (exact, from `|Γ(1/2 + iv)|² = π/cosh πv`), the decay of the modulus ratio, and the
phase cone over the window `[u₀, u₀ + √u₀]`.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics ComplexConjugate

namespace GoldbachBoundaries.Phi2Proof

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-! ## Lemmas proved in `Fill/`

One file per lemma, same name and statement, proved at the end of its file and imported above: `norm_bKer`, `norm_bKer_le`, `bKer_cone`, `sum_bKer_ne_zero`, `pairAtom_eq_two_tsum`, `Aidx_bin_le`, `pairAtom_neg`, `pairAtom_ne_zero_of_large`. -/

end GoldbachBoundaries.Phi2Proof
