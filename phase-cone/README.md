# Phase cones for Gamma-weighted atoms of additive Dirichlet series

Paper: Hexagon (link forthcoming) · Zenodo (link forthcoming)

The paper gives conditions for Gamma-weighted sums to converge absolutely and be nonzero. The main theorem allows polynomial growth of the coefficient mass in unit height bins.

## Formalized results

Project declaration names have the prefix `GoldbachBoundaries.` This README omits shared Lean and Mathlib vocabulary such as `Complex.Gamma`, `MeromorphicOn` and `Set.Icc`.

| Paper result | Lean declaration | Source file |
| --- | --- | --- |
| Theorem 3.1, sector cone with polynomial bins | `PhaseCone.sum_bKer_ne_zero_sector_poly` | [SectorPoly.lean](../GoldbachBoundaries/PhaseCone/SectorPoly.lean) |
| Corollary 3.2, squared-logarithm bins | `PhaseCone.sum_bKer_ne_zero_sector_of_poly` | [SectorPoly.lean](../GoldbachBoundaries/PhaseCone/SectorPoly.lean) |
| Lemma 3.3, integer weights | `Phi2HInf.sum_bKer_ne_zero_hinf` | [sum_bKer_ne_zero_hinf.lean](../GoldbachBoundaries/Phi2HInf/Fill/sum_bKer_ne_zero_hinf.lean) |
| Lemma 3.3, sector proof | `PhaseCone.sum_bKer_ne_zero_hinf_of_sector`, using `PhaseCone.sum_bKer_ne_zero_sector` | [Sector.lean](../GoldbachBoundaries/PhaseCone/Sector.lean) |
| Section 5, boundary lemma for adding a meromorphic term | `Phi2Proof.isNaturalBoundary_of_eventuallyEq_add` | [M5Boundary.lean](../GoldbachBoundaries/Phi2/Proof/M5Boundary.lean) |

## Definitions and premises

- Stirling on strips (`Phi2HInf.StirlingStrip`) gives a uniform relative error of order `1 / |Im z|` for the leading Stirling approximation to `Γ(z)` on each fixed vertical strip at large absolute height. [Defs.lean](../GoldbachBoundaries/Phi2HInf/Defs.lean)
- `Phi2HInf.bKerH b c τ u` is the Gamma product `Γ(b + i(u + τ)) Γ(c − iu)`. [Proof/Defs.lean](../GoldbachBoundaries/Phi2HInf/Proof/Defs.lean)
- `NoMeromorphicExtensionAt F U z₀` rules out a meromorphic function on any disc centred at `z₀` that agrees with `F` on the overlap with `U` off a relatively closed discrete set there. `IsNaturalBoundary F U L` requires this at every point of `L`. [Defs.lean](../GoldbachBoundaries/Defs.lean)

This premise summary describes the results in prose. The paper's appendix gives the exact hypotheses of each declaration.

The sector results assume Stirling on strips and fix a strip `[1 − B, B]` with `1/2 ≤ B < 1` for both real parts. Their sum must be constant across the family. The ordinate sum satisfies `|τ| ≤ Y` for a fixed `Y > 0`. The heights attain a minimum `u₀` at or above a threshold uniform in that window, and a coefficient at that minimum has modulus at least a fixed `a > 0`. All coefficients lie in a common sector of half-angle `0 ≤ δ < π(1 − B)`. Every unit height bin is finite, and bins with nonnegative lower endpoint satisfy the stated polynomial or squared-logarithm bound on coefficient mass. The integer-weight lemma uses nonnegative integer coefficients and squared-logarithm bins. Positivity at the minimum supplies `a = 1`, and the coefficients have sector half-angle zero.

## Scope

The endpoint sharpness argument, the cancellation and least-height coefficient examples, the comparison of `T` and `Φ₂`, and the question on Liouville weights lie outside the formal statements. The private lemma `Phi2Proof.norm_Gamma_half_sq` proves the pointwise Gamma identity used in the examples. [norm_bKer.lean](../GoldbachBoundaries/Phi2/Fill/norm_bKer.lean)

[Check.lean](Check.lean) prints the axiom dependencies of the theorems in the map.
