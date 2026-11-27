# Natural boundaries and real-point limits for class-one Goldbach series

Paper: Hexagon (link forthcoming) · Zenodo (link forthcoming)

The class-one Goldbach series use von Mangoldt weights and restrict each integer in the sum to `1 mod q`. For `q ≥ 2` and `r ≥ 2`, GRH at modulus `q` and the stated classical estimates give a meromorphic continuation to `Re s > r − 1` that agrees pointwise with the defining series on `Re s > r`. Every meromorphic function on `Re s > r − 1` that agrees with the series on `Re s > r` in the codiscrete sense has natural boundary `Re s = r − 1`.

At the real point, the paper subtracts an explicit main term `M` and gives a positive limit for `η(Φᶜ − M)(r − 1 + η)` as `η` decreases to zero. For the unrestricted series it gives regularized limits at every ordinate under RH and the stated zeta estimates.

## Formalized results

Project declaration names have the prefix `GoldbachBoundaries.` This README omits shared Lean and Mathlib vocabulary such as `Complex.Gamma`, `MeromorphicOn` and `Tendsto`. The sector results in Section 2 are restated from the phase-cone paper.

| Paper result | Lean declaration | Source file |
| --- | --- | --- |
| Theorem 2.1, sector cone with polynomial bins | `PhaseCone.sum_bKer_ne_zero_sector_poly` | [SectorPoly.lean](../GoldbachBoundaries/PhaseCone/SectorPoly.lean) |
| Corollary 2.2, squared-logarithm bins | `PhaseCone.sum_bKer_ne_zero_sector_of_poly` | [SectorPoly.lean](../GoldbachBoundaries/PhaseCone/SectorPoly.lean) |
| Lemma 2.3, integer weights | `Phi2HInf.sum_bKer_ne_zero_hinf` | [sum_bKer_ne_zero_hinf.lean](../GoldbachBoundaries/Phi2HInf/Fill/sum_bKer_ne_zero_hinf.lean) |
| Lemma 2.3, sector proof | `PhaseCone.sum_bKer_ne_zero_hinf_of_sector`, using `PhaseCone.sum_bKer_ne_zero_sector` | [Sector.lean](../GoldbachBoundaries/PhaseCone/Sector.lean) |
| Companion paper, boundary lemma for adding a meromorphic term | `Phi2Proof.isNaturalBoundary_of_eventuallyEq_add` | [M5Boundary.lean](../GoldbachBoundaries/Phi2/Proof/M5Boundary.lean) |
| Lemma 3.1, character average and zero orders | `ResidueClass.D_eq_primitive_average`, `ResidueClass.analyticOrderNatAt_lFunction_eq_primitiveMult` | [EulerFactors.lean](../GoldbachBoundaries/ResidueClass/EulerFactors.lean) |
| Lemma 3.1, Dirichlet series | `ResidueClass.D_eq_lSeries` | [Series.lean](../GoldbachBoundaries/ResidueClass/Series.lean) |
| Lemma 3.1, meromorphy, nonvanishing and poles | `ResidueClass.meromorphic_D`, `ResidueClass.analyticAt_D`, `ResidueClass.primitiveL_ne_zero_of_one_le_re`, `ResidueClass.hasResidue_D_one`, `ResidueClass.hasResidue_D`, `ResidueClass.meromorphicOrderAt_D_one`, `ResidueClass.meromorphicOrderAt_D_of_pos_mult` | [Zeros.lean](../GoldbachBoundaries/ResidueClass/Zeros.lean) |
| Lemma 3.2, zero counts | `ResidueClass.exists_ordinate_window_mass_bound` | [JensenCount.lean](../GoldbachBoundaries/ResidueClass/JensenCount.lean) |
| Lemma 3.2, weights | `ResidueClass.summable_norm_gammaWeight` | [GammaWeights.lean](../GoldbachBoundaries/ResidueClass/GammaWeights.lean) |
| Lemma 3.2, heat expansion and remainder | `ResidueClass.smoothed_explicit_formula`, `ResidueClass.norm_lineRemainder_le` | [ContourShift.lean](../GoldbachBoundaries/ResidueClass/ContourShift.lean) |
| Proposition 3.3, binary decomposition and continuation | `ResidueClass.Gamma_mul_Phi2_eq`, `ResidueClass.differentiableOn_holomorphicCorrection`, `ResidueClass.meromorphicOn_phi2Continuation`, `ResidueClass.eqOn_phi2Continuation` | [BinaryContinuation.lean](../GoldbachBoundaries/ResidueClass/BinaryContinuation.lean) |
| Proposition 3.3, meromorphy of the correction `W` | `ResidueClass.meromorphic_W` | [Correction.lean](../GoldbachBoundaries/ResidueClass/Correction.lean) |
| Lemma 3.4, binary normal limit of the pair sum | `ResidueClass.tendsto_radial_cauchySquare` | [RadialLimit.lean](../GoldbachBoundaries/ResidueClass/RadialLimit.lean) |
| Lemma 3.4, regularized limits | `ResidueClass.tendsto_radial_regularPart`, `ResidueClass.tendsto_radial_phi2Continuation` | [BinaryBoundary.lean](../GoldbachBoundaries/ResidueClass/BinaryBoundary.lean) |
| Lemma 3.5, nonzero atoms | `ResidueClass.exists_pairResidue_ne_zero` | [WeightedCone.lean](../GoldbachBoundaries/ResidueClass/WeightedCone.lean) |
| Lemma 3.5, density | `ResidueClass.exists_nearby_pairResidue_ne_zero` | [BoundaryDensity.lean](../GoldbachBoundaries/ResidueClass/BoundaryDensity.lean) |
| Lemma 3.5, finite pole exclusions | `ResidueClass.finite_W_poles_line_Icc` | [PoleWindows.lean](../GoldbachBoundaries/ResidueClass/PoleWindows.lean) |
| Theorem 3.6, binary class-one boundary | `ResidueClass.phi2_natural_boundary` | [Statement.lean](../GoldbachBoundaries/ResidueClass/Statement.lean) |
| Theorem 3.6, boundary lemmas | `ResidueClass.isNaturalBoundary_regularPart`, `ResidueClass.isNaturalBoundary_phi2_of_agrees` | [BinaryBoundary.lean](../GoldbachBoundaries/ResidueClass/BinaryBoundary.lean) |
| Proposition 3.7, higher-fold reduction | `ResidueClass.Gamma_mul_PhiR_eq`, `ResidueClass.meromorphicOn_phiRContinuation`, `ResidueClass.eqOn_phiRContinuation` | [HigherReduction.lean](../GoldbachBoundaries/ResidueClass/HigherReduction.lean) |
| Theorem 3.8, higher-fold class-one boundary | `ResidueClass.phiR_natural_boundary` | [Statement.lean](../GoldbachBoundaries/ResidueClass/Statement.lean) |
| Theorem 3.8, boundary lemma | `ResidueClass.isNaturalBoundary_phiR_of_agrees` | [HigherReduction.lean](../GoldbachBoundaries/ResidueClass/HigherReduction.lean) |
| Theorem 4.1, positive class-one real limit | `ResidueClass.phiR_sub_main_real_limit` | [ResidueClass/RealPoint.lean](../GoldbachBoundaries/ResidueClass/RealPoint.lean) |
| Proposition 4.2, unrestricted normal limit | `PhiRProof.phiR_sub_main_radial_limit`, with `PhiRProof.PhiRc_sub_phiRMain` | [PhiR/RealPoint.lean](../GoldbachBoundaries/PhiR/RealPoint.lean) |
| Corollary 4.3, positive unrestricted real limit | `PhiRProof.phiR_sub_main_real_limit` | [PhiR/RealPoint.lean](../GoldbachBoundaries/PhiR/RealPoint.lean) |


| Primitive local expansion, nonzero `q` and GRH at `q` or finitely many off-line zeros, respectively | `ResidueClass.logDerivPrimitiveLocal_of_GRH`, `ResidueClass.logDerivPrimitiveLocal_of_finite_exceptions` | [PrimitiveLocalProof.lean](../GoldbachBoundaries/ResidueClass/PrimitiveLocalProof.lean) |
| Binary and higher-fold boundaries, `q ≥ 2`, GRH, Z3, Littlewood and Stirling; also `r ≥ 2` for higher-fold | `ResidueClass.phi2_natural_boundary_of_proved`, `ResidueClass.phiR_natural_boundary_of_proved` | [LocalProved.lean](../GoldbachBoundaries/ResidueClass/LocalProved.lean) |
| Positive class-one real limit, `q,r ≥ 2`, GRH and Z3 | `ResidueClass.phiR_sub_main_real_limit_of_proved` | [LocalProved.lean](../GoldbachBoundaries/ResidueClass/LocalProved.lean) |
| Binary boundary, `q ≥ 2`, finitely many off-line zeros, Z3, Littlewood and Stirling | `ResidueClass.phi2_natural_boundary_finite_exceptions` | [ExceptionalBinary.lean](../GoldbachBoundaries/ResidueClass/ExceptionalBinary.lean) |
| Higher-fold boundary, `q,r ≥ 2`, finitely many off-line zeros, Z3, Littlewood and Stirling | `ResidueClass.phiR_natural_boundary_finite_exceptions` | [ExceptionalHigher.lean](../GoldbachBoundaries/ResidueClass/ExceptionalHigher.lean) |
| Boundary at `q = 2` by Euler deletion, `r ≥ 2`, RH, Z2, Z3 and Littlewood | `ResidueClass.phiR_two_natural_boundary_of_unrestricted` | [TwoBoundary.lean](../GoldbachBoundaries/ResidueClass/TwoBoundary.lean) |
| Euler deletion remainder extends analytically, `r ≥ 2` and RH; GRH at 2 is equivalent to RH without premises | `ResidueClass.phiRc_sub_phiRTwoContinuation_extends`, `ResidueClass.grh_two_iff_riemannHypothesis` | [TwoBoundary.lean](../GoldbachBoundaries/ResidueClass/TwoBoundary.lean) |

| Unsubtracted real-point limit, RH, Z2, Z3 and `r ≥ 2` | `PhiRProof.phiR_real_limit` | [UnsubtractedRealLimit.lean](../GoldbachBoundaries/PhiR/UnsubtractedRealLimit.lean) |
| Zero sum and positivity, RH and Z2 for positivity | `PhiRProof.muZero`, `PhiRProof.muZero_pos` | [UnsubtractedRealLimit.lean](../GoldbachBoundaries/PhiR/UnsubtractedRealLimit.lean) |
| Conditional bound and negative limit, H14 and HN; RH, Z2, Z3 and `2 ≤ r ≤ 4 × 10^15` for the limit | `PhiRProof.muZero_lt`, `PhiRProof.phiR_real_limit_neg`, `PhiRProof.phiR_tendsto_negative_real` | [UnsubtractedSign.lean](../GoldbachBoundaries/PhiR/UnsubtractedSign.lean) |
| Four low zeros through height 32, unconditional | `PhiRProof.ReleaseLowZeros`, `PhiRProof.releaseLowZeros_proved` | [LowZerosSpec.lean](../GoldbachBoundaries/PhiR/LowZerosSpec.lean), [ReleaseBridge.lean](../GoldbachBoundaries/LowZeros/ReleaseBridge.lean) |
| Conditional threshold gap and nonzero limit, RH, Z2, `ReleaseLowZeros` and HN; Z3 and `r ≥ 2` for the limit | `PhiRProof.rStar_gap`, `PhiRProof.phiR_real_limit_ne_zero` | [UnsubtractedGap.lean](../GoldbachBoundaries/PhiR/UnsubtractedGap.lean) |
| D0 identity, RH | `PhiRProof.d0_identity` | [D0Tail.lean](../GoldbachBoundaries/PhiR/D0Tail.lean) |
| Threshold gap, RH, Z2 and `ReleaseLowZeros` | `PhiRProof.rStar_gap_RH` | [D0Tail.lean](../GoldbachBoundaries/PhiR/D0Tail.lean) |
| Unsubtracted limit exists and is nonzero, RH, Z2, Z3 and `r ≥ 2` | `PhiRProof.phiR_tendsto_ne_zero` | [UnsubtractedFinal.lean](../GoldbachBoundaries/PhiR/UnsubtractedFinal.lean) |

## Definitions and premises

- `ResidueClass.Phi2 q` and `ResidueClass.PhiR q r` are the binary and `r`-fold class-one Goldbach series. [Definitions.lean](../GoldbachBoundaries/ResidueClass/Definitions.lean)
- `ResidueClass.phiRContinuation q r` is the continuation constructed by the higher-fold reduction. [HigherReduction.lean](../GoldbachBoundaries/ResidueClass/HigherReduction.lean)
- `ResidueClass.phiRMain q r` is the main term subtracted for the class-one real limit. `ResidueClass.phiRMainTail q r` is the entire tail term included in its Gamma normalization. [ResidueClass/RealPoint.lean](../GoldbachBoundaries/ResidueClass/RealPoint.lean)
- `PhiRProof.phiRMain r` is the main term subtracted for the unrestricted limits. [PhiR/RealPoint.lean](../GoldbachBoundaries/PhiR/RealPoint.lean)
- `ResidueClass.Ordinates q` is the set of critical-line ordinates `I` with positive total multiplicity. `ResidueClass.ordinateWeight q t` is the total multiplicity `P₁(t)` across inducing primitive functions, counted for each character. `ResidueClass.criticalPoint t` is `1/2 + it`. [Zeros.lean](../GoldbachBoundaries/ResidueClass/Zeros.lean)
- `halfPlane a` is `{s : Re s > a}`, and `HH` is `halfPlane 1`. `lineAt a` is `{s : Re s = a}`, with `lineOne` the line at 1. `IsNaturalBoundary F U L` rules out meromorphic extension across each point of `L`, using codiscrete agreement with `F` on the overlap with `U`. [Defs.lean](../GoldbachBoundaries/Defs.lean) [PhiR/Defs.lean](../GoldbachBoundaries/PhiR/Defs.lean)
- GRH at modulus `q` (`ResidueClass.GRH q`) places all zeros in the open critical strip of the inducing primitive functions, including ζ, on `Re z = 1/2`.
- `ResidueClass.OffLineZeros q` contains the distinct off-line strip zeros of the inducing primitive functions, including zeta zeros and real zeros. [ExceptionalZeros.lean](../GoldbachBoundaries/ResidueClass/ExceptionalZeros.lean)
- RH (`RiemannHypothesis` in Mathlib) places every nontrivial zeta zero on `Re z = 1/2`.
- Z2 (`Paper2.Z2`) gives the Riemann–von Mangoldt count with logarithmic error and a logarithmic bound on multiplicity in unit height intervals.
- Z3 (`Paper2.Z3`) gives a local expansion of `ζ′/ζ` in terms of zeros within one unit of the height, with a uniform logarithmic error for `−1 ≤ Re z ≤ 2` and `|Im z| ≥ 2`, away from zeros.
- H14 (`PhiRProof.H14`) places every nontrivial zeta zero at absolute ordinate greater than 14. HN (`PhiRProof.HN`) bounds the zero count by `T² / 8` for `T ≥ 14`.
- `ResidueClass.LogDerivPrimitiveLocal q`, proved under GRH or finite off-line zeros, gives a local expansion of `L′/L` in terms of strip zeros within one unit of the height. For `0 < Re z ≤ 2` and sufficiently large `|Im z|`, away from zeros, the logarithmic error is uniform over the primitive functions inducing nonprincipal characters modulo `q`.
- Littlewood's gap estimate (`Paper2.ZLittlewood`) places a zeta-zero ordinate within `O(1 / log log log t)` of each sufficiently large positive height `t`.
- Stirling on strips (`Phi2HInf.StirlingStrip`) gives a uniform relative error of order `1 / |Im z|` in the leading Gamma approximation on every fixed vertical strip at large absolute height.

This premise summary describes the results in prose. The paper's appendix gives the exact hypotheses of each declaration.

- The restated cone results take Stirling on strips and the stated polynomial-bin, squared-logarithm-bin or integer-weight hypotheses.
- The class-one declarations fix a nonzero modulus.
- The pointwise character average is stated for `Re z > 0`, `z ≠ 1` and no vanishing inducing primitive function at `z`. GRH is used to locate the strip poles.
- The zero count and weight summability use GRH. The heat expansion also takes Z3, the primitive local expansion, `0 < d < 1/2` and `x > 0`. The standalone remainder bound requires `x > 0` and has no zero hypotheses.
- The binary decomposition, corrected binary normal limits and higher-fold reduction take GRH, Z3 and the primitive local expansion. The holomorphic correction also takes `0 < d < 1/2`. The uncorrected binary pair-sum limit uses GRH. The higher-fold reduction is stated for `q,r ≥ 2` in the paper.
- The nonzero-atom result uses GRH and Stirling. Density also takes Littlewood's gap estimate. Excluding finitely many poles requires no zero hypothesis.
- The original class-one boundary declarations take `q ≥ 2`, GRH, Z3, the primitive local expansion, Littlewood and Stirling; the `_of_proved` wrappers derive the primitive expansion from GRH. The higher-fold versions also take `r ≥ 2`. The original class-one real limit takes `q,r ≥ 2`, GRH, Z3 and the primitive local expansion; its `_of_proved` wrapper derives that expansion from GRH. The unrestricted limits take `r ≥ 2`, RH, Z2 and Z3.

## Scope

The separate deduction at `q = 2` is formalized by Euler deletion. The comparisons with Rüppel's formulas lie outside the formal statements. The paper's numerical enclosure of `r_*` in the section on real-point limits is now checked in Lean; the paper text will be updated in its next revision. The final theorem gives a negative limit for `2 ≤ r ≤ 5639249912025015212` and a positive limit for `r ≥ 5639249912025015213`. The two positive real-point formulas use squared Gamma norms. The unrestricted every-ordinate limit uses a possibly complex atom summed over ordered zero pairs, with products of Gamma values. The private lemma `Phi2Proof.norm_Gamma_half_sq` proves the pointwise Gamma identity used in the hyperbolic-cosine reformulation. [norm_bKer.lean](../GoldbachBoundaries/Phi2/Fill/norm_bKer.lean)

The higher-fold reduction uses the private helpers `ResidueClass.higherRemainder`, `ResidueClass.differentiableOn_higherRemainder`, `ResidueClass.analyticAt_higherCoefficient`, `ResidueClass.higherCoefficient_ne_zero` and `ResidueClass.meromorphicOn_higherCorrection`. [HigherReduction.lean](../GoldbachBoundaries/ResidueClass/HigherReduction.lean)

[Check.lean](Check.lean) prints the axiom dependencies of the declarations listed in that file.
