# The natural boundary of the filtered prime-pair Dirichlet series

Paper: Hexagon (link forthcoming) · Zenodo (link forthcoming)

Under H∞ and the stated classical inputs, the filtered series `T₀` has a meromorphic continuation to `Re s > 1` that agrees pointwise with the defining series on `Re s > 2`. Every meromorphic function on `Re s > 1` that agrees with `T₀` on `Re s > 2` in the codiscrete sense has natural boundary `Re s = 1`.

## Formalized results

Project declaration names have the prefix `GoldbachBoundaries.` This README omits shared Lean and Mathlib vocabulary such as `Complex.Gamma`, `MeromorphicOn` and `EqOn`. Theorem 4.1 restates the polynomial sector theorem from the phase-cone paper.

| Paper result | Lean declaration | Source file |
| --- | --- | --- |
| Lemma 3.1, Mellin square | `T0HInf.t0_mellin_sq` | [PrimeMellin.lean](../GoldbachBoundaries/T0HInf/PrimeMellin.lean) |
| Lemma 3.2, filtered explicit formula | `T0HInf.L_explicit`, `T0HInf.remainder_bound` | [ExplicitFormula.lean](../GoldbachBoundaries/T0HInf/ExplicitFormula.lean) |
| Lemma 3.2, coefficient summability | `T0HInf.summable_norm_zeroCoef` | [ZeroCoefficients.lean](../GoldbachBoundaries/T0HInf/ZeroCoefficients.lean) |
| Proposition 3.3, cutoff | `T0HInf.exists_cutoff` | [Cutoff.lean](../GoldbachBoundaries/T0HInf/Cutoff.lean) |
| Proposition 3.3, correction and continuation | `T0HInf.meromorphicOn_W`, `T0HInf.t0_reg_identity`, `T0HInf.t0_hinf_continuation` | [Regularization.lean](../GoldbachBoundaries/T0HInf/Regularization.lean) |
| Proposition 3.3, ordered pair sum and residues | `T0HInf.meromorphicOn_C`, `T0HInf.hasResidue_C` | [Catalogue.lean](../GoldbachBoundaries/T0HInf/Catalogue.lean) |
| Theorem 4.1, sector cone with polynomial bins | `PhaseCone.sum_bKer_ne_zero_sector_poly` | [SectorPoly.lean](../GoldbachBoundaries/PhaseCone/SectorPoly.lean) |
| Corollary 4.2(a), full collision atoms | `T0HInf.collisionAtom_ne_zero_of_large_of_sector` | [SectorBridge.lean](../GoldbachBoundaries/T0HInf/SectorBridge.lean) |
| Corollary 4.2(b), critical-line atoms | `T0HInf.criticalAtom_ne_zero_of_large_of_sector` | [SectorBridge.lean](../GoldbachBoundaries/T0HInf/SectorBridge.lean) |
| Corollary 4.2, shared pair-family lemma | `T0HInf.pair_family_ne_zero_of_large_of_sector` | [SectorBridge.lean](../GoldbachBoundaries/T0HInf/SectorBridge.lean) |
| Theorem 5.1, filtered prime pairs | `T0HInf.t0_hinf_natural_boundary_of_sector` | [SectorBoundary.lean](../GoldbachBoundaries/T0HInf/SectorBoundary.lean) |
| Theorem 5.1, normal limit of the critical-line pair sum | `T0HInf.tendsto_eta_criticalC` | [CriticalCatalogue.lean](../GoldbachBoundaries/T0HInf/CriticalCatalogue.lean) |

## Definitions and premises

- `Paper2.T0` is the filtered prime-pair Dirichlet series on its half-plane of absolute convergence, `Re s > 2`. [Paper2/Defs.lean](../GoldbachBoundaries/Paper2/Defs.lean)
- `T0HInf.remainderAbscissa`, `T0HInf.cutoffAbscissa` and `T0HInf.crossingAbscissa` are the abscissae `a`, `b` and `c_*` in the explicit formula and cutoff construction. `T0HInf.IsCutoff E` says that the finite set `E` contains exactly the nontrivial zeta zeros with real part greater than `b`. `T0HInf.T0c` is the continuation obtained by dividing the pair sum plus its correction by `Γ(s)`. [T0HInf/Defs.lean](../GoldbachBoundaries/T0HInf/Defs.lean)
- `halfPlane a` is `{s : Re s > a}`, `HH` is `halfPlane 1`, and `lineOne` is `{s : Re s = 1}`. `IsNaturalBoundary F U L` rules out meromorphic extension across each point of `L`, using codiscrete agreement with `F` on the overlap with `U`. [Defs.lean](../GoldbachBoundaries/Defs.lean)
- H∞ (`Paper2.Hinf`) says that for each `δ > 0`, finitely many nontrivial zeta zeros satisfy `Re ρ > 1/2 + δ`.
- Z1 (`Paper2.Z1`) states that conjugation and `ρ ↦ 1 − conj ρ` preserve the nontrivial zeta zeros and their multiplicities.
- Z2 (`Paper2.Z2`) gives the Riemann–von Mangoldt count with logarithmic error and a logarithmic bound on multiplicity in unit height intervals.
- Z3 (`Paper2.Z3`) gives a local expansion of `ζ′/ζ` in terms of zeros within one unit of the height, with a uniform logarithmic error for `−1 ≤ Re z ≤ 2` and `|Im z| ≥ 2`, away from zeros.
- Littlewood's gap estimate (`Paper2.ZLittlewood`) places a zeta-zero ordinate within `O(1 / log log log t)` of each sufficiently large positive height `t`.
- Stirling on strips (`Phi2HInf.StirlingStrip`) gives a uniform relative error of order `1 / |Im z|` in the leading Gamma approximation on every fixed vertical strip at large absolute height.

This premise summary describes the results in prose. The paper's appendix gives the exact hypotheses of each declaration.

- The Mellin-square identity holds on `Re s > 2` with no classical zeta or Gamma premises. The explicit-formula identity is definitional. Coefficient summability takes Z1 and Z2. The remainder bound takes H∞, Z1–Z3 and Stirling on strips.
- Cutoff existence takes H∞. The pair sum and its interior residue take H∞, Z1 and Z2. The correction and continuation take H∞, Z1–Z3, Stirling on strips and a finite set `E` satisfying `T0HInf.IsCutoff E`.
- The polynomial sector theorem takes Stirling on strips and the same strip, height, sector and bin conditions as in the phase-cone paper. The two filtered-atom results take Z1, Z2 and Stirling. Both fix an ordinate window `|Im s₀| ≤ Y` with `Y > 0` and require a nonempty pair family with both ordinates of every pair larger than a uniform threshold `X > Y` in absolute value. The full collision-atom result also takes H∞.
- The boundary theorem takes H∞, Z1–Z3, Littlewood's gap estimate and Stirling. The critical-line pair-sum limit `T0HInf.tendsto_eta_criticalC` takes Z1 and Z2. Finiteness of the off-line zeros is a condition in the boundary argument that applies this limit.

## Scope

The comparison with the earlier arguments for `T` and `Φ₂` and the discussion of deriving H∞ from RH are expository.

[Check.lean](Check.lean) prints the axiom dependencies of the theorems in the map.
