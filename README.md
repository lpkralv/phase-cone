# Lean formalizations for phase cones and Goldbach series

This Lean 4 project accompanies three papers by Louis P. Slothouber on non-cancellation of Gamma-weighted sums and natural boundaries of additive Dirichlet series. The proofs use Lean 4.35.0 and Mathlib at `56a0058`. The classical estimates and zero hypotheses appear as explicit arguments to the theorems that use them.

## Contents

- [Phase cones for Gamma-weighted atoms of additive Dirichlet series](phase-cone/README.md)
- [The natural boundary of the filtered prime-pair Dirichlet series](t0-boundary/README.md)
- [Natural boundaries and real-point limits for class-one Goldbach series](class-one/README.md)

Each paper's README maps its numbered results to the Lean files and summarizes the premises and scope. Each paper's appendix gives the exact hypotheses of its declarations. The [source manifest](MANIFEST.md) lists the local import closure for each paper.

The declaration lists omit shared Lean and Mathlib vocabulary such as `Complex.Gamma`, `MeromorphicOn` and `Tendsto`.

## Release

Repository: https://github.com/lpkralv/phase-cone (release tag `v1.1`; release `v1.0` is the version the papers first cited). One build from a clean clone checks the Lean results of all three papers. The papers are posted on Hexagon and Zenodo:

- Phase cones for Gamma-weighted atoms of additive Dirichlet series: [hexagon:2611.01111](https://hexagonmath.org/2611.01111), doi:[10.5281/zenodo.24550714](https://doi.org/10.5281/zenodo.24550714)
- The natural boundary of the filtered prime-pair Dirichlet series: [hexagon:2611.01112](https://hexagonmath.org/2611.01112), doi:[10.5281/zenodo.24551160](https://doi.org/10.5281/zenodo.24551160)
- Natural boundaries and real-point limits for class-one Goldbach series: [hexagon:2611.01114](https://hexagonmath.org/2611.01114), doi:[10.5281/zenodo.24551268](https://doi.org/10.5281/zenodo.24551268)

## Changes in v1.1

The class-one development now proves the unsubtracted real-point limit and its sign for every integer `r ≥ 2`, assuming RH, Z2 and Z3. It checks the four low zeros and the numerical enclosure of the sign-change threshold in Lean.

## Build and check

Elan reads `lean-toolchain` to select Lean, and Lake uses `lake-manifest.json` for the dependency revisions. Install elan and run the commands below from the repository root. [Elan installation](https://github.com/leanprover/elan)

The dependency is the [zeta project](https://github.com/smmercuri/zeta) by Salvatore Mercuri and Bhavik Mehta, licensed under Apache-2.0, pinned at `4704234df2d97563936adcaf0b89e2f8955389f9`. Our low-zero modules are built on it. Zeta brings Mathlib, the smmercuri fork of PrimeNumberTheoremAnd at `16a8986`, and LeanCert. Cite: Mercuri and Mehta, "Certifying the Riemann hypothesis up to bounded height in Lean", 2026, https://github.com/smmercuri/zeta.

```sh
lake exe cache get
lake build
./scripts/check_axioms.sh
```

The first build compiles the PrimeNumberTheoremAnd fork and zeta's libraries. On 2026-11-27, a clean-clone run of these commands completed with 9959 build jobs and 85 axiom reports, using only `propext`, `Classical.choice` and `Quot.sound`.

Use `import GoldbachBoundaries` to load the complete development. The check files print the axiom dependencies of the public theorems in the corresponding README maps. They omit definitions and private helpers. The check script runs all three files and rejects any axiom outside `propext`, `Classical.choice` and `Quot.sound`. To inspect one paper's output directly, pass its check file to `lake env lean`.

```sh
lake env lean phase-cone/Check.lean
lake env lean t0-boundary/Check.lean
lake env lean class-one/Check.lean
```

The local `GoldbachBoundaries` development has five `sorry` placeholders in `Paper2/Statements.lean`, all outside the cited results. The pinned `PrimeNumberTheoremAnd` dependency also emits two `sorry` warnings from `Wiener.lean` during the build. The axiom checks confirm that none of the checked declarations depends on any of these placeholders. [Local source declarations](GoldbachBoundaries/Paper2/Statements.lean)

## Use of AI

Louis P. Slothouber posed the research questions, directed the investigation and designed the verification process. Anthropic Claude and OpenAI GPT models did much of the mathematical work, reviewed the arguments and wrote the Lean development. Slothouber relies on the Lean kernel and the axiom checks for the formal proofs. No human mathematician has checked the proofs line by line. Slothouber takes responsibility for the work.

## Corrections and licenses

Please report corrections through the Issues tab of this GitHub repository. Include the paper result or Lean declaration when possible.

Copyright 2026 Louis P. Slothouber. The Lean code, scripts and build files use the Apache License 2.0. [LICENSE](LICENSE)

The papers and repository documentation use Creative Commons Attribution 4.0 International. [LICENSE-docs](LICENSE-docs)
