import GoldbachBoundaries.ThmA.G16_Decomp

/-!
# G18–G19. The local model (`thm:local`) and access across the cuts (`lem:access`)

Four general lemmas about integrals with a logarithmic or Cauchy kernel (`logEnd`, `logInt`,
`cauchyEnd`, `cauchyInt`; upstream candidates), the paper-specific local forms of `N₁` and `𝒟`, and
the two assembly lemmas `Gnat_local`, `Gnat_access`.

In `N₁`, with `s = s₀ + δv` and `x = 1 - uv`, `s - x = a + (δ + u - t₀)v` when
`s₀ - 1 + t₀ v = a ∈ Σ`; after `PsegA_split` the only non-holomorphic term is
`∫ φ(δ,u) Log(δ + u - t₀) du` with `φ(δ,u) = Γ(1-uv)Γ(s - 1 + uv)`: at an endpoint (`t₀ = 0`,
`thm:local`) it is `-(∫_{-δ}^0 φ)·Log δ + hol` (`logEnd`, the paper's integration by parts), and at
an interior point (`lem:access` (i),(ii)) it continues across from `Im δ > 0` (`logInt`, the paper's
bent segment `𝒮'`). For `𝒟` the same with the Cauchy kernel (`Dc_eq_diag`, `cauchyEnd`, `cauchyInt`).

**Integrated layout.** The 11 lemmas this file stated with `sorry` (`logEnd`, `logInt`, `cauchyEnd`,
`cauchyInt`, `N1A_local`, `N1A_access`, `Dc_eq_diag`, `Dc_local_two`, `Dc_access_two`, `Gnat_local`,
`Gnat_access`) are proved in `Fill/<name>.lean`, statements unchanged, each with its sketch as
docstring. This file keeps only the definitions and real proofs that do not use them;
`isPrincipalSheet_Gnat` moved to `Assembly.lean`. `Assembly.lean` imports all of it.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open scoped Interval

namespace GoldbachBoundaries.ThmA

/-! ### Real proofs -/

/-- Smaller discs centred on a cut are again cut discs. -/
theorem IsCutDisc.mono {κ : ℝ} {α s₀ : ℂ} {r r' : ℝ} (h : IsCutDisc κ α s₀ r) (hr : r' ≤ r) :
    IsCutDisc κ α s₀ r' :=
  ⟨(ball_subset_ball hr).trans h.1, fun hα => h.2.1 (ball_subset_ball hr hα),
    fun α' hα' hne => (h.2.2 α' hα' hne).mono_left (ball_subset_ball hr)⟩

end GoldbachBoundaries.ThmA
