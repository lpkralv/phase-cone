import GoldbachBoundaries.Paper2.M3.Hsq
import GoldbachBoundaries.Paper2.M3.Fill.differentiableOn_laplace
import GoldbachBoundaries.Paper2.M3.Fill.integrableOn_laplace_of_lt
import GoldbachBoundaries.Paper2.M3.Fill.iteratedDeriv_laplace
import GoldbachBoundaries.Paper2.M3.Fill.laplace_no_extension

/-!
# M3: Landau's theorem on Laplace transforms of non-negative functions (`nr:lem:Landau`)

General, no hypothesis on the zeros. `S = laplaceConvSet φ` (real `x` with `φ(u)e^{-xu}` integrable on `(0, ∞)`) is an
up-set (`e^{-x'u} ≤ e^{-xu}` for `u > 0`, `x' ≥ x`), so `{s : ∃ x ∈ S, x < Re s}` is `{Re s > σ_c}`. The paper's
proof: domination by `φ(u)e^{-xu}` gives absolute convergence and holomorphy, and
`𝓛^{(n)}(a) = ∫_0^∞ (-u)^n φ(u)e^{-au} du` at real `a > σ_c`; a holomorphic `g` on `Δ(σ_c, r)` agreeing with `𝓛` on the
right half would make the Taylor series of the glued function at `a = σ_c + r/3` converge at `s₁ = σ_c - r/6`, and
Tonelli turns that series into `∫_0^∞ φ(u)e^{-s₁u} du < ∞`, contradicting `s₁ < σ_c`.

The target `lem_Landau_proof` is at the end of this file (`Mellin.lean` uses it).
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M3

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-! ## Target: `lem_Landau` -/

/-- `lem_Landau` of `Paper2/Statements.lean`, statement verbatim. -/
theorem lem_Landau_proof (φ : ℝ → ℝ) (hφm : Measurable ((Ioi (0 : ℝ)).domRestrict φ))
    (hφ0 : ∀ u, 0 < u → 0 ≤ φ u) (hS : (laplaceConvSet φ).Nonempty) :
    (∀ s : ℂ, (∃ x ∈ laplaceConvSet φ, x < s.re) →
      IntegrableOn (fun u : ℝ => (φ u : ℂ) * exp (-(s * u))) (Ioi (0 : ℝ))) ∧
    DifferentiableOn ℂ (laplace φ) {s | ∃ x ∈ laplaceConvSet φ, x < s.re} ∧
    (BddBelow (laplaceConvSet φ) → ∀ r : ℝ, 0 < r →
      ¬ ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball ((sInf (laplaceConvSet φ) : ℝ) : ℂ) r) ∧
        EqOn g (laplace φ) (ball ((sInf (laplaceConvSet φ) : ℝ) : ℂ) r ∩
          {s | sInf (laplaceConvSet φ) < s.re})) :=
  ⟨fun _ hs => integrableOn_laplace_of_lt φ hφm hφ0 hs, differentiableOn_laplace φ hφm hφ0,
    fun hB _ hr => laplace_no_extension φ hφm hφ0 hS hB hr⟩

end GoldbachBoundaries.Paper2.M3
