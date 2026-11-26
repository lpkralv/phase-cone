import GoldbachBoundaries.Paper2.M6.Fill.isOpen_OmegaP
import GoldbachBoundaries.Paper2.M6.Fill.isPathConnected_OmegaP

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M6

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **The identity theorem on `Ω`** (unconditional). `f` and `g` are analytic on the open, connected `Ω` and agree on
the open set `{Re z > 1}`, a neighbourhood of `2 ∈ Ω`. -/
theorem eqOn_OmegaP_of_eqOn_halfPlane_one {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f OmegaP)
    (hg : DifferentiableOn ℂ g OmegaP) (hfg : EqOn f g (halfPlane 1)) : EqOn f g OmegaP := by
  have h2 : (2 : ℂ) ∈ halfPlane 1 := show (1 : ℝ) < (2 : ℂ).re by norm_num
  have hnhds : halfPlane 1 ∈ 𝓝 (2 : ℂ) := (isOpen_lt continuous_const continuous_re).mem_nhds h2
  exact (hf.analyticOnNhd isOpen_OmegaP).eqOn_of_preconnected_of_eventuallyEq
    (hg.analyticOnNhd isOpen_OmegaP) isPathConnected_OmegaP.isConnected.isPreconnected
    (halfPlane_one_subset_OmegaP h2) (eventually_of_mem hnhds hfg)

end GoldbachBoundaries.Paper2.M6
