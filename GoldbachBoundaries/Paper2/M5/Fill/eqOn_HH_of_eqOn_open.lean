import GoldbachBoundaries.Paper2.M5.Defs

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics
namespace GoldbachBoundaries.Paper2.M5
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

theorem eqOn_HH_of_eqOn_open {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f HH) (hg : DifferentiableOn ℂ g HH)
    {V : Set ℂ} (hV : IsOpen V) (hVne : V.Nonempty) (hVH : V ⊆ HH) (hfg : EqOn f g V) : EqOn f g HH := by
  obtain ⟨z, hz⟩ := hVne
  exact (hf.analyticOnNhd (isOpen_halfPlane 1)).eqOn_of_preconnected_of_eventuallyEq
    (hg.analyticOnNhd (isOpen_halfPlane 1))
    (convex_halfSpace_gt (f := Complex.reLm) Complex.reLm.isLinear 1).isPreconnected
    (hVH hz) (Filter.eventuallyEq_of_mem (hV.mem_nhds hz) hfg)

end GoldbachBoundaries.Paper2.M5
