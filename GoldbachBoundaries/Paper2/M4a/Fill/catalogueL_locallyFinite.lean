import GoldbachBoundaries.Paper2.M4a.Fill.sub_one_mem_poleSetQ_of_mem_pinch
import GoldbachBoundaries.SigmaFinite
import GoldbachBoundaries.Density

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
namespace GoldbachBoundaries.Paper2.M4a
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1


/-- **`𝒞_L` is locally finite in `ℍ_L`** (RH). For `z ∈ ℍ_L`, `w₀ = L(z) - 1` has `Re w₀ > 0`; `lem_Sigma_iv hRH`
gives `V ∈ 𝓝 w₀` with `V ∩ Σ` finite. `U = {s : L(s) - 1 ∈ V}` is a neighbourhood of `z` (continuity of `L`), and
`U ∩ 𝒞_L ⊆ (fun s => L(s) - 1)⁻¹' (V ∩ Σ)` by `sub_one_mem_poleSetQ_of_mem_pinch`; the preimage of a finite set under
the injective `s ↦ L(s) - 1` (`app_injective`) is finite (`Set.Finite.preimage`). Size: 60–120 lines. -/
theorem catalogueL_locallyFinite (hRH : RiemannHypothesis) (A : Aff) :
    ∀ z ∈ A.HL, ∃ U ∈ 𝓝 z, (U ∩ catalogueL A).Finite := by
  intro z hz
  have hz' : A.app z - 1 ∈ halfPlane 0 := by
    change 0 < (A.app z - 1).re
    simp only [sub_re, one_re]
    exact sub_pos.mpr hz
  obtain ⟨V, hV, hfin⟩ := (lem_Sigma_iv_proof hRH).2 _ hz'
  let f : ℂ → ℂ := fun s => A.app s - 1
  have hf : Continuous f := by unfold f Aff.app; fun_prop
  have hi : Function.Injective f := fun s t h => app_injective A (sub_left_inj.mp h)
  refine ⟨f ⁻¹' V, hf.continuousAt.preimage_mem_nhds hV, ?_⟩
  exact (hfin.preimage hi.injOn).subset (fun s hs =>
    ⟨hs.1, sub_one_mem_poleSetQ_of_mem_pinch hRH hs.2.2 hs.2.1⟩)

end GoldbachBoundaries.Paper2.M4a
