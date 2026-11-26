import GoldbachBoundaries.Paper2.M6.Defs

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M6

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **`{Re z > 0} ∖ Σ` is open** (unconditional). Near `z₀` with `Re z₀ > 0`, M1's `poleSetQ_locallyFinite` gives a
neighbourhood `V` with `V ∩ Σ` finite, hence closed; `z₀ ∉ V ∩ Σ`, so `V ∩ (V ∩ Σ)ᶜ ∩ halfPlane 0` is a neighbourhood
of `z₀` inside `{Re z > 0} ∖ Σ`. -/
theorem isOpen_halfPlane_diff_poleSetQ : IsOpen (halfPlane 0 \ PoleSetQ) := by
  rw [isOpen_iff_mem_nhds]
  rintro z ⟨hz0, hzS⟩
  obtain ⟨V, hV, hVfin⟩ := M1.poleSetQ_locallyFinite z hz0
  have hc : (V ∩ PoleSetQ)ᶜ ∈ 𝓝 z :=
    hVfin.isClosed.isOpen_compl.mem_nhds fun h => hzS h.2
  filter_upwards [hV, hc, (isOpen_halfPlane 0).mem_nhds hz0] with w hwV hwc hw0
  exact ⟨hw0, fun hwS => hwc ⟨hwV, hwS⟩⟩

end GoldbachBoundaries.Paper2.M6
