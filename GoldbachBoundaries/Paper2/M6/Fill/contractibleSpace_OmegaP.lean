import GoldbachBoundaries.Paper2.M6.Fill.isPathConnected_OmegaP

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M6

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- Two maps into a subset `S ⊆ ℂ` whose values are joined by segments inside `S` are homotopic (the straight-line
homotopy, taken in the subtype). -/
lemma homotopic_of_segment_subset_A {X : Type*} [TopologicalSpace X] {S : Set ℂ} (f g : C(X, S))
    (h : ∀ x, segment ℝ (f x : ℂ) (g x) ⊆ S) : f.Homotopic g := by
  refine ⟨{ toFun := fun p => ⟨(1 - (p.1 : ℝ)) • (f p.2 : ℂ) + (p.1 : ℝ) • (g p.2 : ℂ),
              h p.2 ⟨1 - (p.1 : ℝ), p.1, by linarith [p.1.2.2], p.1.2.1, by ring, rfl⟩⟩
            continuous_toFun := ?_
            map_zero_left := ?_
            map_one_left := ?_ }⟩
  · apply Continuous.subtype_mk
    have hf : Continuous fun p : unitInterval × X => (f p.2 : ℂ) :=
      continuous_subtype_val.comp (f.continuous.comp continuous_snd)
    have hg : Continuous fun p : unitInterval × X => (g p.2 : ℂ) :=
      continuous_subtype_val.comp (g.continuous.comp continuous_snd)
    have ht : Continuous fun p : unitInterval × X => (p.1 : ℝ) :=
      continuous_subtype_val.comp continuous_fst
    exact ((continuous_const.sub ht).smul hf).add (ht.smul hg)
  · intro x; apply Subtype.ext; simp
  · intro x; apply Subtype.ext; simp

/-- **`Ω` is contractible** (unconditional). The identity of `Ω` is homotopic (straight line, `add_real_mem_OmegaP`) to
the eastward push `z ↦ z + max(0, 2 - Re z)`, which is homotopic (straight line in the convex `{Re z ≥ 2} ⊆ Ω`) to the
constant `2`. -/
theorem contractibleSpace_OmegaP : ContractibleSpace OmegaP := by
  rw [contractible_iff_id_nullhomotopic]
  have h2 : (2 : ℂ) ∈ OmegaP := re_ge_two_subset_OmegaP_A (by simp)
  let R : C(OmegaP, OmegaP) :=
    ⟨fun z => ⟨eastPushA z, segment_eastPushA_subset z.2 (right_mem_segment ℝ _ _)⟩,
      (continuous_eastPushA.comp continuous_subtype_val).subtype_mk _⟩
  refine ⟨⟨2, h2⟩, ?_⟩
  refine ContinuousMap.Homotopic.trans (g := R) ?_ ?_
  · exact homotopic_of_segment_subset_A _ _ fun z => segment_eastPushA_subset z.2
  · refine homotopic_of_segment_subset_A _ _ fun z => ?_
    exact (convex_re_ge_two_A.segment_subset (two_le_re_eastPushA z) (by simp)).trans
      re_ge_two_subset_OmegaP_A

end GoldbachBoundaries.Paper2.M6
