import GoldbachBoundaries.Paper2.M6.Fill.OmegaP_subset
import GoldbachBoundaries.Paper2.M6.Fill.add_real_mem_OmegaP
import GoldbachBoundaries.Paper2.M6.Fill.isOpen_OmegaP

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M6

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **`P̃' = -Q` on `Ω`** (unconditional). The segment `K = [z, z + 2]` is a compact convex subset of the open `Ω`
(`add_real_mem_OmegaP`, `isOpen_OmegaP`), so some thickening `U` of it is a convex open subset of `Ω`, on which
`Qcont` is holomorphic (`OmegaP_subset`, M2's `isQCont_Qcont`). Let `Φ` be the segment primitive of `Qcont` on `U`
(paper 1's `ThmA.GroupDPrimitive.hasDerivAt_segInt`). For `w` near `z`, `w + [0, 2] ⊆ U`, so
`∫_0^2 Qcont(w + t) dt = Φ(w + 2) - Φ(w)`, which has derivative `Qcont(z + 2) - Qcont(z)` at `z`. With paper 1's
`hasDerivAt_P` at `z + 2` and `Qcont(z + 2) = Q(z + 2)`: `P̃'(z) = -Qcont(z)`. -/
theorem hasDerivAt_Ptil {z : ℂ} (hz : z ∈ OmegaP) : HasDerivAt Ptil (-Qcont z) z := by
  have hz0 : 0 < z.re := hz.1
  set K : Set ℂ := segment ℝ z (z + 2) with hK
  have hKΩ : K ⊆ OmegaP := by
    rintro w ⟨a, b, ha, hb, hab, rfl⟩
    have hab' : (a : ℂ) + (b : ℂ) = 1 := by exact_mod_cast hab
    have hw : a • z + b • (z + 2) = z + ((2 * b : ℝ) : ℂ) := by
      simp only [Complex.real_smul]; push_cast; linear_combination z * hab'
    rw [hw]
    exact add_real_mem_OmegaP hz (by positivity)
  have hseg : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 2 → z + t ∈ K := fun t ht =>
    ⟨1 - t / 2, t / 2, by linarith [ht.2], by linarith [ht.1], by ring, by
      simp only [Complex.real_smul]; push_cast; ring⟩
  have hKc : IsCompact K := by
    rw [hK, segment_eq_image']
    exact isCompact_Icc.image (by fun_prop)
  obtain ⟨ε, hε, hεK⟩ := hKc.exists_thickening_subset_open isOpen_OmegaP hKΩ
  set U : Set ℂ := thickening ε K with hU
  have hUo : IsOpen U := isOpen_thickening
  have hUc : Convex ℝ U := (convex_segment z (z + 2)).thickening ε
  have hzU : z ∈ U := self_subset_thickening hε K (left_mem_segment ℝ z (z + 2))
  have hQd : DifferentiableOn ℂ Qcont U := fun w hw =>
    (M2.isQCont_Qcont.2.2 w (OmegaP_subset (hεK hw))).differentiableAt.differentiableWithinAt
  set Φ : ℂ → ℂ := fun w => ThmA.segInt Qcont z w with hΦdef
  have hΦ : ∀ w ∈ U, HasDerivAt Φ (Qcont w) w := fun w hw =>
    ThmA.GroupDPrimitive.hasDerivAt_segInt hUo hUc hQd hzU hw
  have hshift : ∀ w ∈ ball z ε, ∀ t ∈ Icc (0 : ℝ) 2, w + t ∈ U := by
    intro w hw t ht
    rw [hU, mem_thickening_iff]
    refine ⟨z + t, hseg t ht, ?_⟩
    rw [dist_eq_norm, add_sub_add_right_eq_sub, ← dist_eq_norm]
    exact hw
  have hint : ∀ w ∈ ball z ε, (∫ t in (0 : ℝ)..2, Qcont (w + t)) = Φ (w + 2) - Φ w := by
    intro w hw
    have hd : ∀ t ∈ uIcc (0 : ℝ) 2, HasDerivAt (fun t : ℝ => Φ (w + t)) (Qcont (w + t)) t := by
      intro t ht
      rw [uIcc_of_le (by norm_num)] at ht
      have h1 : HasDerivAt (fun x : ℂ => Φ (w + x)) (Qcont (w + t)) (t : ℂ) := by
        have := (hΦ (w + t) (hshift w hw t ht)).comp (t : ℂ) ((hasDerivAt_id (t : ℂ)).const_add w)
        simpa [Function.comp_def] using this
      exact h1.comp_ofReal
    have hc : ContinuousOn (fun t : ℝ => Qcont (w + t)) (uIcc 0 2) := by
      intro t ht
      rw [uIcc_of_le (by norm_num)] at ht
      exact (ContinuousAt.comp (f := fun t : ℝ => w + (t : ℂ)) (g := Qcont)
        (hQd.differentiableAt (hUo.mem_nhds (hshift w hw t ht))).continuousAt
        (by fun_prop)).continuousWithinAt
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable
    simpa using this
  have hev : (fun w => ∫ t in (0 : ℝ)..2, Qcont (w + t)) =ᶠ[𝓝 z] fun w => Φ (w + 2) - Φ w :=
    Filter.eventuallyEq_of_mem (ball_mem_nhds z hε) hint
  have hz2U : z + 2 ∈ U := by
    simpa using hshift z (mem_ball_self hε) 2 ⟨by norm_num, le_rfl⟩
  have hD1 : HasDerivAt (fun w => Φ (w + 2) - Φ w) (Qcont (z + 2) - Qcont z) z := by
    have h1 : HasDerivAt (fun w => Φ (w + 2)) (Qcont (z + 2)) z := by
      have := (hΦ (z + 2) hz2U).comp z ((hasDerivAt_id z).add_const 2)
      simpa [Function.comp_def] using this
    exact h1.sub (hΦ z hzU)
  have hD2 : HasDerivAt (fun w => ∫ t in (0 : ℝ)..2, Qcont (w + t)) (Qcont (z + 2) - Qcont z) z :=
    hD1.congr_of_eventuallyEq hev
  have hre2 : 1 < (z + 2).re := by simp; linarith
  have hP : HasDerivAt (fun w => P (w + 2)) (-Q (z + 2)) z := by
    have := (hasDerivAt_P (show z + 2 ∈ halfPlane 1 from hre2)).comp z ((hasDerivAt_id z).add_const 2)
    simpa [Function.comp_def] using this
  have hsum := hP.add hD2
  have heq : -Qcont z = -Q (z + 2) + (Qcont (z + 2) - Qcont z) := by
    rw [TIdentity.Qcont_eq_Q_of_one_lt hre2]; ring
  rw [heq]
  exact hsum

end GoldbachBoundaries.Paper2.M6
