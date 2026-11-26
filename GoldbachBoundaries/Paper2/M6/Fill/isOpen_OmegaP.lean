import GoldbachBoundaries.Paper2.M6.Defs

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M6

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- The cut `a - [0, ∞)` is the closed set `{Im z = Im a, Re z ≤ Re a}`. -/
lemma leftCut_eq_A (a : ℂ) : leftCut a = {z : ℂ | z.im = a.im ∧ z.re ≤ a.re} := by
  ext z
  simp only [leftCut, mem_ofPred_eq]
  constructor
  · rintro ⟨t, ht, rfl⟩
    simp; linarith
  · rintro ⟨h1, h2⟩
    refine ⟨a.re - z.re, by linarith, ?_⟩
    apply Complex.ext <;> simp [h1]

lemma isClosed_leftCut_A (a : ℂ) : IsClosed (leftCut a) := by
  rw [leftCut_eq_A]
  exact (isClosed_eq continuous_im continuous_const).inter (isClosed_le continuous_re continuous_const)

/-- A compact subset of `{Re z > 0}` meets `Σ` in a finite set (M1's `poleSetQ_locallyFinite`). -/
lemma finite_inter_poleSetQ_A {K : Set ℂ} (hK : IsCompact K) (hK0 : K ⊆ halfPlane 0) :
    (K ∩ PoleSetQ).Finite := by
  classical
  have hU : ∀ x ∈ K, ∃ U ∈ 𝓝 x, (U ∩ PoleSetQ).Finite := fun x hx =>
    M1.poleSetQ_locallyFinite x (hK0 hx)
  choose! U hUn hUf using hU
  obtain ⟨t, htK, hcov⟩ := hK.elim_nhds_subcover U hUn
  have hfin : (⋃ x ∈ t, U x ∩ PoleSetQ).Finite :=
    t.finite_toSet.biUnion fun x hx => hUf x (htK x hx)
  refine hfin.subset ?_
  rintro z ⟨hzK, hzP⟩
  obtain ⟨x, hx, hzx⟩ := mem_iUnion₂.mp (hcov hzK)
  exact mem_iUnion₂.mpr ⟨x, hx, hzx, hzP⟩

/-- **`Ω` is open** (unconditional). Near `z₀ ∈ Ω` (`x₀ = Re z₀ > 0`), only cuts of the finitely many points of `Σ`
in a compact set `K ⊆ {Re z ≥ x₀/2}` meet `ball z₀ (x₀/2)`; their union is closed and misses `z₀`. -/
theorem isOpen_OmegaP : IsOpen OmegaP := by
  classical
  rw [isOpen_iff_mem_nhds]
  intro z₀ hz₀
  have hx₀ : 0 < z₀.re := hz₀.1
  set r : ℝ := z₀.re / 2 with hr
  set R : ℝ := 1 + |z₀.im| + z₀.re with hR
  set K : Set ℂ := closedBall 0 R ∩ {w | r ≤ w.re} with hK
  have hKc : IsCompact K := (isCompact_closedBall 0 R).inter_right (isClosed_le continuous_const continuous_re)
  have hK0 : K ⊆ halfPlane 0 := fun w hw => by
    show 0 < w.re
    have := hw.2; simp only [mem_ofPred_eq] at this; linarith
  set S : Set ℂ := K ∩ PoleSetQ with hS
  have hSf : S.Finite := finite_inter_poleSetQ_A hKc hK0
  -- the closed set of relevant cuts
  set C : Set ℂ := ⋃ a ∈ S, leftCut a with hC
  have hCc : IsClosed C := hSf.isClosed_biUnion fun a _ => isClosed_leftCut_A a
  have hz₀C : z₀ ∉ C := by
    intro h
    obtain ⟨a, haS, hz⟩ := mem_iUnion₂.mp h
    exact hz₀.2 (mem_iUnion₂.mpr ⟨a, haS.2, hz⟩)
  -- any cut meeting the ball comes from a point of `S`
  have key : ∀ w ∈ ball z₀ r, ∀ a ∈ PoleSetQ, w ∈ leftCut a → a ∈ S := by
    intro w hw a ha hwa
    rw [leftCut_eq_A] at hwa
    obtain ⟨him, hre⟩ := hwa
    have hwz : ‖w - z₀‖ < r := by rwa [mem_ball, dist_eq_norm] at hw
    have h1 : |w.re - z₀.re| < r := lt_of_le_of_lt (by
      simpa using Complex.abs_re_le_norm (w - z₀)) hwz
    have h2 : |w.im - z₀.im| < r := lt_of_le_of_lt (by
      simpa using Complex.abs_im_le_norm (w - z₀)) hwz
    have hb := M1.poleSetQ_re_bounds ha
    rw [abs_lt] at h1 h2
    refine ⟨⟨?_, ?_⟩, ha⟩
    · rw [mem_closedBall, dist_zero_right]
      refine (Complex.norm_le_abs_re_add_abs_im a).trans ?_
      rw [abs_of_pos hb.1, ← him]
      have : |w.im| ≤ |z₀.im| + r := by
        rw [abs_le]; constructor
        · have := neg_abs_le z₀.im; linarith
        · have := le_abs_self z₀.im; linarith
      linarith [hb.2.1]
    · simp only [mem_ofPred_eq]; linarith
  have hsub : ball z₀ r ∩ halfPlane 0 ∩ Cᶜ ⊆ OmegaP := by
    rintro w ⟨⟨hwb, hw0⟩, hwC⟩
    refine ⟨hw0, fun h => hwC ?_⟩
    obtain ⟨a, ha, hwa⟩ := mem_iUnion₂.mp h
    exact mem_iUnion₂.mpr ⟨a, key w hwb a ha hwa, hwa⟩
  refine mem_of_superset ?_ hsub
  refine IsOpen.mem_nhds ?_ ⟨⟨mem_ball_self (by positivity), hx₀⟩, hz₀C⟩
  exact (isOpen_ball.inter (isOpen_lt continuous_const continuous_re)).inter hCc.isOpen_compl

end GoldbachBoundaries.Paper2.M6
