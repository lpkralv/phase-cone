import GoldbachBoundaries.T0HInf.ZeroCoefficients

/-! The generic Cauchy-series and local-gap cores are reused verbatim. -/
noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
namespace GoldbachBoundaries.T0HInf
open GoldbachBoundaries Paper2
open _root_.GoldbachBoundaries.Phi2HInf (StirlingStrip)
open _root_.GoldbachBoundaries.Phi2HInf
  (meromorphicAt_cauchy_of_gap hasResidue_cauchy_of_gap pairCat_denominator_bound collisionIdx)

theorem meromorphicOn_C (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) :
    MeromorphicOn C HH := by
  intro s hs
  let r := (s.re - 1) / 2
  have hr : 0 < r := by change 1 < s.re at hs; dsimp [r]; linarith
  have hsub : closedBall s r ⊆ HH := by
    intro w hw
    have hh : ‖w - s‖ ≤ r := by simpa only [mem_closedBall, dist_eq_norm] using hw
    have hre := (abs_re_le_norm (w - s)).trans hh
    rw [sub_re, abs_le] at hre
    change 1 < w.re
    dsimp [r] at *
    linarith [hre.1]
  obtain ⟨E, d, hd, hgap⟩ := pairCat_denominator_bound hH (isCompact_closedBall s r) hsub
  have ha := summable_norm_zeroCoef hZ1 hZ2
  have hm := meromorphicAt_cauchy_of_gap (z := s)
    (fun p : NontrivialZeros × NontrivialZeros => zeroCoef p.1 * zeroCoef p.2)
    (fun p => (p.1 : ℂ) + p.2)
    (Summable.mul_norm (f := fun ρ : NontrivialZeros => zeroCoef ρ)
      (g := fun ρ : NontrivialZeros => zeroCoef ρ) ha ha) hr hd E
    (by
      intro w hw p hp
      simpa only [sub_add_eq_sub_sub] using hgap w (ball_subset_closedBall hw) p hp)
  change MeromorphicAt (fun w => ∑' p : NontrivialZeros × NontrivialZeros,
    zeroCoef p.1 * zeroCoef p.2 / (w - p.1 - p.2)) s
  simpa only [sub_add_eq_sub_sub] using hm

theorem meromorphicOn_singleC (hZ1 : Z1) (hZ2 : Z2) :
    MeromorphicOn singleC univ := by
  classical
  intro s _
  have hfin : {ρ : NontrivialZeros | |(ρ : ℂ).im| ≤ |s.im| + 2}.Finite := by
    refine ((M1.finite_zeros_abs_im_le (|s.im| + 2)).preimage
      (Subtype.val_injective (p := fun ρ : ℂ => ρ ∈ NontrivialZeros)).injOn).subset ?_
    intro ρ hρ
    exact ⟨ρ.2, hρ⟩
  apply meromorphicAt_cauchy_of_gap (fun ρ : NontrivialZeros => zeroCoef ρ)
    (fun ρ => ρ) (summable_norm_zeroCoef hZ1 hZ2)
    (r := 1) (d := 1) one_pos one_pos hfin.toFinset
  intro w hw ρ hρ
  have hfar : |s.im| + 2 < |(ρ : ℂ).im| := by
    simpa only [hfin.mem_toFinset, mem_setOf_eq, not_le] using hρ
  have hnear : ‖w - s‖ < 1 := by simpa only [mem_ball, dist_eq_norm] using hw
  have him : |w.im| < |s.im| + 1 := by
    have ht := abs_sub_abs_le_abs_sub w.im s.im
    have hn := abs_im_le_norm (w - s)
    rw [sub_im] at hn
    linarith
  have ht := abs_sub_abs_le_abs_sub (ρ : ℂ).im w.im
  have hn := abs_im_le_norm (w - (ρ : ℂ))
  rw [sub_im, abs_sub_comm] at hn
  linarith
theorem hasResidue_C (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2)
    {s : ℂ} (hs : s ∈ HH) : HasResidue C s (collisionAtom s) := by
  change 1 < s.re at hs
  let r := (s.re - 1) / 2
  have hr : 0 < r := by dsimp [r]; linarith
  have hsub : closedBall s r ⊆ HH := by
    intro w hw
    have hh : ‖w - s‖ ≤ r := by simpa only [mem_closedBall, dist_eq_norm] using hw
    have hre := (abs_re_le_norm (w - s)).trans hh
    rw [sub_re, abs_le] at hre
    change 1 < w.re
    dsimp [r] at *
    linarith [hre.1]
  obtain ⟨E, d, hd, hgap⟩ := pairCat_denominator_bound hH (isCompact_closedBall s r) hsub
  have ha := summable_norm_zeroCoef hZ1 hZ2
  have hres := hasResidue_cauchy_of_gap (z := s)
    (fun p : NontrivialZeros × NontrivialZeros => zeroCoef p.1 * zeroCoef p.2)
    (fun p => (p.1 : ℂ) + p.2)
    (Summable.mul_norm (f := fun ρ : NontrivialZeros => zeroCoef ρ)
      (g := fun ρ : NontrivialZeros => zeroCoef ρ) ha ha) hr hd E
    (by
      intro w hw p hp
      simpa only [sub_add_eq_sub_sub] using hgap w (ball_subset_closedBall hw) p hp)
  change HasResidue (fun w => ∑' p : NontrivialZeros × NontrivialZeros,
    zeroCoef p.1 * zeroCoef p.2 / (w - p.1 - p.2)) s (collisionAtom s)
  simpa only [collisionAtom, collisionIdx, sub_add_eq_sub_sub] using hres
theorem summable_norm_pairTerm (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2)
    {s : ℂ} (hs : s ∈ HH) :
    Summable (fun p : NontrivialZeros × NontrivialZeros =>
      ‖zeroCoef p.1 * zeroCoef p.2 / (s - p.1 - p.2)‖) := by
  have ha := summable_norm_zeroCoef hZ1 hZ2
  have hp := Summable.mul_norm (f := fun ρ : NontrivialZeros => zeroCoef ρ)
    (g := fun ρ : NontrivialZeros => zeroCoef ρ) ha ha
  obtain ⟨E, d, hd, hbound⟩ := pairCat_denominator_bound hH isCompact_singleton
    (show ({s} : Set ℂ) ⊆ HH by simpa)
  apply (hp.div_const d).of_norm_bounded_eventually
  have hev : ∀ᶠ p in cofinite, p ∉ E := E.finite_toSet.compl_mem_cofinite
  filter_upwards [hev] with p hpE
  rw [Real.norm_of_nonneg (norm_nonneg _), norm_div]
  exact div_le_div_of_nonneg_left (norm_nonneg _) hd (hbound s (mem_singleton _) p hpE)


end GoldbachBoundaries.T0HInf
