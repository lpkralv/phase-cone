import GoldbachBoundaries.T0HInf.Catalogue

/-! Critical-family dominated convergence and the finite exceptional partition. -/
noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
namespace GoldbachBoundaries.T0HInf
open GoldbachBoundaries Paper2
open _root_.GoldbachBoundaries.Phi2HInf (StirlingStrip)
open _root_.GoldbachBoundaries.Phi2HInf
  (CriticalZero criticalVal criticalPairIdx offLineZeros meromorphicAt_cauchy_of_gap)

theorem summable_norm_critical_pair (hZ1 : Z1) (hZ2 : Z2) :
    Summable (fun p : CriticalZero × CriticalZero =>
      ‖zeroCoef (criticalVal p.1) * zeroCoef (criticalVal p.2)‖) := by
  have hs : Summable (fun ρ : CriticalZero => ‖zeroCoef (criticalVal ρ)‖) :=
    (summable_norm_zeroCoef hZ1 hZ2).subtype _
  exact Summable.mul_norm (f := fun ρ : CriticalZero => zeroCoef (criticalVal ρ))
    (g := fun ρ : CriticalZero => zeroCoef (criticalVal ρ)) hs hs

theorem differentiableOn_criticalC (hZ1 : Z1) (hZ2 : Z2) :
    DifferentiableOn ℂ criticalC HH := by
  intro s hs
  change 1 < s.re at hs
  let d := (s.re - 1) / 2
  have hd : 0 < d := by dsimp [d]; linarith
  let F (p : CriticalZero × CriticalZero) (z : ℂ) :=
    zeroCoef (criticalVal p.1) * zeroCoef (criticalVal p.2) /
      (z - criticalVal p.1 - criticalVal p.2)
  have hden (p : CriticalZero × CriticalZero) (z : ℂ) (hz : z ∈ halfPlane (1 + d)) :
      d ≤ ‖z - criticalVal p.1 - criticalVal p.2‖ := by
    have hr : (z - criticalVal p.1 - criticalVal p.2).re = z.re - 1 := by
      simp only [sub_re]
      rw [show (criticalVal p.1).re = 1 / 2 from p.1.2,
        show (criticalVal p.2).re = 1 / 2 from p.2.2]
      ring
    have hh := Complex.re_le_norm (z - criticalVal p.1 - criticalVal p.2)
    rw [hr] at hh
    change 1 + d < z.re at hz
    linarith
  have hdiff : DifferentiableOn ℂ (fun z => ∑' p, F p z) (halfPlane (1 + d)) := by
    apply Complex.differentiableOn_tsum_of_summable_norm
      ((summable_norm_critical_pair hZ1 hZ2).div_const d)
    · intro p z hz
      exact (differentiableWithinAt_const _).div
        ((differentiableWithinAt_id.sub_const _).sub_const _)
        (norm_pos_iff.mp (hd.trans_le (hden p z hz)))
    · exact isOpen_halfPlane _
    · intro p z hz
      dsimp [F]
      rw [norm_div]
      exact div_le_div_of_nonneg_left (norm_nonneg _) hd (hden p z hz)
  exact (hdiff.differentiableAt ((isOpen_halfPlane _).mem_nhds
    (show s ∈ halfPlane (1 + d) by change 1 + d < s.re; dsimp [d]; linarith))).differentiableWithinAt
theorem tendsto_eta_criticalC (hZ1 : Z1) (hZ2 : Z2) (τ : ℝ) :
    Tendsto (fun η : ℝ => (η : ℂ) * criticalC (1 + τ * I + η))
      (𝓝[>] 0) (𝓝 (criticalAtom τ)) := by
  classical
  let A (p : CriticalZero × CriticalZero) : ℂ := zeroCoef (criticalVal p.1) * zeroCoef (criticalVal p.2)
  let F (η : ℝ) (p : CriticalZero × CriticalZero) : ℂ :=
    (η : ℂ) * (A p / (1 + τ * I + η - criticalVal p.1 - criticalVal p.2))
  let L (p : CriticalZero × CriticalZero) : ℂ :=
    if criticalVal p.1 + criticalVal p.2 = 1 + τ * I then A p else 0
  have hsumA : Summable (fun p => ‖A p‖) := summable_norm_critical_pair hZ1 hZ2
  have hη : Tendsto (fun η : ℝ => (η : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (Complex.continuous_ofReal.tendsto 0).mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have hlim : ∀ p, Tendsto (fun η : ℝ => F η p) (𝓝[>] 0) (𝓝 (L p)) := by
    intro p
    by_cases hp : criticalVal p.1 + criticalVal p.2 = 1 + τ * I
    · have he (η : ℝ) : 1 + τ * I + η - criticalVal p.1 - criticalVal p.2 = (η : ℂ) := by
        linear_combination -hp
      have hev : (fun η : ℝ => F η p) =ᶠ[𝓝[>] 0] fun _ => A p := by
        filter_upwards [self_mem_nhdsWithin] with η hηpos
        dsimp [F]
        rw [he]
        exact mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr (ne_of_gt hηpos))
      simpa only [L, ite_eq_left hp] using tendsto_const_nhds.congr' hev.symm
    · have hd : (1 + τ * I - criticalVal p.1 - criticalVal p.2 : ℂ) ≠ 0 := by
        intro he
        apply hp
        linear_combination -he
      have hden : Tendsto (fun η : ℝ => 1 + τ * I + η - criticalVal p.1 - criticalVal p.2)
          (𝓝[>] 0) (𝓝 (1 + τ * I - criticalVal p.1 - criticalVal p.2)) := by
        simpa using (((tendsto_const_nhds (x := 1 + τ * I)).add hη).sub_const (criticalVal p.1)).sub_const (criticalVal p.2)
      simpa only [F, L, ite_eq_right hp, zero_mul, Pi.div_apply] using
        hη.mul ((tendsto_const_nhds (x := A p)).div hden hd)
  have hbound : ∀ᶠ η : ℝ in 𝓝[>] 0, ∀ p, ‖F η p‖ ≤ ‖A p‖ := by
    filter_upwards [self_mem_nhdsWithin] with η hηpos p
    have hre : (1 + τ * I + η - criticalVal p.1 - criticalVal p.2 : ℂ).re = η := by
      simp only [sub_re, add_re, one_re, mul_re, ofReal_re, ofReal_im, I_re, I_im,
        mul_zero, zero_mul, sub_self, add_zero]
      rw [show (criticalVal p.1).re = 1 / 2 from p.1.2,
        show (criticalVal p.2).re = 1 / 2 from p.2.2]
      ring
    have hnorm : η ≤ ‖(1 + τ * I + η - criticalVal p.1 - criticalVal p.2 : ℂ)‖ := by
      simpa only [hre] using Complex.re_le_norm (1 + τ * I + η - criticalVal p.1 - criticalVal p.2 : ℂ)
    have hnormpos : 0 < ‖(1 + τ * I + η - criticalVal p.1 - criticalVal p.2 : ℂ)‖ := lt_of_lt_of_le hηpos hnorm
    dsimp [F]
    rw [norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg hηpos.le]
    calc η * (‖A p‖ / ‖(1 + τ * I + η - criticalVal p.1 - criticalVal p.2 : ℂ)‖) =
        ‖A p‖ * (η / ‖(1 + τ * I + η - criticalVal p.1 - criticalVal p.2 : ℂ)‖) := by ring
      _ ≤ ‖A p‖ * 1 := mul_le_mul_of_nonneg_left ((div_le_one hnormpos).mpr hnorm) (norm_nonneg _)
      _ = ‖A p‖ := mul_one _
  have hT := tendsto_tsum_of_dominated_convergence hsumA hlim hbound
  have hL : (∑' p, L p) = criticalAtom τ := by
    symm
    exact tsum_subtype {p : CriticalZero × CriticalZero | criticalVal p.1 + criticalVal p.2 = 1 + τ * I} A
  rw [hL] at hT
  exact hT.congr (fun η => by simp only [F, A, criticalC, tsum_mul_left])

theorem meromorphicOn_exceptionalC (hZ1 : Z1) (hZ2 : Z2)
    (hfin : offLineZeros.Finite) : MeromorphicOn exceptionalC univ := by
  classical
  intro s _
  let J := {p : NontrivialZeros × NontrivialZeros //
    (p.1 : ℂ).re ≠ 1 / 2 ∨ (p.2 : ℂ).re ≠ 1 / 2}
  obtain ⟨T, hT⟩ := (hfin.image (fun z : ℂ => |z.im|)).bddAbove
  let M := |T| + |s.im| + 2
  have hZ : {ρ : NontrivialZeros | |(ρ : ℂ).im| ≤ M}.Finite := by
    refine ((M1.finite_zeros_abs_im_le M).preimage
      (Subtype.val_injective (p := fun ρ : ℂ => ρ ∈ NontrivialZeros)).injOn).subset ?_
    intro ρ hρ
    exact ⟨ρ.2, hρ⟩
  have hP : {p : J | |(p.1.1 : ℂ).im| ≤ M ∧ |(p.1.2 : ℂ).im| ≤ M}.Finite :=
    (hZ.prod hZ).preimage Subtype.val_injective.injOn
  have ha := summable_norm_zeroCoef hZ1 hZ2
  have hsum := (Summable.mul_norm (f := fun ρ : NontrivialZeros => zeroCoef ρ)
    (g := fun ρ : NontrivialZeros => zeroCoef ρ) ha ha).subtype
      (fun p : NontrivialZeros × NontrivialZeros =>
        (p.1 : ℂ).re ≠ 1 / 2 ∨ (p.2 : ℂ).re ≠ 1 / 2)
  have hgap : ∀ w ∈ ball s 1, ∀ p : J, p ∉ hP.toFinset →
      1 ≤ ‖w - ((p.1.1 : ℂ) + p.1.2)‖ := by
    intro w hw p hp
    by_contra hn
    have hn' := (abs_im_le_norm (w - ((p.1.1 : ℂ) + p.1.2))).trans_lt (lt_of_not_ge hn)
    simp only [sub_im, add_im] at hn'
    have hw' : ‖w - s‖ < 1 := by simpa only [mem_ball, dist_eq_norm] using hw
    have hwim := (abs_im_le_norm (w - s)).trans_lt hw'
    rw [sub_im, abs_lt] at hwim
    have hsabs := abs_le.mp (le_refl |s.im|)
    have hbound : |(p.1.1 : ℂ).im| ≤ |T| ∨ |(p.1.2 : ℂ).im| ≤ |T| := by
      rcases p.2 with h | h
      · exact Or.inl ((hT (mem_image_of_mem _ (show (p.1.1 : ℂ) ∈ offLineZeros from
          ⟨p.1.1.2, h⟩))).trans (le_abs_self T))
      · exact Or.inr ((hT (mem_image_of_mem _ (show (p.1.2 : ℂ) ∈ offLineZeros from
          ⟨p.1.2.2, h⟩))).trans (le_abs_self T))
    apply hp
    rw [hP.mem_toFinset]
    change |(p.1.1 : ℂ).im| ≤ M ∧ |(p.1.2 : ℂ).im| ≤ M
    rw [abs_lt] at hn'
    rcases hbound with h | h
    · rw [abs_le] at h
      constructor <;> rw [abs_le] <;> dsimp [M] <;>
        constructor <;> linarith [hsabs.1, hsabs.2, abs_nonneg s.im]
    · rw [abs_le] at h
      constructor <;> rw [abs_le] <;> dsimp [M] <;>
        constructor <;> linarith [hsabs.1, hsabs.2, abs_nonneg s.im]
  have hm := meromorphicAt_cauchy_of_gap
    (fun p : J => zeroCoef p.1.1 * zeroCoef p.1.2)
    (fun p : J => (p.1.1 : ℂ) + p.1.2) hsum one_pos one_pos hP.toFinset hgap
  change MeromorphicAt (fun w => ∑' p : J,
    zeroCoef p.1.1 * zeroCoef p.1.2 / (w - p.1.1 - p.1.2)) s
  simpa only [sub_add_eq_sub_sub] using hm
theorem critical_decomposition (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) {s : ℂ} (hs : s ∈ HH) :
    C s = criticalC s + exceptionalC s := by
  classical
  let P : Set (NontrivialZeros × NontrivialZeros) :=
    {p | (p.1 : ℂ).re = 1 / 2 ∧ (p.2 : ℂ).re = 1 / 2}
  let f (p : NontrivialZeros × NontrivialZeros) : ℂ :=
    zeroCoef p.1 * zeroCoef p.2 / (s - p.1 - p.2)
  let e : (CriticalZero × CriticalZero) ≃ P :=
    { toFun := fun p => ⟨(p.1.1, p.2.1), p.1.2, p.2.2⟩
      invFun := fun p => (⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2⟩)
      left_inv := fun p => by rfl
      right_inv := fun p => by rfl }
  let eE : ↥(Pᶜ) ≃ {p : NontrivialZeros × NontrivialZeros //
      (p.1 : ℂ).re ≠ 1 / 2 ∨ (p.2 : ℂ).re ≠ 1 / 2} :=
    Equiv.subtypeEquivRight (fun p => not_and_or)
  have hcc : criticalC s = ∑' p : P, f p.1 := e.tsum_eq (fun p : P => f p.1)
  have hexc : (∑' p : ↥(Pᶜ), f p.1) = exceptionalC s :=
    eE.tsum_eq (fun p => f p.1)
  have hsum : Summable f := (summable_norm_pairTerm hH hZ1 hZ2 hs).of_norm
  have hsplit : criticalC s + exceptionalC s = C s := by
    rw [hcc, ← hexc]
    exact hsum.tsum_subtype_add_tsum_subtype_compl P
  exact hsplit.symm

end GoldbachBoundaries.T0HInf
