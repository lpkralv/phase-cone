import GoldbachBoundaries.ResidueClass.Zeros

/-! # Mellin inversion of the exponentially smoothed residue-class weights -/

noncomputable section

open Complex Filter Set MeasureTheory

namespace GoldbachBoundaries.ResidueClass

open Phi2Proof.FillA (posNat summable_vonMangoldt_mul_exp_neg)

variable (q : ℕ)

/-- The exponential generating sum used in the inverse Mellin formula. -/
def smoothed (x : ℝ) : ℝ :=
  ∑' n : ℕ, mangoldtOne q n * Real.exp (-((n : ℝ) * x))

theorem summable_smoothed_terms {x : ℝ} (hx : 0 < x) :
    Summable fun n : ℕ ↦ mangoldtOne q n * Real.exp (-((n : ℝ) * x)) :=
  (summable_vonMangoldt_mul_exp_neg hx).of_nonneg_of_le
    (fun _ ↦ mul_nonneg (mangoldtOne_nonneg _ _) (Real.exp_pos _).le)
    (fun _ ↦ mul_le_mul_of_nonneg_right (mangoldtOne_le _ _) (Real.exp_pos _).le)

theorem smoothed_nonneg (x : ℝ) : 0 ≤ smoothed q x :=
  tsum_nonneg fun _ ↦ mul_nonneg (mangoldtOne_nonneg _ _) (Real.exp_pos _).le

theorem continuousOn_smoothed : ContinuousOn (smoothed q) (Ioi 0) := by
  intro x hx
  have hx' : 0 < x := hx
  have h : ContinuousOn (smoothed q) (Ioi (x / 2)) := by
    refine continuousOn_tsum (fun _ ↦ by fun_prop)
      (summable_smoothed_terms q (half_pos hx')) fun n y hy ↦ ?_
    rw [Real.norm_of_nonneg (mul_nonneg (mangoldtOne_nonneg _ _) (Real.exp_pos _).le)]
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left hy.le (Nat.cast_nonneg n))))
      (mangoldtOne_nonneg _ _)
  exact (h.continuousAt (Ioi_mem_nhds (by linarith))).continuousWithinAt

theorem exists_smoothed_le_exp : ∃ C : ℝ, 0 ≤ C ∧
    ∀ x : ℝ, 1 ≤ x → smoothed q x ≤ C * Real.exp (-x) := by
  obtain ⟨C, hC⟩ := Phi2Proof.FillA.FL_continuousOn_and_le_exp.2
  refine ⟨max C 0, le_max_right _ _, fun x hx ↦ ?_⟩
  calc
    smoothed q x ≤ Phi2Proof.FL x :=
      (summable_smoothed_terms q (by linarith)).tsum_le_tsum
        (fun _ ↦ mul_le_mul_of_nonneg_right (mangoldtOne_le _ _) (Real.exp_pos _).le)
        (summable_vonMangoldt_mul_exp_neg (by linarith))
    _ ≤ C * Real.exp (-x) := hC x hx
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le

variable [NeZero q]

/-- The initial Mellin transform is the character average times Gamma. -/
theorem mellin_smoothed {z : ℂ} (hz : 1 < z.re) :
    MellinConvergent (fun x ↦ (smoothed q x : ℂ)) z ∧
      mellin (fun x ↦ (smoothed q x : ℂ)) z = Gamma z * D q z := by
  let a : ℕ → ℂ := fun n ↦ (mangoldtOne q n : ℂ)
  have hw (i : posNat) : 0 < ((i : ℕ) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero i.prop
  have hF : ∀ x ∈ Ioi (0 : ℝ), HasSum
      (fun i : posNat ↦ a i * Real.exp (-((i : ℕ) : ℝ) * x)) (smoothed q x : ℂ) := by
    intro x hx
    have h := (summable_smoothed_terms q hx).hasSum
    rw [← Complex.hasSum_ofReal] at h
    have h' : HasSum (fun n : ℕ ↦ a n * Real.exp (-((n : ℝ) * x))) (smoothed q x : ℂ) := by
      simpa only [a, ofReal_mul, smoothed] using h
    exact (hasSum_subtype_iff_of_support_subset
      (show Function.support (fun n : ℕ ↦ a n * Real.exp (-((n : ℝ) * x))) ⊆ posNat from
        fun n hn hzero ↦ hn (by simp [hzero, a]))).mpr h' |>.congr_fun
        (fun _ ↦ by simp only [neg_mul, Function.comp_apply])
  have hnorm : Summable (fun i : posNat ↦ ‖a i‖ / ((i : ℕ) : ℝ) ^ z.re) := by
    refine ((lSeriesSummable_mangoldtOne q hz).norm.subtype posNat).congr fun i ↦ ?_
    have hn : i.val ≠ 0 := i.prop
    simp only [Function.comp_apply, LSeries.norm_term_eq, ite_eq_right hn, a]
  obtain ⟨hconv, hval⟩ := TIdentity.mellin_convergent_and_hasSum_of_exp hw
    (by linarith) hF (continuous_ofReal.comp_continuousOn (continuousOn_smoothed q)) hnorm
  refine ⟨hconv, ?_⟩
  have hsupp : Function.support (LSeries.term a z) ⊆ posNat :=
    fun n hn hzero ↦ hn (by simp [hzero, LSeries.term_zero])
  rw [← hval.tsum_eq, D_eq_lSeries q hz, LSeries, ← tsum_subtype_eq_of_support_subset hsupp,
    ← tsum_mul_left]
  exact tsum_congr fun i ↦ by rw [LSeries.term_of_ne_zero i.prop, ofReal_natCast, mul_div_assoc]

/-- The Dirichlet series majorizes the character average on its initial half-plane. -/
theorem norm_D_le_of_re {c : ℝ} (hc : 1 < c) {z : ℂ} (hz : z.re = c) :
    ‖D q z‖ ≤ ∑' n, ‖LSeries.term (fun k ↦ (mangoldtOne q k : ℂ)) (c : ℂ) n‖ := by
  rw [D_eq_lSeries q (hz ▸ hc), LSeries]
  refine (norm_tsum_le_tsum_norm (lSeriesSummable_mangoldtOne q (hz ▸ hc)).norm).trans_eq ?_
  exact tsum_congr fun n ↦ by simp [LSeries.norm_term_eq, hz]

theorem integrable_Gamma_mul_D_right {c : ℝ} (hc : 1 < c) :
    Integrable fun y : ℝ ↦ Gamma (c + y * I) * D q (c + y * I) := by
  let K := ∑' n, ‖LSeries.term (fun k ↦ (mangoldtOne q k : ℂ)) (c : ℂ) n‖
  refine TIdentity.integrable_Gamma_mul_of_bound (by linarith) ?_ (K := K) fun y ↦ ?_
  · rw [continuous_iff_continuousAt]
    intro y
    have hr : ((c : ℂ) + y * I).re = c := by simp
    exact (analyticAt_D (by rw [hr]; linarith) (fun h ↦ by
      rw [h, one_re] at hr; linarith) (fun χ ↦ primitiveL_ne_zero_of_one_le_re χ
        (by rw [hr]; exact hc.le))).continuousAt.comp (f := fun y : ℝ ↦ (c : ℂ) + y * I)
          (by fun_prop)
  · exact (norm_D_le_of_re q hc (by simp)).trans
      (le_mul_of_one_le_right (tsum_nonneg (fun _ ↦ norm_nonneg _)) (by simp))

/-- The inverse Mellin kernel; the Gamma factor supplies vertical decay. -/
def inverseKernel (x : ℝ) (z : ℂ) : ℂ :=
  (x : ℂ) ^ (-z) * (Gamma z * D q z)

/-- On an initial vertical line the inverse Mellin integral equals the smoothed sum. -/
theorem smoothed_eq_verticalIntegral {c x : ℝ} (hc : 1 < c) (hx : 0 < x) :
    (smoothed q x : ℂ) = VerticalIntegral' (inverseKernel q x) c := by
  have hmel (y : ℝ) : mellin (fun x ↦ (smoothed q x : ℂ)) (c + y * I) =
      Gamma (c + y * I) * D q (c + y * I) :=
    (mellin_smoothed q (by simpa using hc)).2
  have hconv : MellinConvergent (fun x ↦ (smoothed q x : ℂ)) (c : ℂ) :=
    (mellin_smoothed q (by simpa using hc)).1
  have hvi : VerticalIntegrable (mellin (fun x ↦ (smoothed q x : ℂ))) c := by
    unfold VerticalIntegrable
    simp_rw [hmel]
    exact integrable_Gamma_mul_D_right q hc
  have hcont : ContinuousAt (fun x ↦ (smoothed q x : ℂ)) x :=
    continuous_ofReal.continuousAt.comp ((continuousOn_smoothed q).continuousAt (Ioi_mem_nhds hx))
  rw [← mellinInv_mellin_eq c _ hx hconv hvi hcont, mellinInv, VerticalIntegral', VerticalIntegral]
  simp_rw [hmel, inverseKernel, smul_eq_mul, Complex.real_smul]
  rw [← mul_assoc]
  congr 1
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_pos.ne'
  field_simp
  push_cast
  ring_nf
  exact mul_inv_cancel₀ hpi

end GoldbachBoundaries.ResidueClass
