import GoldbachBoundaries.ResidueClass.ExceptionalZeros
import GoldbachBoundaries.ResidueClass.ContourBounds
import GoldbachBoundaries.ResidueClass.Smoothed
import GoldbachBoundaries.T0HInf.InverseMellinDerivative
import GoldbachBoundaries.ResidueClass.GammaWeights
import GoldbachBoundaries.Paper2.M5.Fill.rectangleIntegral'_eq_sum_of_simplePoles_rect
import GoldbachBoundaries.Paper2.M4b.Fill.isBigO_mul_sub_residue

/-! # Positive-line contour shift and the restricted explicit formula -/

noncomputable section

open Complex Filter Topology Set MeasureTheory Asymptotics
open scoped Interval

namespace GoldbachBoundaries.ResidueClass

variable {q : ℕ} [NeZero q]

/-- The remaining vertical integral on the line of real part `δ`. -/
def lineRemainder (q : ℕ) [NeZero q] (δ x : ℝ) : ℂ :=
  VerticalIntegral' (inverseKernel q x) δ

/-- The remainder is bounded by a constant times `x ^ (-δ)` on the positive axis. -/
theorem norm_lineRemainder_le (q : ℕ) [NeZero q] (δ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x > 0, ‖lineRemainder q δ x‖ ≤ C * x ^ (-δ) := by
  let f (z : ℂ) := Gamma z * D q z
  refine ⟨(1 / (2 * Real.pi)) * ∫ y : ℝ, ‖f (δ + y * I)‖,
    mul_nonneg (by positivity) (integral_nonneg (fun _ ↦ norm_nonneg _)), fun x hx ↦ ?_⟩
  exact T0HInf.norm_inverse_vertical_le (σ := δ) hx f

private theorem criticalPoint_ne_one (t : ℝ) : criticalPoint t ≠ 1 := by
  intro h
  have hh := congrArg Complex.re h
  norm_num [criticalPoint_re] at hh

private theorem criticalPoint_injective : Function.Injective criticalPoint :=
  fun _ _ h ↦ by simpa only [criticalPoint_im] using congrArg Complex.im h

private def truncatedOrd (q : ℕ) [NeZero q] (H : ℝ) : Finset (Ordinates q) :=
  (((finite_Ordinates_inter (q := q) (-H) H).preimage
    (Subtype.val_injective (p := fun t ↦ t ∈ Ordinates q)).injOn).subset
    (show {t : Ordinates q | |(t : ℝ)| < H} ⊆ _ from
      fun t ht ↦ ⟨t.prop, abs_le.mp ht.le⟩)).toFinset

private theorem mem_truncatedOrd {H : ℝ} {t : Ordinates q} :
    t ∈ truncatedOrd q H ↔ |(t : ℝ)| < H :=
  Set.Finite.mem_toFinset _

private theorem inverseKernel_sub_pole_isBigO {x : ℝ} (hx : 0 < x)
    {p : ℂ} (hp : 0 < p.re) {R : ℂ} (hres : HasResidue (D q) p R) :
    (inverseKernel q x - fun z ↦ ((x : ℂ) ^ (-p) * Gamma p * R) / (z - p))
      =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
  have hG : AnalyticAt ℂ Gamma p :=
    (show DifferentiableOn ℂ Gamma (halfPlane 0) from
      fun z hz ↦ (TIdentity.differentiableAt_Gamma_of_re_pos hz).differentiableWithinAt).analyticAt
      ((isOpen_halfPlane 0).mem_nhds hp)
  have hx' : AnalyticAt ℂ (fun z : ℂ ↦ (x : ℂ) ^ (-z)) p :=
    (show Differentiable ℂ (fun z : ℂ ↦ (x : ℂ) ^ (-z)) from
      TIdentity.differentiableAt_ofReal_cpow_neg hx).analyticAt p
  have hm := meromorphic_D (q := q) p
  convert Paper2.M4b.isBigO_mul_sub_residue hm (hres.neg_one_le_meromorphicOrderAt hm) hres
    (hx'.mul hG) using 1
  ext z
  simp only [Pi.sub_apply, Pi.mul_apply, inverseKernel]
  ring

private theorem rectangle_inverseKernel {E : Finset ℂ} {δ H x : ℝ}
    (hδ : 0 < δ) (hδ' : δ < 1 / 2) (hH : 0 < H) (hx : 0 < x)
    (hE : ∀ p, p ∈ E ↔ p ∈ OffLineZeros q)
    (hleft : ∀ p ∈ E, δ < Complex.re p) (hheight : ∀ p ∈ E, |Complex.im p| < H)
    (havoid : ∀ t ∈ Ordinates q, |t| ≠ H) :
    RectangleIntegral' (inverseKernel q x) ((δ : ℂ) - I * H) (2 + I * H) =
      principalWeight q / (x : ℂ) -
        (∑ t ∈ truncatedOrd q H, gammaWeight q t * (x : ℂ) ^ (-criticalPoint t)) -
        exceptionalTerm q E x := by
  classical
  let e : Ordinates q ↪ ℂ := ⟨fun t ↦ criticalPoint t, criticalPoint_injective.comp Subtype.val_injective⟩
  let W := (truncatedOrd q H).map e
  let S := insert 1 (W ∪ E)
  let A (p : ℂ) := if p = 1 then principalWeight q / (x : ℂ)
    else -(exceptionalWeight q p * (x : ℂ) ^ (-p))
  have hm (p : ℂ) : p ∈ S ↔ p = 1 ∨ (∃ t ∈ truncatedOrd q H, criticalPoint t = p) ∨ p ∈ E := by
    simp [S, W, e]
  have hS (p : ℂ) (hp : p ∈ S) : δ < p.re ∧ p.re < 2 ∧ |p.im| < H := by
    rcases (hm p).mp hp with rfl | ⟨t, ht, rfl⟩ | hp
    · simp only [one_re, one_im, abs_zero]
      exact ⟨by linarith, by norm_num, hH⟩
    · rw [criticalPoint_re, criticalPoint_im]
      exact ⟨hδ', by norm_num, mem_truncatedOrd.mp ht⟩
    · exact ⟨hleft p hp, (OffLineZeros.re_lt_one ((hE p).mp hp)).trans (by norm_num), hheight p hp⟩
  have hf : DifferentiableOn ℂ (inverseKernel q x)
      (Icc δ 2 ×ℂ Icc (-H) H \ (S : Set ℂ)) := by
    rintro z ⟨hz, hn⟩
    obtain ⟨⟨hzδ, _⟩, hy⟩ := mem_reProdIm.mp hz
    have hz₀ := hδ.trans_le hzδ
    have hz₁ : z ≠ 1 := fun he ↦ hn ((hm z).mpr (.inl he))
    have hne (χ : DirichletCharacter ℂ q) : primitiveL χ z ≠ 0 := by
      by_cases hzre : 1 ≤ z.re
      · exact primitiveL_ne_zero_of_one_le_re χ hzre
      · intro hzero
        have hzP : z ∈ primitiveZeros χ := ⟨hzero, hz₀, lt_of_not_ge hzre⟩
        by_cases hc : z.re = 1 / 2
        · have he : criticalPoint z.im = z :=
            Complex.ext (by rw [criticalPoint_re, hc]) (criticalPoint_im _)
          have ht : z.im ∈ Ordinates q := mem_Ordinates_iff.mpr ⟨χ, he.symm ▸ hzP⟩
          have hy' : |z.im| < H := (abs_le.mpr hy).lt_of_ne (havoid _ ht)
          exact hn ((hm z).mpr (.inr (.inl ⟨⟨z.im, ht⟩, mem_truncatedOrd.mpr hy', he⟩)))
        · exact hn ((hm z).mpr (.inr (.inr ((hE z).mpr ⟨⟨χ, hzP⟩, hc⟩))))
    exact ((TIdentity.differentiableAt_ofReal_cpow_neg hx z).mul
      ((TIdentity.differentiableAt_Gamma_of_re_pos hz₀).mul
        (analyticAt_D hz₀ hz₁ hne).differentiableAt)).differentiableWithinAt
  have hPole (p : ℂ) (hp : p ∈ S) :
      (inverseKernel q x - fun z ↦ A p / (z - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
    by_cases hp₁ : p = 1
    · subst p
      simpa [A, principalWeight, Gamma_one, cpow_neg, div_eq_mul_inv, mul_comm] using
        inverseKernel_sub_pole_isBigO hx (by norm_num : (0 : ℝ) < (1 : ℂ).re)
          (hasResidue_D_one (q := q))
    · have hpos := hδ.trans (hS p hp).1
      have hr := inverseKernel_sub_pole_isBigO hx hpos (hasResidue_D hpos hp₁ (q := q))
      convert hr using 1
      ext z
      simp only [Pi.sub_apply, A, ite_eq_right hp₁, exceptionalWeight]
      congr 2
      ring
  have hdis : Disjoint W E := by
    rw [Finset.disjoint_left]
    intro p hp he
    obtain ⟨t, _, rfl⟩ := Finset.mem_map.mp hp
    exact ((hE _).mp he).2 (criticalPoint_re t)
  have hEn (p : ℂ) (hp : p ∈ E) : p ≠ 1 := by
    intro eq
    have ht := OffLineZeros.re_lt_one ((hE p).mp hp)
    norm_num [eq] at ht
  have hSn : (1 : ℂ) ∉ W ∪ E := by
    rw [Finset.mem_union, not_or]
    exact ⟨fun h ↦ by obtain ⟨t, _, ht⟩ := Finset.mem_map.mp h
                      exact criticalPoint_ne_one t ht, fun h ↦ hEn 1 h rfl⟩
  rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
    Paper2.M5.rectangleIntegral'_eq_sum_of_simplePoles_rect S A
      (by linarith) hH.le hS hf hPole]
  change ∑ p ∈ insert 1 (W ∪ E), A p = _
  rw [Finset.sum_insert hSn, Finset.sum_union hdis]
  dsimp only [W]
  rw [Finset.sum_map]
  simp only [A, ite_true, e, Function.Embedding.coeFn_mk, criticalPoint_ne_one, ite_false,
    Finset.sum_neg_distrib, sub_eq_add_neg, add_assoc]
  congr 1
  congr 1
  rw [exceptionalTerm, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun p hp ↦ ite_eq_right (hEn p hp)

private theorem tendsto_truncatedOrd {H : ℕ → ℝ} (hH : Tendsto H atTop atTop) :
    Tendsto (fun n ↦ truncatedOrd q (H n)) atTop atTop := by
  classical
  refine tendsto_atTop.mpr fun S ↦ ?_
  let B : ℝ := ∑ t ∈ S, |(t : ℝ)|
  filter_upwards [hH.eventually (eventually_gt_atTop B)] with n hn
  exact fun t ht ↦ mem_truncatedOrd.mpr
    ((Finset.single_le_sum (f := fun t : Ordinates q ↦ |(t : ℝ)|) (fun _ _ ↦ abs_nonneg _) ht).trans_lt hn)

private theorem horizontal_integral_bound {δ x K : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 2)
    (hx : 0 < x) (hK : 0 ≤ K) :
    ∃ C : ℝ, ∀ y : ℝ,
      (∀ z : ℂ, δ ≤ z.re → z.re ≤ 2 → |z.im| = |y| → ‖D q z‖ ≤ K * (1 + |y|) ^ 2) →
      ‖HIntegral (inverseKernel q x) δ 2 y‖ ≤ C * (1 + |y|)⁻¹ := by
  obtain ⟨G, hG⟩ := TIdentity.norm_Gamma_mul_one_add_abs_im_pow_le (a := δ) (a' := 2) hδ 3
  let V : ℝ := x ^ (-δ) + x ^ (-(2 : ℝ))
  have hV : 0 ≤ V := by positivity
  refine ⟨V * K * |G| * |2 - δ|, fun y hy ↦ ?_⟩
  have hpt (b : ℝ) (hb : b ∈ Ι δ 2) :
      ‖inverseKernel q x (b + y * I)‖ ≤ V * K * |G| * (1 + |y|)⁻¹ := by
    rw [uIoc_of_le (by linarith)] at hb
    have hpower : x ^ (-b) ≤ V := by
      rcases le_or_gt 1 x with h | h
      · exact (Real.rpow_le_rpow_of_exponent_le h (neg_le_neg hb.1.le)).trans
          (le_add_of_nonneg_right (by positivity))
      · exact (Real.rpow_le_rpow_of_exponent_ge hx h.le (neg_le_neg hb.2)).trans
          (le_add_of_nonneg_left (by positivity))
    have hGam : ‖Gamma (b + y * I)‖ * (1 + |y|) ^ 3 ≤ |G| :=
      (show ‖Gamma (b + y * I)‖ * (1 + |y|) ^ 3 ≤ G by
        simpa using hG (b + y * I) (by simpa using hb.1.le) (by simpa using hb.2)).trans (le_abs_self G)
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    simp only [inverseKernel, norm_mul, norm_cpow_eq_rpow_re_of_pos hx, neg_re]
    have hre : ((b : ℂ) + y * I).re = b := by simp
    rw [hre]
    calc
      _ ≤ V * (‖Gamma (b + y * I)‖ * (K * (1 + |y|) ^ 2)) * (1 + |y|) := by
        gcongr
        exact hy _ (by simpa using hb.1.le) (by simpa using hb.2) (by simp)
      _ = V * K * (‖Gamma (b + y * I)‖ * (1 + |y|) ^ 3) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hGam (mul_nonneg hV hK)
  calc
    _ ≤ (V * K * |G| * (1 + |y|)⁻¹) * |2 - δ| :=
      intervalIntegral.norm_integral_le_of_norm_le_const hpt
    _ = _ := by ring

set_option maxHeartbeats 800000 in
private theorem tendsto_inverseRect {δ x K : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 2)
    (hx : 0 < x) (hK : 0 ≤ K) {H : ℕ → ℝ} (hHt : Tendsto H atTop atTop)
    (hH₀ : ∀ n, 0 < H n)
    (hBound : ∀ n z, δ ≤ z.re → z.re ≤ 2 → |z.im| = H n → ‖D q z‖ ≤ K * (1 + H n)^2)
    (hI₁ : Integrable fun y : ℝ ↦ inverseKernel q x (2 + y * I))
    (hI₂ : Integrable fun y : ℝ ↦ inverseKernel q x (δ + y * I)) :
    Tendsto (fun n ↦ RectangleIntegral' (inverseKernel q x)
      ((δ : ℂ) - I * H n) (2 + I * H n)) atTop
      (𝓝 (VerticalIntegral' (inverseKernel q x) 2 - VerticalIntegral' (inverseKernel q x) δ)) := by
  obtain ⟨C, hC⟩ := horizontal_integral_bound (q := q) hδ hδ' hx hK
  have hHorizontal (y : ℕ → ℝ) (hy : ∀ n, |y n| = H n) :
      Tendsto (fun n ↦ HIntegral (inverseKernel q x) δ 2 (y n)) atTop (𝓝 0) := by
    have hdecay : Tendsto (fun n : ℕ ↦ C * (1 + H n)⁻¹) atTop (𝓝 0) := by
      simpa using ((tendsto_atTop_add_const_left _ 1 hHt).inv_tendsto_atTop).const_mul C
    apply squeeze_zero_norm' _ hdecay
    exact Eventually.of_forall fun n ↦ by
      rw [← hy n]
      apply hC
      rw [hy n]
      exact hBound n
  have hVert (σ : ℝ) (hi : Integrable fun y : ℝ ↦ inverseKernel q x (σ + y * I)) :
      Tendsto (fun n ↦ VIntegral (inverseKernel q x) σ (-H n) (H n)) atTop
        (𝓝 (VerticalIntegral (inverseKernel q x) σ)) :=
    by simpa only [VIntegral, VerticalIntegral, smul_eq_mul, Function.comp_apply] using
      (intervalIntegral_tendsto_integral hi (tendsto_neg_atTop_atBot.comp hHt) hHt).const_mul I
  have hR := hVert 2 (by simpa only [ofReal_ofNat] using hI₁)
  have hL := hVert δ hI₂
  have hBot := hHorizontal (fun n ↦ -H n) (fun n ↦ by rw [abs_neg, abs_of_pos (hH₀ n)])
  have hTop := hHorizontal H (fun n ↦ abs_of_pos (hH₀ n))
  have hx₁ (n : ℕ) : (((δ : ℂ) - I * H n)).re = δ := by simp
  have hy₁ (n : ℕ) : (((δ : ℂ) - I * H n)).im = -H n := by simp
  have hx₂ (n : ℕ) : ((2 : ℂ) + I * H n).re = 2 := by simp
  have hy₂ (n : ℕ) : ((2 : ℂ) + I * H n).im = H n := by simp
  simp only [RectangleIntegral, hx₁, hy₁, hx₂, hy₂, smul_eq_mul, ← mul_sub]
  simpa only [sub_self, zero_add] using
    (((hBot.sub hTop).add hR).sub hL).const_mul (1 / (2 * Real.pi * I) : ℂ)

private theorem tendsto_inverseRect_residues {E : Finset ℂ} {δ x : ℝ}
    (hδ : 0 < δ) (hδ' : δ < 1 / 2) (hx : 0 < x) {H : ℕ → ℝ} (hHt : Tendsto H atTop atTop)
    (hH₀ : ∀ n, 0 < H n) (hAvoid : ∀ n t, t ∈ Ordinates q → |t| ≠ H n)
    (hE : ∀ p, p ∈ E ↔ p ∈ OffLineZeros q)
    (hleft : ∀ p ∈ E, δ < Complex.re p) (hheight : ∀ n p, p ∈ E → |Complex.im p| < H n) :
    Tendsto (fun n ↦ RectangleIntegral' (inverseKernel q x)
      ((δ : ℂ) - I * H n) (2 + I * H n)) atTop
      (𝓝 (principalWeight q / (x : ℂ) - zeroTerm q x - exceptionalTerm q E x)) := by
  let a (t : Ordinates q) := gammaWeight q t * (x : ℂ) ^ (-criticalPoint t)
  have ha : Summable a := (summable_norm_zeroTerm_unconditional hx).of_norm
  have hSum : Tendsto (fun n ↦ ∑ t ∈ truncatedOrd q (H n), a t) atTop (𝓝 (zeroTerm q x)) :=
    ha.hasSum.comp (tendsto_truncatedOrd (q := q) hHt)
  exact (((tendsto_const_nhds (x := principalWeight q / (x : ℂ))).sub hSum).sub_const
    (exceptionalTerm q E x)).congr fun n ↦
    (rectangle_inverseKernel hδ hδ' (hH₀ n) hx hE hleft (hheight n) (hAvoid n)).symm

/-- The contour moves from two to any positive line left of the critical line.
The crossed residues are the principal pole and the full weighted zero sum. -/
theorem smoothed_explicit_formula_with_exceptions {T : ℝ}
    (hline : ∀ (χ : DirichletCharacter ℂ q) ρ, ρ ∈ primitiveZeros χ →
      T ≤ |ρ.im| → ρ.re = 1 / 2) (hZ3 : Paper2.Z3)
    (hLocal : LogDerivPrimitiveLocal q) {δ x : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 2)
    (hx : 0 < x) {E : Finset ℂ}
    (hE : ∀ p, p ∈ E ↔ p ∈ OffLineZeros q)
    (hleft : ∀ p ∈ E, δ < Complex.re p) :
    (smoothed q x : ℂ) =
      principalWeight q / (x : ℂ) - zeroTerm q x - exceptionalTerm q E x + lineRemainder q δ x := by
  obtain ⟨K, Y₀, hK, hY₀, hYT, hY⟩ := exists_D_horizontal_bounds_of_high_critical hline hZ3 hLocal hδ
  have hSelect (n : ℕ) := hY (Y₀ + (n : ℝ)) (le_add_of_nonneg_right (Nat.cast_nonneg n))
  choose H hH hAvoid hBound using hSelect
  have hHt : Tendsto H atTop atTop :=
    tendsto_atTop_mono (fun n ↦ (hH n).1) (tendsto_atTop_add_const_left _ Y₀ tendsto_natCast_atTop_atTop)
  have hH₀ (n : ℕ) : 0 < H n := by linarith [(hH n).1, Nat.cast_nonneg (α := ℝ) n]
  have heleft : ∀ (χ : DirichletCharacter ℂ q) ρ, ρ ∈ primitiveZeros χ → δ < ρ.re := by
    intro χ ρ hρ
    by_cases h : ρ.re = 1 / 2
    · simpa only [h] using hδ'
    · exact hleft ρ ((hE ρ).mpr ⟨⟨χ, hρ⟩, h⟩)
  have heheight (n : ℕ) (p : ℂ) (hp : p ∈ E) : |p.im| < H n := by
    have he := (hE p).mp hp
    obtain ⟨χ, hχ⟩ := he.1
    have ht : |p.im| < T := lt_of_not_ge (fun h ↦ he.2 (hline χ p hχ h))
    linarith [(hH n).1, Nat.cast_nonneg (α := ℝ) n]
  have hI₁ : Integrable (fun y : ℝ ↦ inverseKernel q x (2 + y * I)) := by
    have h := T0HInf.integrable_inverse_kernel hx (f := fun z ↦ Gamma z * D q z)
      (integrable_Gamma_mul_D_right q (c := 2) (by norm_num))
    simpa only [inverseKernel, ofReal_ofNat] using h
  have hI₂ : Integrable (fun y : ℝ ↦ inverseKernel q x (δ + y * I)) :=
    T0HInf.integrable_inverse_kernel hx (f := fun z ↦ Gamma z * D q z)
      (integrable_Gamma_mul_D_left_of_high_critical hline hZ3 hLocal hδ hδ' heleft)
  have hRect := tendsto_inverseRect hδ hδ' hx hK hHt hH₀ hBound hI₁ hI₂
  have hRes := tendsto_inverseRect_residues hδ hδ' hx hHt hH₀ hAvoid hE hleft heheight
  rw [smoothed_eq_verticalIntegral q (c := 2) (by norm_num) hx, lineRemainder]
  exact sub_eq_iff_eq_add.mp (tendsto_nhds_unique hRect hRes)

theorem smoothed_explicit_formula (hGRH : GRH q) (hZ3 : Paper2.Z3)
    (hLocal : LogDerivPrimitiveLocal q) {δ x : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 2)
    (hx : 0 < x) :
    (smoothed q x : ℂ) =
      principalWeight q / (x : ℂ) - zeroTerm q x + lineRemainder q δ x := by
  have hE (p : ℂ) : p ∈ (∅ : Finset ℂ) ↔ p ∈ OffLineZeros q := by
    simp only [Finset.notMem_empty, false_iff]
    rintro ⟨⟨χ, hχ⟩, hn⟩
    exact hn (hGRH χ p hχ)
  simpa [exceptionalTerm] using smoothed_explicit_formula_with_exceptions
    (T := 0) (fun χ ρ hρ _ ↦ hGRH χ ρ hρ) hZ3 hLocal hδ hδ' hx hE
    (fun p hp ↦ (Finset.notMem_empty p hp).elim)

end GoldbachBoundaries.ResidueClass
