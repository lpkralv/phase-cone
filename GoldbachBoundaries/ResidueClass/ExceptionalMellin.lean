import GoldbachBoundaries.ResidueClass.ExceptionalZeros
import GoldbachBoundaries.ResidueClass.CauchySquare
import GoldbachBoundaries.Phi2HInf.Fill.cauchy_meromorphic

/-! # Mellin transforms of the exceptional pair terms -/

noncomputable section

open Complex Set Metric MeasureTheory

namespace GoldbachBoundaries.ResidueClass

variable {q : ℕ} [NeZero q]

theorem aestronglyMeasurable_exceptionalTerm (E : Finset ℂ) :
    AEStronglyMeasurable (exceptionalTerm q E) (volume.restrict (Ioc 0 1)) := by
  unfold exceptionalTerm
  convert (Finset.aestronglyMeasurable_sum E fun ρ _ ↦
    (Phi2Proof.C_cpow_meas (-ρ)).const_mul (exceptionalWeight q ρ)) using 1
  funext x
  rw [Finset.sum_apply]

theorem norm_exceptionalTerm_le {E : Finset ℂ} {B : ℝ} (hB : ∀ ρ ∈ E, Complex.re ρ ≤ B)
    {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) :
    ‖exceptionalTerm q E x‖ ≤ (∑ ρ ∈ E, ‖exceptionalWeight q ρ‖) * x ^ (-B) := by
  rw [exceptionalTerm, Finset.sum_mul]
  apply (norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ hρ ↦ ?_)
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx.1, neg_re]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge hx.1 hx.2 (neg_le_neg (hB ρ hρ))) (norm_nonneg _)

/-- Integration and its value travel together when a finite Mellin sum is expanded. -/
theorem integral_finset_mellin {ι : Type*} {S : Finset ι} {f : ι → ℝ → ℂ}
    {g : ι → ℂ} {s : ℂ}
    (h : ∀ i ∈ S,
      IntegrableOn (fun x : ℝ ↦ f i x * (x : ℂ) ^ (s - 1)) (Ioc 0 1) ∧
      (∫ x in Ioc (0 : ℝ) 1, f i x * (x : ℂ) ^ (s - 1)) = g i) :
    IntegrableOn (fun x : ℝ ↦ (∑ i ∈ S, f i x) * (x : ℂ) ^ (s - 1)) (Ioc 0 1) ∧
    (∫ x in Ioc (0 : ℝ) 1, (∑ i ∈ S, f i x) * (x : ℂ) ^ (s - 1)) = ∑ i ∈ S, g i := by
  simp only [Finset.sum_mul]
  refine ⟨integrable_finsetSum S (fun i hi ↦ (h i hi).1), ?_⟩
  rw [integral_finsetSum S (fun i hi ↦ (h i hi).1)]
  exact Finset.sum_congr rfl fun i hi ↦ (h i hi).2

theorem integral_monomial {s ρ a : ℂ} (hs : ρ.re < s.re) :
    IntegrableOn (fun x : ℝ ↦ (a * (x : ℂ) ^ (-ρ)) * (x : ℂ) ^ (s - 1)) (Ioc 0 1) ∧
    (∫ x in Ioc (0 : ℝ) 1, (a * (x : ℂ) ^ (-ρ)) * (x : ℂ) ^ (s - 1)) = a / (s - ρ) := by
  have h := Phi2HInf.integral_cpow_family (fun _ : Unit ↦ a) (fun _ : Unit ↦ ρ)
    Summable.of_finite (fun _ ↦ le_rfl) hs
  simpa using h

private def mixedCauchy (q : ℕ) [NeZero q] (ρ s : ℂ) : ℂ :=
  ∑' t : Ordinates q, exceptionalWeight q ρ * gammaWeight q t / (s - (ρ + criticalPoint t))

/-- Both orders of each mixed pair and each ordered exceptional pair. -/
def exceptionalCauchy (q : ℕ) [NeZero q] (E : Finset ℂ) (s : ℂ) : ℂ :=
  2 * (∑ ρ ∈ E, mixedCauchy q ρ s) +
    ∑ ρ ∈ E, ∑ ξ ∈ E, exceptionalWeight q ρ * exceptionalWeight q ξ / (s - (ρ + ξ))

private theorem meromorphic_mixedCauchy (ρ : ℂ) : Meromorphic (mixedCauchy q ρ) := by
  classical
  intro s
  let M := |(s - ρ).im| + 2
  have hf : {t : Ordinates q | |(t : ℝ)| ≤ M}.Finite :=
    ((finite_Ordinates_inter (q := q) (-M) M).preimage Subtype.val_injective.injOn).subset
      fun t ht ↦ ⟨t.2, abs_le.mp ht⟩
  apply Phi2HInf.meromorphicAt_cauchy_of_gap
    (fun t : Ordinates q ↦ exceptionalWeight q ρ * gammaWeight q t)
    (fun t ↦ ρ + criticalPoint t) (by
      simp only [norm_mul]
      exact (summable_norm_gammaWeight_unconditional q).mul_left _) one_pos one_pos hf.toFinset
  intro w hw t ht
  by_contra! hn
  apply ht
  rw [hf.mem_toFinset]
  have h₁ := (abs_im_le_norm (w - (ρ + criticalPoint t))).trans_lt hn
  have h₂ := (abs_im_le_norm (w - s)).trans_lt (show ‖w - s‖ < 1 from
    by simpa only [mem_ball, dist_eq_norm] using hw)
  simp only [sub_im, add_im, criticalPoint_im, abs_lt] at h₁ h₂
  change |(t : ℝ)| ≤ M
  rw [abs_le]
  dsimp [M]
  constructor <;> linarith [le_abs_self (s.im - ρ.im), neg_le_abs (s.im - ρ.im)]

theorem meromorphic_exceptionalCauchy (E : Finset ℂ) : Meromorphic (exceptionalCauchy q E) := by
  intro s
  apply (MeromorphicAt.const _ s).mul (MeromorphicAt.fun_sum fun ρ _ ↦
    meromorphic_mixedCauchy (q := q) ρ s) |>.add
  apply MeromorphicAt.fun_sum
  intro ρ _
  apply MeromorphicAt.fun_sum
  intro ξ _
  exact analyticAt_const.meromorphicAt.div (analyticAt_id.sub analyticAt_const).meromorphicAt

private theorem integral_mixed {ρ s : ℂ} (hρ : ρ.re < 1) (hs : 2 < s.re) :
    IntegrableOn (fun x : ℝ ↦ (exceptionalWeight q ρ * (x : ℂ) ^ (-ρ) * zeroTerm q x) *
      (x : ℂ) ^ (s - 1)) (Ioc 0 1) ∧
    (∫ x in Ioc (0 : ℝ) 1, (exceptionalWeight q ρ * (x : ℂ) ^ (-ρ) * zeroTerm q x) *
      (x : ℂ) ^ (s - 1)) = mixedCauchy q ρ s := by
  have h := Phi2HInf.integral_cpow_family
    (fun t : Ordinates q ↦ exceptionalWeight q ρ * gammaWeight q t)
    (fun t ↦ ρ + criticalPoint t) (by
      simp only [norm_mul]
      exact (summable_norm_gammaWeight_unconditional q).mul_left _)
    (r := 2) (fun t ↦ by simp only [add_re, criticalPoint_re]; linarith) hs
  have heq (x : ℝ) (hx : x ∈ Ioc (0 : ℝ) 1) :
      exceptionalWeight q ρ * (x : ℂ) ^ (-ρ) * zeroTerm q x =
      ∑' t : Ordinates q, (exceptionalWeight q ρ * gammaWeight q t) *
        (x : ℂ) ^ (-(ρ + criticalPoint t)) := by
    rw [zeroTerm, ← tsum_mul_left]
    apply tsum_congr
    intro t
    rw [neg_add, cpow_add _ _ (ofReal_ne_zero.mpr hx.1.ne')]
    ring
  exact ⟨h.1.congr_fun (fun x hx ↦ by rw [heq x hx]) measurableSet_Ioc,
    (setIntegral_congr_fun measurableSet_Ioc fun x hx ↦ by rw [heq x hx]).trans h.2⟩

theorem integral_zeroTerm_add_exceptional_sq {E : Finset ℂ} {s : ℂ}
    (hE : ∀ ρ ∈ E, Complex.re ρ < 1) (hs : 2 < s.re) :
    IntegrableOn (fun x : ℝ ↦ (zeroTerm q x + exceptionalTerm q E x)^2 *
      (x : ℂ) ^ (s - 1)) (Ioc 0 1) ∧
    (∫ x in Ioc (0 : ℝ) 1, (zeroTerm q x + exceptionalTerm q E x)^2 * (x : ℂ) ^ (s - 1)) =
      cauchySquare q s + exceptionalCauchy q E s := by
  let a (ρ : ℂ) (x : ℝ) := exceptionalWeight q ρ * (x : ℂ) ^ (-ρ)
  obtain ⟨hZ, hZv⟩ := integral_zeroTerm_sq_unconditional (q := q) (show 1 < s.re by linarith)
  obtain ⟨hM, hMv⟩ := integral_finset_mellin (S := E) (f := fun ρ x ↦ a ρ x * zeroTerm q x)
    (fun ρ hρ ↦ integral_mixed (q := q) (hE ρ hρ) hs)
  obtain ⟨hX, hXv⟩ := integral_finset_mellin (S := E)
    (f := fun ρ x ↦ ∑ ξ ∈ E, a ρ x * a ξ x) fun ρ hρ ↦
    integral_finset_mellin (S := E) (f := fun ξ x ↦ a ρ x * a ξ x) fun ξ hξ ↦ by
      have h := integral_monomial (ρ := ρ + ξ) (a := exceptionalWeight q ρ * exceptionalWeight q ξ)
        (s := s) (by simp only [add_re]; linarith [hE ρ hρ, hE ξ hξ])
      have he (x : ℝ) (hx : x ∈ Ioc (0 : ℝ) 1) :
          a ρ x * a ξ x = exceptionalWeight q ρ * exceptionalWeight q ξ * (x : ℂ) ^ (-(ρ + ξ)) := by
        simp only [a, neg_add, cpow_add _ _ (ofReal_ne_zero.mpr hx.1.ne')]
        ring
      exact ⟨h.1.congr_fun (fun x hx ↦ by rw [he x hx]) measurableSet_Ioc,
        (setIntegral_congr_fun measurableSet_Ioc fun x hx ↦ by rw [he x hx]).trans h.2⟩
  have he (x : ℝ) :
      (zeroTerm q x + exceptionalTerm q E x)^2 * (x : ℂ) ^ (s - 1) =
        (zeroTerm q x ^ 2 * (x : ℂ) ^ (s - 1) +
          2 * ((∑ ρ ∈ E, a ρ x * zeroTerm q x) * (x : ℂ) ^ (s - 1))) +
        (∑ ρ ∈ E, ∑ ξ ∈ E, a ρ x * a ξ x) * (x : ℂ) ^ (s - 1) := by
    rw [← Finset.sum_mul, ← Finset.sum_mul_sum]
    change (zeroTerm q x + ∑ ρ ∈ E, a ρ x)^2 * _ = _
    ring
  refine ⟨((hZ.add (hM.const_mul 2)).add hX).congr_fun (fun x _ ↦ (he x).symm) measurableSet_Ioc, ?_⟩
  have hAdd := integral_add (hZ.add (hM.const_mul 2)) hX
  have hAdd' := integral_add hZ (hM.const_mul 2)
  simp only [Pi.add_apply] at hAdd hAdd'
  rw [setIntegral_congr_fun measurableSet_Ioc (fun x _ ↦ he x),
    hAdd, hAdd', integral_const_mul, hZv, hMv, hXv, exceptionalCauchy]
  ring

end GoldbachBoundaries.ResidueClass
