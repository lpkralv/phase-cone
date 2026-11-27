import GoldbachBoundaries.ResidueClass.ExceptionalBinary
import GoldbachBoundaries.ResidueClass.HigherReduction

/-! # Higher Mellin terms with finitely many exceptional zeros -/

noncomputable section

open Complex Filter Set MeasureTheory Topology

namespace GoldbachBoundaries.ResidueClass

variable {q : ℕ} [NeZero q]

private def exceptionalPart (q : ℕ) [NeZero q] (E : Finset ℂ) (x : ℝ) : ℂ :=
  -exceptionalTerm q E x

private def regularResidual (q : ℕ) [NeZero q] (E : Finset ℂ) (x : ℝ) : ℂ :=
  smoothedResidual q x - exceptionalPart q E x

private theorem regularResidual_meas (E : Finset ℂ) :
    AEStronglyMeasurable (regularResidual q E) (volume.restrict (Ioc 0 1)) :=
  ((continuousOn_smoothedResidual (q := q)).mono Ioc_subset_Ioi_self).aestronglyMeasurable
    measurableSet_Ioc |>.sub (aestronglyMeasurable_exceptionalTerm E).neg

private theorem exists_regularResidual_bound {E : Finset ℂ}
    (hE : ∀ ρ, ρ ∈ E ↔ ρ ∈ OffLineZeros q)
    (hZ3 : Paper2.Z3) (hLocal : LogDerivPrimitiveLocal q) {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ < 1 / 2) (hleft : ∀ ρ ∈ E, δ < Complex.re ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Ioc (0 : ℝ) 1,
      ‖regularResidual q E x‖ ≤ C * x ^ (-(1 / 2 : ℝ)) := by
  have hfin : (OffLineZeros q).Finite := by
    convert E.finite_toSet using 1
    ext ρ
    exact (hE ρ).symm
  obtain ⟨T, _, hline⟩ := exists_high_critical hfin
  obtain ⟨K, hK, hR⟩ := norm_lineRemainder_le q δ
  let Z := ∑' t : Ordinates q, ‖gammaWeight q t‖
  have hZ : 0 ≤ Z := tsum_nonneg fun _ ↦ norm_nonneg _
  refine ⟨Z + K, add_nonneg hZ hK, fun x hx ↦ ?_⟩
  have he : regularResidual q E x = -zeroTerm q x + lineRemainder q δ x := by
    rw [regularResidual, exceptionalPart, smoothedResidual,
      smoothed_explicit_formula_with_exceptions hline hZ3 hLocal hδ hδ' hx.1 hE hleft]
    ring
  rw [he, add_mul]
  refine (norm_add_le _ _).trans ?_
  rw [norm_neg]
  exact add_le_add (norm_zeroTerm_le_unconditional hx.1) ((hR x hx.1).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hx.1 hx.2 (by linarith)) hK))

/-- Multiplying the integrand by each exceptional monomial shifts the Mellin
parameter. Iteration gives the finite shift for an arbitrary power. -/
private def shiftExceptionalMellin (q : ℕ) [NeZero q] (E : Finset ℂ) :
    ℕ → (ℂ → ℂ) → ℂ → ℂ
  | 0, f, s => f s
  | n + 1, f, s =>
      ∑ ρ ∈ E, -exceptionalWeight q ρ * shiftExceptionalMellin q E n f (s - ρ)

private theorem integral_exceptional_pow {E : Finset ℂ} {B a : ℝ}
    (hB : ∀ ρ ∈ E, Complex.re ρ ≤ B) {f : ℂ → ℂ} {g : ℝ → ℂ}
    (hf : ∀ s : ℂ, a < s.re →
      IntegrableOn (fun x : ℝ ↦ g x * (x : ℂ) ^ (s - 1)) (Ioc 0 1) ∧
      (∫ x in Ioc (0 : ℝ) 1, g x * (x : ℂ) ^ (s - 1)) = f s)
    (n : ℕ) {s : ℂ} (hs : (n : ℝ) * B + a < s.re) :
    IntegrableOn (fun x : ℝ ↦ exceptionalPart q E x ^ n * g x * (x : ℂ) ^ (s - 1)) (Ioc 0 1) ∧
    (∫ x in Ioc (0 : ℝ) 1, exceptionalPart q E x ^ n * g x * (x : ℂ) ^ (s - 1)) =
      shiftExceptionalMellin q E n f s := by
  induction n generalizing s with
  | zero => simpa [shiftExceptionalMellin] using hf s (by simpa using hs)
  | succ n ih =>
    have hi (ρ : ℂ) (hρ : ρ ∈ E) := ih (s := s - ρ) (by
      simp only [sub_re]
      push_cast at hs
      linarith [hB ρ hρ])
    let F (ρ : ℂ) (x : ℝ) : ℂ :=
      -exceptionalWeight q ρ * (exceptionalPart q E x ^ n * g x * (x : ℂ) ^ ((s - ρ) - 1))
    have he (x : ℝ) (hx : x ∈ Ioc (0 : ℝ) 1) :
        exceptionalPart q E x ^ (n + 1) * g x * (x : ℂ) ^ (s - 1) = ∑ ρ ∈ E, F ρ x := by
      have hX : exceptionalPart q E x =
          ∑ ρ ∈ E, -exceptionalWeight q ρ * (x : ℂ) ^ (-ρ) := by
        rw [exceptionalPart, exceptionalTerm, ← Finset.sum_neg_distrib]
        simp only [neg_mul]
      rw [pow_succ]
      conv_lhs =>
        arg 1
        arg 1
        arg 2
        rw [hX]
      rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro ρ _
      simp only [F, show s - ρ - 1 = -ρ + (s - 1) by ring,
        cpow_add _ _ (ofReal_ne_zero.mpr hx.1.ne')]
      ring
    have hI : ∀ ρ ∈ E, IntegrableOn (F ρ) (Ioc 0 1) :=
      fun ρ hρ ↦ (hi ρ hρ).1.const_mul _
    have hSum : IntegrableOn (fun x ↦ ∑ ρ ∈ E, F ρ x) (Ioc 0 1) := integrable_finsetSum E hI
    refine ⟨hSum.congr_fun (fun x hx ↦ (he x hx).symm) measurableSet_Ioc, ?_⟩
    rw [setIntegral_congr_fun measurableSet_Ioc he, integral_finsetSum E hI, shiftExceptionalMellin]
    apply Finset.sum_congr rfl
    intro ρ hρ
    dsimp only [F]
    rw [integral_const_mul, (hi ρ hρ).2]

private theorem meromorphic_shiftExceptional {E : Finset ℂ} {B a : ℝ}
    (hB : ∀ ρ ∈ E, Complex.re ρ ≤ B) {f : ℂ → ℂ}
    (hf : MeromorphicOn f (halfPlane a)) (n : ℕ) :
    MeromorphicOn (shiftExceptionalMellin q E n f) (halfPlane ((n : ℝ) * B + a)) := by
  induction n with
  | zero =>
    simpa only [Nat.cast_zero, zero_mul, zero_add, shiftExceptionalMellin] using hf
  | succ n ih =>
    intro s hs
    change ((n + 1 : ℕ) : ℝ) * B + a < s.re at hs
    simp only [Nat.cast_succ, shiftExceptionalMellin] at hs ⊢
    apply MeromorphicAt.fun_sum
    intro ρ hρ
    apply (MeromorphicAt.const _ s).mul
    exact (ih (s - ρ) (show (n : ℝ) * B + a < (s - ρ).re by
      rw [sub_re]
      linarith [hB ρ hρ])).comp_analyticAt (g := fun z : ℂ ↦ z - ρ) (by fun_prop)

private theorem meromorphic_shiftExceptional_global (E : Finset ℂ) {f : ℂ → ℂ}
    (hf : Meromorphic f) (n : ℕ) : Meromorphic (shiftExceptionalMellin q E n f) := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    intro s
    apply MeromorphicAt.fun_sum
    intro ρ _
    exact (MeromorphicAt.const _ s).mul ((ih (s - ρ)).comp_analyticAt (g := fun z : ℂ ↦ z - ρ) (by fun_prop))

private def regularMellin (q : ℕ) [NeZero q] (E : Finset ℂ) (s : ℂ) : ℂ :=
  Gamma s * D q s - tailMellin q 1 s - principalWeight q / (s - 1) +
    ∑ ρ ∈ E, exceptionalWeight q ρ / (s - ρ)

private theorem meromorphic_regularMellin (E : Finset ℂ) : Meromorphic (regularMellin q E) := by
  intro s
  have hG := (PhiRProof.meromorphicAt_Gamma s).mul (meromorphic_D (q := q) s)
  have ht := ((differentiable_tailMellin (q := q) le_rfl).analyticAt s).meromorphicAt
  have hu : MeromorphicAt (fun z ↦ principalWeight q / (z - 1)) s :=
    analyticAt_const.meromorphicAt.div (analyticAt_id.sub analyticAt_const).meromorphicAt
  apply ((hG.sub ht).sub hu).add
  exact MeromorphicAt.fun_sum (fun ρ _ ↦
    analyticAt_const.meromorphicAt.div (analyticAt_id.sub analyticAt_const).meromorphicAt)

private theorem integral_regularResidual {E : Finset ℂ} (hE : ∀ ρ ∈ E, Complex.re ρ < 1)
    {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ ↦ regularResidual q E x * (x : ℂ) ^ (s - 1)) (Ioc 0 1) ∧
    (∫ x in Ioc (0 : ℝ) 1, regularResidual q E x * (x : ℂ) ^ (s - 1)) =
      regularMellin q E s := by
  obtain ⟨hF, hFv⟩ := mellin_smoothed q hs
  have hF' : IntegrableOn (fun x : ℝ ↦ (smoothed q x : ℂ) * (x : ℂ) ^ (s - 1)) (Ioi 0) := by
    simpa only [MellinConvergent, smul_eq_mul, mul_comm] using hF
  have hFv' : (∫ x in Ioi (0 : ℝ), (smoothed q x : ℂ) * (x : ℂ) ^ (s - 1)) =
      Gamma s * D q s := by simpa only [mellin, smul_eq_mul, mul_comm] using hFv
  have hFs := hF'.mono_set (show Ioc (0 : ℝ) 1 ⊆ Ioi 0 from Ioc_subset_Ioi_self)
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 from zero_le_one),
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hFs
      (hF'.mono_set (Ioi_subset_Ioi zero_le_one))] at hFv'
  obtain ⟨hU, hUv⟩ := integral_monomial (a := principalWeight q) (ρ := 1) (s := s) (by simpa using hs)
  obtain ⟨hX, hXv⟩ := integral_finset_mellin
    (f := fun ρ x ↦ exceptionalWeight q ρ * (x : ℂ) ^ (-ρ)) (s := s) (S := E)
    (fun ρ hρ ↦ integral_monomial ((hE ρ hρ).trans hs))
  have he (x : ℝ) (hx : x ∈ Ioc (0 : ℝ) 1) :
      regularResidual q E x * (x : ℂ) ^ (s - 1) =
      ((smoothed q x : ℂ) * (x : ℂ) ^ (s - 1) -
        (principalWeight q * (x : ℂ) ^ (-(1 : ℂ))) * (x : ℂ) ^ (s - 1)) +
      (∑ ρ ∈ E, exceptionalWeight q ρ * (x : ℂ) ^ (-ρ)) * (x : ℂ) ^ (s - 1) := by
    simp only [regularResidual, exceptionalPart, exceptionalTerm, smoothedResidual, cpow_neg,
      cpow_one, div_eq_mul_inv]
    ring
  refine ⟨((hFs.sub hU).add hX).congr_fun (fun x hx ↦ (he x hx).symm) measurableSet_Ioc, ?_⟩
  have hAdd := integral_add (hFs.sub hU) hX
  have hSub := integral_sub hFs hU
  simp only [Pi.sub_apply] at hAdd hSub
  rw [setIntegral_congr_fun measurableSet_Ioc he, hAdd, hSub,
    hUv, hXv, regularMellin, ← hFv']
  simp only [tailMellin, pow_one]
  ring

private def residualMoment (q : ℕ) [NeZero q] (E : Finset ℂ) (k : ℕ) (s : ℂ) : ℂ :=
  match k with
  | 0 => 1 / s
  | 1 => regularMellin q E s
  | k + 2 => ∫ x in Ioc (0 : ℝ) 1, regularResidual q E x ^ (k + 2) * (x : ℂ) ^ (s - 1)

private theorem norm_residual_pow_le {E : Finset ℂ} {C : ℝ}
    (hb : ∀ x ∈ Ioc (0 : ℝ) 1, ‖regularResidual q E x‖ ≤ C * x ^ (-(1 / 2 : ℝ)))
    (k : ℕ) (x : ℝ) (hx : x ∈ Ioc (0 : ℝ) 1) :
    ‖regularResidual q E x ^ k‖ ≤ C ^ k * x ^ (-((k : ℝ) / 2)) := by
  rw [norm_pow]
  refine (pow_le_pow_left₀ (norm_nonneg _) (hb x hx) k).trans_eq ?_
  rw [mul_pow, ← Real.rpow_mul_natCast hx.1.le]
  congr 2
  ring

private theorem integral_residualMoment {E : Finset ℂ} (hE : ∀ ρ ∈ E, Complex.re ρ < 1) {C : ℝ}
    (hb : ∀ x ∈ Ioc (0 : ℝ) 1, ‖regularResidual q E x‖ ≤ C * x ^ (-(1 / 2 : ℝ)))
    (k : ℕ) (s : ℂ) (hs : (k : ℝ) < s.re) :
    IntegrableOn (fun x : ℝ ↦ regularResidual q E x ^ k * (x : ℂ) ^ (s - 1)) (Ioc 0 1) ∧
    (∫ x in Ioc (0 : ℝ) 1, regularResidual q E x ^ k * (x : ℂ) ^ (s - 1)) =
      residualMoment q E k s := by
  cases k with
  | zero => simpa [residualMoment] using integral_monomial (a := 1) (ρ := 0) (s := s) (by simpa using hs)
  | succ k =>
    cases k with
    | zero => simpa [residualMoment] using integral_regularResidual (q := q) hE (by simpa using hs)
    | succ k =>
      exact ⟨Phi2Proof.C_integrableOn_mellin ((regularResidual_meas E).pow _) (norm_residual_pow_le hb _)
        (by linarith [Nat.cast_nonneg (α := ℝ) (k + 1 + 1)]), rfl⟩

private theorem meromorphic_residualMoment {E : Finset ℂ} {C : ℝ}
    (hb : ∀ x ∈ Ioc (0 : ℝ) 1, ‖regularResidual q E x‖ ≤ C * x ^ (-(1 / 2 : ℝ))) (k : ℕ) :
    MeromorphicOn (residualMoment q E k) (halfPlane ((k : ℝ) / 2)) := by
  cases k with
  | zero =>
    exact fun s _ ↦ analyticAt_const.meromorphicAt.div analyticAt_id.meromorphicAt
  | succ k =>
    cases k with
    | zero => exact fun s _ ↦ meromorphic_regularMellin E s
    | succ k =>
      exact fun s hs ↦ ((TIdentity.differentiableOn_integral_Ioc_cpow ((regularResidual_meas E).pow _)
        (norm_residual_pow_le hb _)).analyticAt ((isOpen_halfPlane _).mem_nhds hs)).meromorphicAt

private def mixedHigherMellin (q : ℕ) [NeZero q] (E : Finset ℂ) (r : ℕ) (s : ℂ) : ℂ :=
  ∑ j ∈ Finset.Ico 3 (r + 1), ∑ k ∈ Finset.range (j + 1),
    ((r.choose j : ℂ) * principalWeight q ^ (r - j) * (j.choose k : ℂ)) *
      shiftExceptionalMellin q E (j - k) (residualMoment q E k) (s - r + j)

private theorem mixed_abscissa {r j k : ℕ} (hjr : j ≤ r) (hj : 3 ≤ j)
    (hkj : k ≤ j) (hk : 2 ≤ k) {B : ℝ} (hB : B < 1) :
    ((r - j : ℕ) : ℝ) + ((j - k : ℕ) : ℝ) * B + (k : ℝ) / 2 ≤
      (r : ℝ) - 1 - min (1 - B) (1 / 2) := by
  have hp : (0 : ℝ) ≤ ((j - k : ℕ) : ℝ) := Nat.cast_nonneg _
  have hs : (((j - k : ℕ) : ℝ) + (k : ℝ)) = j := by rw [Nat.cast_sub hkj]; ring
  rw [Nat.cast_sub hjr]
  by_cases he : k = 2
  · have hp' : (1 : ℝ) ≤ ((j - k : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ j - k by omega)
    subst k
    norm_num only [Nat.cast_ofNat] at hs ⊢
    nlinarith [mul_nonneg (sub_nonneg.mpr hp') (sub_nonneg.mpr hB.le),
      min_le_left (1 - B) (1 / 2)]
  · have hk' : (3 : ℝ) ≤ k := by exact_mod_cast (show 3 ≤ k by omega)
    nlinarith [mul_nonneg hp (sub_nonneg.mpr hB.le), min_le_right (1 - B) (1 / 2)]

private theorem meromorphic_mixedHigherMellin {E : Finset ℂ} {B C : ℝ}
    (hB : B < 1) (hE : ∀ ρ ∈ E, Complex.re ρ ≤ B)
    (hb : ∀ x ∈ Ioc (0 : ℝ) 1, ‖regularResidual q E x‖ ≤ C * x ^ (-(1 / 2 : ℝ)))
    (r : ℕ) : MeromorphicOn (mixedHigherMellin q E r)
      (halfPlane ((r : ℝ) - 1 - min (1 - B) (1 / 2))) := by
  intro s hs
  change (r : ℝ) - 1 - min (1 - B) (1 / 2) < s.re at hs
  apply MeromorphicAt.fun_sum
  intro j hj
  apply MeromorphicAt.fun_sum
  intro k hk
  apply (MeromorphicAt.const _ s).mul
  have ha : AnalyticAt ℂ (fun z : ℂ ↦ z - r + j) s := by fun_prop
  by_cases h₀ : k = 0
  · subst k
    have hm : Meromorphic (residualMoment q E 0) :=
      fun z ↦ analyticAt_const.meromorphicAt.div analyticAt_id.meromorphicAt
    exact (meromorphic_shiftExceptional_global E hm _ _).comp_analyticAt ha
  by_cases h₁ : k = 1
  · subst k
    exact (meromorphic_shiftExceptional_global E (meromorphic_regularMellin (q := q) E) _ _).comp_analyticAt ha
  have hjr : j ≤ r := by have := (Finset.mem_Ico.mp hj).2; omega
  have hkj : k ≤ j := by have := Finset.mem_range.mp hk; omega
  have hm := mixed_abscissa hjr (Finset.mem_Ico.mp hj).1 hkj (by omega) hB
  rw [Nat.cast_sub hjr] at hm
  have hs' : (s - r + j) ∈ halfPlane (((j - k : ℕ) : ℝ) * B + (k : ℝ) / 2) := by
    change _ < (s - r + j).re
    simp only [add_re, sub_re, natCast_re]
    linarith
  exact (meromorphic_shiftExceptional hE (meromorphic_residualMoment hb k) _ _ hs').comp_analyticAt (g := fun z : ℂ ↦ z - r + j) ha

private theorem integral_mixedHigherMellin {E : Finset ℂ} {B C : ℝ}
    (hB : B < 1) (hE : ∀ ρ ∈ E, Complex.re ρ ≤ B)
    (hb : ∀ x ∈ Ioc (0 : ℝ) 1, ‖regularResidual q E x‖ ≤ C * x ^ (-(1 / 2 : ℝ)))
    {r : ℕ} {s : ℂ} (hs : (r : ℝ) < s.re) :
    IntegrableOn (fun x : ℝ ↦ higherTail q r x * (x : ℂ) ^ (s - 1)) (Ioc 0 1) ∧
    (∫ x in Ioc (0 : ℝ) 1, higherTail q r x * (x : ℂ) ^ (s - 1)) =
      mixedHigherMellin q E r s := by
  let f (j k : ℕ) (x : ℝ) : ℂ :=
    (r.choose j : ℂ) * principalTerm q x ^ (r - j) * (j.choose k : ℂ) *
      (exceptionalPart q E x ^ (j - k) * regularResidual q E x ^ k)
  have hi (j : ℕ) (hj : j ∈ Finset.Ico 3 (r + 1)) (k : ℕ) (hk : k ∈ Finset.range (j + 1)) :
      IntegrableOn (fun x : ℝ ↦ f j k x * (x : ℂ) ^ (s - 1)) (Ioc 0 1) ∧
      (∫ x in Ioc (0 : ℝ) 1, f j k x * (x : ℂ) ^ (s - 1)) =
        ((r.choose j : ℂ) * principalWeight q ^ (r - j) * (j.choose k : ℂ)) *
          shiftExceptionalMellin q E (j - k) (residualMoment q E k) (s - r + j) := by
    have hjr : j ≤ r := by have := (Finset.mem_Ico.mp hj).2; omega
    have hkj : k ≤ j := by have := Finset.mem_range.mp hk; omega
    have hp : ((j - k : ℕ) : ℝ) * B ≤ ((j - k : ℕ) : ℝ) :=
      mul_le_of_le_one_right (Nat.cast_nonneg _) hB.le
    obtain ⟨h, hv⟩ := integral_exceptional_pow (q := q) hE
      (integral_residualMoment (fun ρ hρ ↦ (hE ρ hρ).trans_lt hB) hb k) (j - k)
      (s := s - r + j) (by simp only [add_re, sub_re, natCast_re]; rw [Nat.cast_sub hkj] at hp ⊢; linarith)
    let c : ℂ := (r.choose j : ℂ) * principalWeight q ^ (r - j) * (j.choose k : ℂ)
    have he (x : ℝ) (hx : x ∈ Ioc (0 : ℝ) 1) :
        f j k x * (x : ℂ) ^ (s - 1) = c *
          (exceptionalPart q E x ^ (j - k) * regularResidual q E x ^ k *
            (x : ℂ) ^ (s - r + j - 1)) := by
      have he' : s - r + j - 1 = (s - 1) - ((r - j : ℕ) : ℂ) := by rw [Nat.cast_sub hjr]; ring
      simp only [f, c, principalTerm, div_pow, he',
        cpow_sub _ _ (ofReal_ne_zero.mpr hx.1.ne'), cpow_natCast]
      ring
    have h' : IntegrableOn (fun x : ℝ ↦ c *
          (exceptionalPart q E x ^ (j - k) * regularResidual q E x ^ k *
            (x : ℂ) ^ (s - r + j - 1))) (Ioc 0 1) := h.const_mul c
    refine ⟨h'.congr_fun (fun x hx ↦ (he x hx).symm) measurableSet_Ioc, ?_⟩
    rw [setIntegral_congr_fun measurableSet_Ioc he, integral_const_mul, hv]
  obtain ⟨hI, hIv⟩ := integral_finset_mellin (S := Finset.Ico 3 (r + 1))
    (f := fun j x ↦ ∑ k ∈ Finset.range (j + 1), f j k x)
    (fun j hj ↦ integral_finset_mellin (hi j hj))
  have he (x : ℝ) : higherTail q r x =
      ∑ j ∈ Finset.Ico 3 (r + 1), ∑ k ∈ Finset.range (j + 1), f j k x := by
    apply Finset.sum_congr rfl
    intro j _
    have he' : smoothedResidual q x = regularResidual q E x + exceptionalPart q E x := by
      unfold regularResidual
      ring
    rw [he', add_pow, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    dsimp [f]
    ring
  exact ⟨hI.congr_fun (fun x _ ↦ by rw [he x]) measurableSet_Ioc,
    (setIntegral_congr_fun measurableSet_Ioc fun x _ ↦ by rw [he x]).trans hIv⟩

/-- All higher class-one series have the translated binary boundary. -/
theorem phiR_natural_boundary_finite_exceptions (hq : 2 ≤ q)
    (hE : (OffLineZeros q).Finite) (hZ3 : Paper2.Z3) (hGap : Paper2.ZLittlewood)
    (hStir : Phi2HInf.StirlingStrip) {r : ℕ} (hr : 2 ≤ r) :
    (∃ F : ℂ → ℂ, MeromorphicOn F (halfPlane ((r : ℝ) - 1)) ∧
      EqOn F (PhiR q r) (halfPlane r)) ∧
    (∀ F : ℂ → ℂ, MeromorphicOn F (halfPlane ((r : ℝ) - 1)) →
      F =ᶠ[codiscreteWithin (halfPlane r)] PhiR q r →
      IsNaturalBoundary F (halfPlane ((r : ℝ) - 1)) (lineAt ((r : ℝ) - 1))) := by
  classical
  obtain ⟨⟨F, hF, hInit⟩, hboundary⟩ := phi2_natural_boundary_finite_exceptions hq hE hZ3 hGap hStir
  obtain ⟨B, δ, _, hB, hδ, hδ', _, hstrip⟩ := exists_exception_strip hE
  let E := hE.toFinset
  have he (ρ : ℂ) : ρ ∈ E ↔ ρ ∈ OffLineZeros q := hE.mem_toFinset
  obtain ⟨C, _, hb⟩ := exists_regularResidual_bound he hZ3
    (logDerivPrimitiveLocal_of_finite_exceptions hE) hδ hδ' (fun ρ hρ ↦ (hstrip ρ ((he ρ).mp hρ)).1)
  have hupper (ρ : ℂ) (hρ : ρ ∈ E) : ρ.re ≤ B := (hstrip ρ ((he ρ).mp hρ)).2
  apply naturalBoundary_higher_of_mellin hr
    (sub_lt_self _ (lt_min (sub_pos.mpr hB) (by norm_num)))
    (meromorphic_mixedHigherMellin hB hupper hb r)
    (fun _ hs ↦ integral_mixedHigherMellin hB hupper hb hs) hF hInit
  apply hboundary F hF
  filter_upwards [self_mem_codiscreteWithin (halfPlane 2)] with s hs using hInit hs

end GoldbachBoundaries.ResidueClass
