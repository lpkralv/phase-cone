import GoldbachBoundaries.ResidueClass.Zeros
import GoldbachBoundaries.ZetaRealNonvanishing
import Mathlib.NumberTheory.LSeries.SumCoeff

/-! # Partial summation for the Jensen estimate -/

noncomputable section

open Complex Finset Filter MeasureTheory Set Asymptotics
open scoped Topology Fin.NatCast

namespace GoldbachBoundaries.ResidueClass

variable {m : ℕ} [NeZero m] {ψ : DirichletCharacter ℂ m}

/-- A nonprincipal character sums to zero over a complete period of natural numbers. -/
theorem sum_character_range_period (hψ : ψ ≠ 1) :
    ∑ k ∈ range m, ψ (k : ZMod m) = 0 := by
  rw [← Fin.sum_univ_eq_sum_range (fun k : ℕ ↦ ψ (k : ZMod m))]
  calc
    _ = ∑ a : ZMod m, ψ a := by
      refine Fintype.sum_equiv (ZMod.finEquiv m).toEquiv _ _ fun k ↦ ?_
      cases m with
      | zero => exact (NeZero.ne 0 rfl).elim
      | succ m =>
        change ψ ((k.val : ℕ) : Fin (m + 1)) = ψ k
        rw [Fin.cast_val_eq_self]
    _ = 0 := ψ.sum_eq_zero_of_ne_one hψ

/-- Nonprincipal character sums are bounded by the length of a period. -/
theorem norm_sum_character_Icc_le (hψ : ψ ≠ 1) (n : ℕ) :
    ‖∑ k ∈ Finset.Icc 1 n, ψ (k : ZMod m)‖ ≤ (m : ℝ) := by
  let : Nontrivial (ZMod m) := ZMod.nontrivial_iff.mpr (by
    intro h
    subst m
    exact hψ (Subsingleton.elim _ _))
  have hzero : ψ 0 = 0 := ψ.map_zero
  have hsplit : (∑ k ∈ Finset.Icc 1 n, ψ (k : ZMod m)) =
      ∑ k ∈ range (n + 1), ψ (k : ZMod m) := by
    rw [Nat.range_succ_eq_Icc_zero, ← Finset.insert_Icc_add_one_left_eq_Icc n.zero_le,
      sum_insert (by simp), Nat.cast_zero, hzero, zero_add, zero_add]
  have hblock (j : ℕ) : ∑ k ∈ range (m * j), ψ (k : ZMod m) = 0 := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Nat.mul_succ, sum_range_add, ih, zero_add]
      simpa [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self]
        using sum_character_range_period hψ
  rw [hsplit]
  conv_lhs => rw [← Nat.div_add_mod (n + 1) m, sum_range_add, hblock, zero_add]
  calc
    _ ≤ ∑ _k ∈ range ((n + 1) % m), (1 : ℝ) :=
      (norm_sum_le _ _).trans (sum_le_sum fun _ _ ↦ ψ.norm_le_one _)
    _ ≤ (m : ℝ) := by
      simpa using (show (((n + 1) % m : ℕ) : ℝ) ≤ m by
        exact_mod_cast (Nat.mod_lt _ (NeZero.pos m)).le)

private theorem differentiableAt_bounded_mellin {g : ℝ → ℂ} {B : ℝ}
    (hg : Measurable g) (hB : 0 ≤ B) (hbound : ∀ t, ‖g t‖ ≤ B) {s : ℂ} (hs : s.re < 0) :
    DifferentiableAt ℂ (fun z : ℂ ↦ ∫ t in Ioi (1 : ℝ), g t * (t : ℂ) ^ (z - 1)) s := by
  let f : ℝ → ℂ := (Ioi (1 : ℝ)).indicator g
  have hfn (t : ℝ) : ‖f t‖ ≤ B := by
    by_cases ht : t ∈ Ioi (1 : ℝ)
    · simpa [f, indicator_of_mem ht] using hbound t
    · simpa [f, indicator_of_notMem ht] using hB
  have hcont : Continuous (fun _ : ℝ ↦ B) := continuous_const
  have hlocal : LocallyIntegrableOn f (Ioi 0) :=
    (hcont.locallyIntegrable.locallyIntegrableOn _).mono
      (hg.indicator measurableSet_Ioi).aestronglyMeasurable
      (Eventually.of_forall (fun t ↦ (hfn t).trans (Real.le_norm_self B)))
  have htop : f =O[atTop] (fun t : ℝ ↦ t ^ (-(0 : ℝ))) :=
    IsBigO.of_bound B (Eventually.of_forall (by simpa using hfn))
  have hbot : f =O[𝓝[>] 0] (fun t : ℝ ↦ t ^ (-(s.re - 1))) := by
    refine IsBigO.of_bound 0 ?_
    filter_upwards [(eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
      nhdsWithin_le_nhds] with t ht
    simp [f, indicator_of_notMem (show t ∉ Ioi (1 : ℝ) from not_lt_of_gt ht)]
  have heq : (fun z : ℂ ↦ ∫ t in Ioi (1 : ℝ), g t * (t : ℂ) ^ (z - 1)) = mellin f := by
    funext z
    rw [mellin]
    simp_rw [f, ← indicator_smul, setIntegral_indicator measurableSet_Ioi,
      inter_eq_right.mpr (Ioi_subset_Ioi (show (0 : ℝ) ≤ 1 by norm_num)), smul_eq_mul, mul_comm]
  rw [heq]
  exact mellin_differentiableAt_of_isBigO_rpow hlocal htop hs hbot (by linarith)

private theorem norm_bounded_mellin {g : ℝ → ℂ} {B : ℝ}
    (hbound : ∀ t, ‖g t‖ ≤ B) {s : ℂ} (hs : 0 < s.re) :
    ‖∫ t in Ioi (1 : ℝ), g t * (t : ℂ) ^ (-(s + 1))‖ ≤ B / s.re := by
  have hint : IntegrableOn (fun t : ℝ ↦ B * t ^ (-s.re - 1)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -s.re - 1 < -1) one_pos).const_mul B
  calc
    _ ≤ ∫ t in Ioi (1 : ℝ), B * t ^ (-s.re - 1) := by
      refine norm_integral_le_of_norm_le hint ((ae_restrict_iff' measurableSet_Ioi).mpr
        (Eventually.of_forall fun t (ht : 1 < t) ↦ ?_))
      rw [norm_mul, norm_cpow_eq_rpow_re_of_pos (one_pos.trans ht), neg_re, add_re, one_re,
        neg_add_rev, add_comm (-1 : ℝ), ← sub_eq_add_neg]
      gcongr
      exact hbound t
    _ = B / s.re := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith : -s.re - 1 < -1) one_pos]
      simp [show -s.re - 1 + 1 = -s.re by ring, div_eq_mul_inv]

/-- Partial summation continues the Dirichlet series of a nonprincipal
character to the whole positive half-plane. -/
theorem lFunction_eq_character_integral (hψ : ψ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    ψ.LFunction s = s * ∫ t in Ioi (1 : ℝ), (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ψ (k : ZMod m)) *
      (t : ℂ) ^ (-(s + 1)) := by
  let g : ℝ → ℂ := fun t ↦ ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ψ (k : ZMod m)
  let H : ℂ → ℂ := fun z ↦ z * ∫ t in Ioi (1 : ℝ), g t * (t : ℂ) ^ (-(z + 1))
  have hg : Measurable g :=
    (measurable_of_countable (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, ψ (k : ZMod m))).comp Nat.measurable_floor
  have hdiff (z : ℂ) (hz : z ∈ halfPlane 0) : DifferentiableAt ℂ H z := by
    have hmellin := differentiableAt_bounded_mellin hg (Nat.cast_nonneg m)
      (fun t ↦ norm_sum_character_Icc_le hψ ⌊t⌋₊) (s := -z)
      (by simpa [neg_re] using (show 0 < z.re from hz))
    have hcomp := hmellin.comp z (differentiableAt_id.neg)
    have heq (w : ℂ) : -w - 1 = -(w + 1) := by ring
    simp only [Function.comp_def, heq] at hcomp
    exact differentiableAt_id.mul hcomp
  have ha : AnalyticOnNhd ℂ H (halfPlane 0) :=
    DifferentiableOn.analyticOnNhd (fun z hz ↦ (hdiff z hz).differentiableWithinAt)
      (isOpen_halfPlane 0)
  have hla : AnalyticOnNhd ℂ ψ.LFunction (halfPlane 0) :=
    fun z _ ↦ (DirichletCharacter.differentiable_LFunction hψ).analyticAt z
  have hbig : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, ψ (k : ZMod m)) =O[atTop]
      fun n ↦ (n : ℝ) ^ (0 : ℝ) :=
    IsBigO.of_bound (m : ℝ) (Eventually.of_forall (by simpa using norm_sum_character_Icc_le hψ))
  have hagree : ψ.LFunction =ᶠ[𝓝 (2 : ℂ)] H := by
    filter_upwards [(isOpen_halfPlane 1).mem_nhds (show (2 : ℂ) ∈ halfPlane 1 by norm_num [halfPlane])]
      with z (hz : 1 < z.re)
    rw [DirichletCharacter.LFunction_eq_LSeries _ hz]
    exact LSeries_eq_mul_integral _ le_rfl (zero_lt_one.trans hz)
      (ψ.LSeriesSummable_of_one_lt_re hz) hbig
  exact (hla.eqOn_of_preconnected_of_eventuallyEq ha (convex_halfSpace_re_gt 0).isPreconnected
    (show (2 : ℂ) ∈ halfPlane 0 by norm_num [halfPlane]) hagree) hs

/-- On the positive half-plane the nonprincipal function is bounded by
`m * |s| / Re s`, with `m` the period of the character. -/
theorem norm_lFunction_le (hψ : ψ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    ‖ψ.LFunction s‖ ≤ (m : ℝ) * ‖s‖ / s.re := by
  rw [lFunction_eq_character_integral hψ hs, norm_mul, mul_comm (m : ℝ) ‖s‖, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left
    (norm_bounded_mellin (fun t ↦ norm_sum_character_Icc_le hψ ⌊t⌋₊) hs)
    (norm_nonneg _)

/-- A fixed positive lower bound on the vertical line of real part two,
obtained by comparing finite Euler products before taking the limit. -/
theorem inv_norm_zeta_two_le_norm_lFunction {s : ℂ} (hs : s.re = 2) :
    ‖riemannZeta 2‖⁻¹ ≤ ‖ψ.LFunction s‖ := by
  have hs' : 1 < s.re := by rw [hs]; norm_num
  have h₂ : 1 < (2 : ℂ).re := by norm_num
  have hz := (riemannZeta_eulerProduct_hasProd h₂).inv₀
    (riemannZeta_ne_zero_of_one_le_re h₂.le)
  have hψ := ψ.LSeries_eulerProduct_hasProd hs'
  rw [← ψ.LFunction_eq_LSeries hs'] at hψ
  have hterm (p : Nat.Primes) :
      ‖1 - (p : ℂ) ^ (-(2 : ℂ))‖ ≤ ‖(1 - ψ (p : ℕ) * (p : ℂ) ^ (-s))⁻¹‖ := by
    let a : ℝ := (p : ℝ) ^ (-2 : ℤ)
    have ha : 0 ≤ a := by dsimp [a]; positivity
    have ha' : a < 1 := by
      have hp : (1 : ℝ) < p := by exact_mod_cast p.prop.one_lt
      dsimp [a]
      simpa [← Real.rpow_intCast] using
        (Real.rpow_lt_rpow_of_exponent_lt hp (by norm_num : (-2 : ℝ) < 0))
    have hnorm : ‖ψ (p : ℕ) * (p : ℂ) ^ (-s)‖ ≤ a := by
      rw [norm_mul, norm_natCast_cpow_of_pos p.prop.pos, neg_re, hs]
      have he : (p : ℝ) ^ (-(2 : ℝ)) = a := by norm_num [a, ← Real.rpow_intCast]
      exact he ▸ mul_le_of_le_one_left (by positivity) (ψ.norm_le_one _)
    have he : (p : ℂ) ^ (-(2 : ℂ)) = (a : ℂ) := by
      rw [cpow_neg, show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, cpow_natCast]
      simp [a, zpow_neg]
    have hne : (1 - ψ (p : ℕ) * (p : ℂ) ^ (-s)) ≠ 0 := by
      intro hz'
      have heq := sub_eq_zero.mp hz'
      rw [← heq, norm_one] at hnorm
      linarith
    rw [he, ← ofReal_one, ← ofReal_sub, norm_real, Real.norm_of_nonneg (sub_nonneg.mpr ha'.le),
      norm_inv, ← one_div]
    apply (le_div_iff₀ (norm_pos_iff.mpr hne)).2
    calc
      _ ≤ (1 - a) * (1 + a) := by
        apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr ha'.le)
        exact (norm_sub_le _ _).trans (by simpa using add_le_add_left hnorm 1)
      _ ≤ 1 := by nlinarith
  unfold HasProd at hz hψ
  simp only [inv_inv] at hz
  have hb := le_of_tendsto_of_tendsto' hz.norm hψ.norm (fun s ↦ by
    simp only [Complex.norm_prod]
    exact Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun p _ ↦ hterm p)
  simpa only [norm_inv] using hb

/-- The pole-removed principal function satisfies the Abel bound throughout
the positive half-plane, including its regularized value at one. -/
theorem norm_regularized_zeta_le {s : ℂ} (hs : 0 < s.re) :
    ‖DirichletCharacter.LFunctionTrivChar₁ 1 s‖ ≤
      ‖s‖ + ‖s - 1‖ * ‖s‖ / s.re := by
  rcases eq_or_ne s 1 with rfl | hs₁
  · simp [DirichletCharacter.LFunctionTrivChar₁]
  let A : ℂ := ∫ t in Ioi (1 : ℝ), zetaAbelFractKernel s t
  have hA : ‖A‖ ≤ 1 / s.re := by
    have hi := norm_bounded_mellin (g := fun t ↦ ((Int.fract t : ℝ) : ℂ))
      (B := 1) (fun t ↦ by simpa using Int.fract_abs_le_one t) hs
    simpa [A, zetaAbelFractKernel, show -s - 1 = -(s + 1) by ring] using hi
  have heq : DirichletCharacter.LFunctionTrivChar₁ 1 s = s - (s - 1) * s * A := by
    rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hs₁,
      DirichletCharacter.LFunctionTrivChar, DirichletCharacter.LFunction_modOne_eq,
      riemannZeta_eq_zetaAbelContinuationFormula_of_re_pos hs₁ hs, zetaAbelContinuationFormula]
    dsimp only [A]
    field_simp [sub_ne_zero.mpr hs₁]
    ring
  rw [heq]
  refine (norm_sub_le _ _).trans (add_le_add_right ?_ _)
  rw [norm_mul, norm_mul, div_eq_mul_inv, ← one_div]
  exact mul_le_mul_of_nonneg_left hA (by positivity)

end GoldbachBoundaries.ResidueClass
