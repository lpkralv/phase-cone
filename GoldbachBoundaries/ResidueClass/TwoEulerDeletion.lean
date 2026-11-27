import GoldbachBoundaries.ResidueClass.MellinSquare

/-! # Deleting the powers of two from the von Mangoldt heat sum -/

noncomputable section

open Complex Set

namespace GoldbachBoundaries.ResidueClass

open Phi2Proof (FL)
open Phi2Proof.FillA (FL_continuousOn_and_le_exp summable_vonMangoldt_mul_exp_neg)

local notation "Λ" => ArithmeticFunction.vonMangoldt
local notation "f₂" => smoothed 2

/-- The heat sum removed on restricting to odd arguments of the von Mangoldt function. -/
def deletedTwoHeat (x : ℝ) : ℝ :=
  Real.log 2 * ∑' k : ℕ, Real.exp (-((2 : ℝ) ^ (k + 1) * x))

private theorem twoPower_injective : Function.Injective (fun k : ℕ ↦ (2 : ℕ) ^ (k + 1)) :=
  (pow_right_strictMono₀ (by norm_num : (1 : ℕ) < 2)).injective.comp Nat.succ_injective

private theorem mangoldt_two_power (k : ℕ) : Λ (2 ^ (k + 1)) = Real.log 2 := by
  rw [ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero _),
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  norm_num

/-- The class-one heat sum at modulus two is the unrestricted sum with the
positive powers of two deleted. -/
theorem FL_sub_smoothed_two {x : ℝ} (hx : 0 < x) :
    FL x - f₂ x = deletedTwoHeat x := by
  let d : ℕ → ℝ := fun n ↦ (Λ n - mangoldtOne 2 n) * Real.exp (-((n : ℝ) * x))
  have hsupport : Function.support d ⊆ Set.range (fun k : ℕ ↦ (2 : ℕ) ^ (k + 1)) := by
    intro n hn
    change d n ≠ 0 at hn
    have hne : Λ n ≠ 0 := fun h ↦ hn (by simp [d, mangoldtOne_eq_ite, h])
    have hmod : (n : ZMod 2) ≠ 1 := fun h ↦ hn (by simp [d, mangoldtOne_eq_ite, h])
    have hdvd : 2 ∣ n := by
      have hm : n % 2 ≠ 1 := by
        intro hm
        exact hmod ((ZMod.natCast_eq_natCast_iff' n 1 2).2 hm)
      omega
    obtain ⟨p, k, hp, hk0, hk⟩ := (isPrimePow_nat_iff n).mp
      (not_not.mp (ArithmeticFunction.vonMangoldt_eq_zero_iff.not.mp hne))
    have h₂p : 2 ∣ p := Nat.prime_two.dvd_of_dvd_pow (hk ▸ hdvd)
    have hp₂ := (Nat.dvd_prime_two_le hp le_rfl).mp h₂p
    subst p
    exact ⟨k - 1, by change (2 : ℕ) ^ (k - 1 + 1) = n; rwa [Nat.sub_add_cancel hk0]⟩
  have hp (k : ℕ) : d (2 ^ (k + 1)) = Real.log 2 * Real.exp (-((2 : ℝ) ^ (k + 1) * x)) := by
    have hmod : ((2 ^ (k + 1) : ℕ) : ZMod 2) ≠ 1 := by
      rw [Nat.cast_pow, pow_succ, ZMod.natCast_self 2, mul_zero]
      exact zero_ne_one
    dsimp only [d]
    rw [mangoldtOne_eq_ite, ite_eq_right hmod, sub_zero, mangoldt_two_power, Nat.cast_pow]
    norm_num
  change (∑' n, Λ n * Real.exp (-((n : ℝ) * x))) -
    (∑' n, mangoldtOne 2 n * Real.exp (-((n : ℝ) * x))) = _
  rw [← (summable_vonMangoldt_mul_exp_neg hx).tsum_sub (summable_smoothed_terms 2 hx)]
  simp_rw [← sub_mul]
  change ∑' n, d n = _
  rw [← tsum_subtype_eq_of_support_subset hsupport, ← (Equiv.ofInjective _ twoPower_injective).tsum_eq]
  simp only [Equiv.ofInjective_apply, hp, deletedTwoHeat, tsum_mul_left]

theorem continuousOn_deletedTwoHeat : ContinuousOn deletedTwoHeat (Ioi 0) :=
  (FL_continuousOn_and_le_exp.1.sub (continuousOn_smoothed 2)).congr
    (fun _ hx ↦ (FL_sub_smoothed_two hx).symm)

private theorem exp_neg_le_rpow {y ε : ℝ} (hy : 0 < y) (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    Real.exp (-y) ≤ y ^ (-ε) := by
  rw [Real.rpow_neg hy.le, Real.exp_neg]
  apply inv_anti₀ (Real.rpow_pos_of_pos hy _)
  by_cases h : 1 ≤ y
  · exact (Real.rpow_le_self_of_one_le h hε₁).trans ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _))
  · exact (Real.rpow_le_one hy.le (le_of_not_ge h) hε.le).trans
      (Real.one_le_exp_iff.mpr hy.le)

/-- Every exponent in (0, 1] gives an inverse-power upper bound for the removed heat sum. -/
theorem deletedTwoHeat_le_rpow {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x → deletedTwoHeat x ≤ C * x ^ (-ε) := by
  let a : ℝ := 2 ^ (-ε)
  have ha : 0 ≤ a := Real.rpow_nonneg (by norm_num) _
  have ha₁ : a < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hs : Summable (fun k : ℕ ↦ a ^ (k + 1)) :=
    (summable_geometric_of_lt_one ha ha₁).comp_injective Nat.succ_injective
  have hbound {x : ℝ} (hx : 0 < x) (k : ℕ) :
      Real.exp (-((2 : ℝ) ^ (k + 1) * x)) ≤ a ^ (k + 1) * x ^ (-ε) := by
    calc
      _ ≤ ((2 : ℝ) ^ (k + 1) * x) ^ (-ε) := exp_neg_le_rpow (by positivity) hε hε₁
      _ = _ := by
        rw [Real.mul_rpow (by positivity) hx.le, ← Real.rpow_natCast_mul (by norm_num),
          mul_comm (↑(k + 1) : ℝ), Real.rpow_mul_natCast (by norm_num)]
  refine ⟨Real.log 2 * ∑' k : ℕ, a ^ (k + 1), by positivity, fun x hx ↦ ?_⟩
  unfold deletedTwoHeat
  rw [mul_assoc, ← tsum_mul_right]
  exact mul_le_mul_of_nonneg_left
    ((Summable.of_nonneg_of_le (fun _ ↦ (Real.exp_pos _).le) (hbound hx)
      (hs.mul_right _)).tsum_le_tsum (hbound hx) (hs.mul_right _)) (by positivity)

theorem deletedTwoHeat_nonneg (x : ℝ) : 0 ≤ deletedTwoHeat x :=
  mul_nonneg (by positivity) (tsum_nonneg fun _ ↦ (Real.exp_pos _).le)

private theorem norm_two_cpow_neg_lt_one {z : ℂ} (hz : 0 < z.re) : ‖(2 : ℂ) ^ (-z)‖ < 1 := by
  rw [← Nat.cast_ofNat, norm_natCast_cpow_of_pos (by decide : 0 < (2 : ℕ)), neg_re]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_lt_zero.mpr hz)

/-- The Mellin transform of the deleted powers on the positive half-plane, including convergence. -/
theorem mellin_deletedTwoHeat {z : ℂ} (hz : 0 < z.re) :
    MellinConvergent (fun x ↦ (deletedTwoHeat x : ℂ)) z ∧
      mellin (fun x ↦ (deletedTwoHeat x : ℂ)) z =
        Gamma z * (Real.log 2 : ℂ) * (2 : ℂ) ^ (-z) / (1 - (2 : ℂ) ^ (-z)) := by
  let w : ℕ → ℝ := fun k ↦ 2 ^ (k + 1)
  have hgeom : Summable (fun k : ℕ ↦ ((2 : ℝ) ^ (-z.re)) ^ k) :=
    summable_geometric_of_lt_one (by positivity)
      (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_lt_zero.mpr hz))
  have hs : Summable (fun k ↦ ‖(Real.log 2 : ℂ)‖ / (w k) ^ z.re) := by
    refine ((hgeom.comp_injective Nat.succ_injective).mul_left ‖(Real.log 2 : ℂ)‖).congr ?_
    intro k
    dsimp [w, Function.comp_def]
    rw [div_eq_mul_inv, ← Real.rpow_neg (by positivity),
      ← Real.rpow_natCast_mul (by norm_num), mul_comm (↑(k + 1) : ℝ),
      Real.rpow_mul_natCast (by norm_num)]
  have hF : ∀ x ∈ Ioi (0 : ℝ), HasSum
      (fun k ↦ (Real.log 2 : ℂ) * Real.exp (-w k * x)) (deletedTwoHeat x : ℂ) := by
    intro x hx
    have ht := (summable_vonMangoldt_mul_exp_neg hx).comp_injective twoPower_injective
    have he : Summable (fun k : ℕ ↦ Real.log 2 * Real.exp (-(w k * x))) := by
      simpa [Function.comp_def, w, mangoldt_two_power, Nat.cast_pow] using ht
    rw [deletedTwoHeat, ← tsum_mul_left]
    have h := he.hasSum
    rw [← Complex.hasSum_ofReal] at h
    simpa only [neg_mul, ofReal_mul, w] using h
  obtain ⟨hc, hv⟩ := TIdentity.mellin_convergent_and_hasSum_of_exp
    (w := w) (fun _ ↦ by dsimp [w]; positivity) hz hF
    (continuous_ofReal.comp_continuousOn continuousOn_deletedTwoHeat) hs
  refine ⟨hc, ?_⟩
  rw [← hv.tsum_eq]
  have hpower (k : ℕ) : (w k : ℂ) ^ (-z) = ((2 : ℂ) ^ (-z)) ^ (k + 1) := by
    simp only [w, ofReal_pow, ofReal_ofNat]
    rw [← Complex.cpow_nat_mul', Complex.cpow_nat_mul]
    · simpa [show (2 : ℂ).arg = 0 from arg_ofReal_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        using Real.pi_pos
    · simpa [show (2 : ℂ).arg = 0 from arg_ofReal_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        using Real.pi_pos.le
  calc
    _ = (Gamma z * (Real.log 2 : ℂ) * (2 : ℂ) ^ (-z)) *
        ∑' k : ℕ, ((2 : ℂ) ^ (-z)) ^ k := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro k
      rw [div_eq_mul_inv, ← Complex.cpow_neg, hpower, pow_succ]
      ring
    _ = _ := by rw [tsum_geometric_of_norm_lt_one (norm_two_cpow_neg_lt_one hz), div_eq_mul_inv]

end GoldbachBoundaries.ResidueClass
