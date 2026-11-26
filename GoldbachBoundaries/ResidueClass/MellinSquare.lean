import GoldbachBoundaries.ResidueClass.Smoothed

/-! # Mellin transforms of the square and finite powers of the smoothed sum -/

noncomputable section

open Complex Set MeasureTheory

namespace GoldbachBoundaries.ResidueClass

set_option maxHeartbeats 800000 in
/-- Finite powers of a nonnegative real sum, indexed by tuples. -/
private theorem hasSum_tuple_prod {f : ℕ → ℝ} (hf : Summable f) (hn : ∀ n, 0 ≤ f n) (r : ℕ) :
    HasSum (fun k : Fin r → ℕ => ∏ i, f (k i)) ((∑' n, f n) ^ r) := by
  induction r with
  | zero => simpa using (hasSum_fintype (fun k : Fin 0 → ℕ => ∏ i, f (k i)))
  | succ r ih =>
    have hnn : ∀ k : Fin r → ℕ, 0 ≤ ∏ i, f (k i) :=
      fun k => Finset.prod_nonneg fun i hi => hn (k i)
    have hsum : Summable (fun p : ℕ × (Fin r → ℕ) => f p.1 * ∏ i, f (p.2 i)) :=
      hf.mul_of_nonneg ih.summable hn hnn
    have hp := hf.hasSum.mul ih hsum
    apply (Fin.consEquiv (fun _ : Fin (r + 1) => ℕ)).hasSum_iff.mp
    convert hp using 1
    · funext k
      simp [Function.comp_apply, Fin.prod_univ_succ, Fin.consEquiv]
    · rw [pow_succ]; ring


private abbrev posTuple (r : ℕ) : Set (Fin r → ℕ) := {k | ∀ i, k i ≠ 0}

private theorem tuple_sum_pos {r : ℕ} (hr : 1 ≤ r) {k : Fin r → ℕ}
    (hk : ∀ i, k i ≠ 0) : 0 < ∑ i, k i := by
  have hi : k ⟨0, by omega⟩ ≤ ∑ i, k i := Finset.single_le_sum (fun i hi => Nat.zero_le _) (Finset.mem_univ _)
  exact lt_of_lt_of_le (Nat.pos_of_ne_zero (hk _)) hi

private theorem tuple_zero (q : ℕ) {r : ℕ} {k : Fin r → ℕ} (hk : ¬ ∀ i, k i ≠ 0) :
    (∏ i, (mangoldtOne q (k i) : ℂ)) = 0 := by
  classical
  push Not at hk
  obtain ⟨i, hi⟩ := hk
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-- Termwise Mellin integration on the initial half-plane for the tuple series. -/
theorem mellin_smoothed_pow (q : ℕ) {r : ℕ} (hr : 1 ≤ r) {s : ℂ} (hs : (r : ℝ) < s.re) :
    MellinConvergent (fun x ↦ ((smoothed q x ^ r : ℝ) : ℂ)) s ∧
    mellin (fun x ↦ ((smoothed q x ^ r : ℝ) : ℂ)) s = Gamma s * PhiR q r s := by
  classical
  have hs0 : 0 < s.re := (Nat.cast_nonneg r).trans_lt hs
  have hnorm := summable_norm_phiR q hr hs
  let a : posTuple r → ℂ := fun k => ∏ i, (mangoldtOne q (k.val i) : ℂ)
  let w : posTuple r → ℝ := fun k => ((∑ i, k.val i : ℕ) : ℝ)
  have hw : ∀ k, 0 < w k := fun k => by
    dsimp [w]
    exact_mod_cast tuple_sum_pos hr k.prop
  have hF : ∀ t ∈ Ioi (0 : ℝ), HasSum (fun k => a k * Real.exp (-w k * t))
      ((smoothed q t ^ r : ℝ) : ℂ) := by
    intro t ht
    have hf := summable_smoothed_terms q ht
    have hp := hasSum_tuple_prod hf (fun n => mul_nonneg (mangoldtOne_nonneg q n) (Real.exp_pos _).le) r
    rw [← Complex.hasSum_ofReal] at hp
    have hsupp : Function.support (fun k : Fin r → ℕ =>
        ((∏ i, mangoldtOne q (k i) * Real.exp (-((k i : ℝ) * t)) : ℝ) : ℂ)) ⊆ posTuple r := by
      intro k hk
      by_contra hn
      change ¬ ∀ i, k i ≠ 0 at hn
      change _ ≠ 0 at hk
      apply hk
      push Not at hn
      obtain ⟨i, hi⟩ := hn
      dsimp only
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi]), ofReal_zero]
    have hsub := (hasSum_subtype_iff_of_support_subset hsupp).mpr hp
    convert hsub using 1
    · funext k
      dsimp only [a, w, Function.comp_apply]
      rw [← Complex.ofReal_prod, ← Complex.ofReal_mul]
      congr 1
      rw [Finset.prod_mul_distrib, ← Real.exp_sum]
      congr 2
      push_cast
      rw [Finset.sum_neg_distrib, neg_mul, Finset.sum_mul]
    · rfl
  have hFc : ContinuousOn (fun t => ((smoothed q t ^ r : ℝ) : ℂ)) (Ioi 0) :=
    continuous_ofReal.comp_continuousOn ((continuousOn_smoothed q).pow r)
  have h_sum : Summable fun k => ‖a k‖ / (w k) ^ s.re := by
    refine (hnorm.subtype (posTuple r)).congr fun k => ?_
    dsimp only [Function.comp_apply]
    rw [norm_mul, norm_natCast_cpow_of_pos (tuple_sum_pos hr k.prop), neg_re,
      Real.rpow_neg (Nat.cast_nonneg _), div_eq_mul_inv]
  obtain ⟨hconv, hval⟩ := TIdentity.mellin_convergent_and_hasSum_of_exp hw hs0 hF hFc h_sum
  refine ⟨hconv, ?_⟩
  have hsupp : Function.support (fun k : Fin r → ℕ =>
      (∏ i, ((mangoldtOne q (k i) : ℝ) : ℂ)) * (((∑ i, k i : ℕ) : ℂ)) ^ (-s)) ⊆ posTuple r := by
    intro k hk
    by_contra hn
    change _ ≠ 0 at hk
    apply hk
    dsimp only
    rw [tuple_zero q hn, zero_mul]
  rw [← hval.tsum_eq, PhiR, ← tsum_subtype_eq_of_support_subset hsupp, ← tsum_mul_left]
  apply tsum_congr
  intro k
  dsimp [a, w]
  rw [cpow_neg, mul_div_assoc, div_eq_mul_inv]

/-- The binary Mellin transform, with integrability of the Mellin integrand. -/
theorem mellin_smoothed_sq (q : ℕ) {s : ℂ} (hs : 2 < s.re) :
    IntegrableOn (fun x : ℝ ↦ (smoothed q x : ℂ)^2 * (x : ℂ) ^ (s - 1)) (Ioi 0) ∧
      (∫ x in Ioi (0 : ℝ), (smoothed q x : ℂ)^2 * (x : ℂ) ^ (s - 1)) =
        Gamma s * Phi2 q s := by
  obtain ⟨hi, hv⟩ := mellin_smoothed_pow q (r := 2) (by omega) (by simpa using hs)
  rw [phiR_two] at hv
  constructor
  · simpa [MellinConvergent, smul_eq_mul, ofReal_pow, mul_comm] using hi
  · rw [← hv, mellin]
    congr 1
    funext x
    rw [smul_eq_mul, ofReal_pow, mul_comm]

end GoldbachBoundaries.ResidueClass
