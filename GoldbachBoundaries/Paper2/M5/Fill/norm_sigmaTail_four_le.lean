import GoldbachBoundaries.Paper2.M5.General

/-! Filler group Q: `norm_sigmaTail_four_le` (`Qleft.lean`). As M1's `norm_sigmaTail_two_le`: terms `n ≥ 6` by
`norm_sigmaTerm_le` with `d = 1/3` (geometric); terms `n = 4, 5` by `‖A(s)‖ ≤ ∑ Λ(m) m^{-4/3}` on `Re s ≥ 4/3`. -/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **The Möbius tail from `n = 4` is bounded on `Re w ≥ 1/3`** (unconditional). -/
theorem norm_sigmaTail_four_le : ∃ C : ℝ, ∀ w : ℂ, 1 / 3 ≤ w.re → ‖sigmaTail 4 w‖ ≤ C := by
  set K := ∑' m : ℕ, ArithmeticFunction.vonMangoldt m * (m : ℝ) ^ (-(4 / 3 : ℝ)) with hKdef
  set b : ℕ → ℝ := fun m =>
    (if m < 2 then K else 0) + vmConst * 4 * ((2 : ℝ) ^ (-(1 / 3 : ℝ))) ^ (m + 4) with hbdef
  have hb : Summable b := by
    refine Summable.add ?_ (summable_tail_bound (by norm_num) 4)
    refine summable_of_ne_finset_zero (s := Finset.range 2) fun m hm => ?_
    rw [Finset.mem_range] at hm
    simp [hm]
  refine ⟨∑' m, b m, fun w hw => ?_⟩
  refine tsum_of_norm_bounded hb.hasSum fun m => ?_
  have hgeom : 0 ≤ vmConst * 4 * ((2 : ℝ) ^ (-(1 / 3 : ℝ))) ^ (m + 4) := by
    have := vmConst_nonneg
    positivity
  by_cases hm : m < 2
  · simp only [hbdef, hm, ↓reduceIte]
    have hre : 4 / 3 ≤ (((m + 4 : ℕ) : ℂ) * w).re := by
      rw [re_natCast_mul]
      have h2 : (4 : ℝ) ≤ ((m + 4 : ℕ) : ℝ) := by
        push_cast
        linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
      nlinarith
    calc ‖sigmaTerm (m + 4) w‖ ≤ 1 * ‖negLogDerivZeta (((m + 4 : ℕ) : ℂ) * w)‖ := by
          rw [sigmaTerm, norm_mul]
          gcongr
          exact norm_mu_le_one _
      _ ≤ K := by
          rw [one_mul]
          exact norm_negLogDerivZeta_le_of_re (by norm_num) hre
      _ ≤ _ := le_add_of_nonneg_right hgeom
  · simp only [hbdef, hm, ↓reduceIte, zero_add]
    refine norm_sigmaTerm_le ?_ hw
    have : (2 : ℝ) ≤ m := by exact_mod_cast (not_lt.mp hm)
    push_cast
    linarith

end GoldbachBoundaries.Paper2.M5
