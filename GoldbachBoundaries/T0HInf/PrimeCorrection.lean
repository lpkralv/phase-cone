import GoldbachBoundaries.T0HInf.Cutoff

/-! The prime/Lambda correction has only the prime-square pole in the chosen strip. -/
noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
namespace GoldbachBoundaries.T0HInf
open GoldbachBoundaries Paper2

def primeCorrection (z : ℂ) : ℂ := Qcont z - negLogDerivZeta z

lemma zeta_ne_zero_right_of_Bsup (hZ1 : Z1) {z : ℂ} (hz : Bsup < z.re) :
    riemannZeta z ≠ 0 := by
  by_cases h1 : 1 ≤ z.re
  · exact riemannZeta_ne_zero_of_one_le_re h1
  · intro he
    have hz0 : 0 < z.re := by linarith [(M1.Bsup_facts hZ1).2.1]
    have hz1 : z.re < 1 := lt_of_not_ge h1
    have := (M1.Bsup_facts hZ1).1 z ⟨he, hz0, hz1⟩
    linarith

lemma analyticAt_primeCorrection (hH : Hinf) (hZ1 : Z1) {z : ℂ}
    (hz : remainderAbscissa ≤ z.re) (hzhalf : z ≠ 1 / 2) :
    AnalyticAt ℂ primeCorrection z := by
  have hb := cutoff_bounds hH
  have hz0 : 0 < z.re := by linarith [hb.2.1]
  have h := analyticAt_Qcont_sub_sum hz0 {1} (fun n hn hmu => by
    have hn0 : n ≠ 0 := (squarefree_of_mu_ne_zero hmu).ne_zero
    have hn1 : n ≠ 1 := by simpa using hn
    have hn2 : 2 ≤ n := by omega
    by_cases he : n = 2
    · subst n
      constructor
      · norm_num only [Nat.cast_ofNat]
        intro he
        apply hzhalf
        linear_combination he / 2
      · apply zeta_ne_zero_right_of_Bsup hZ1
        simp only [re_natCast_mul]
        norm_num
        linarith [hb.1]
    · have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast (show 3 ≤ n by omega)
      apply ne_one_and_zeta_ne_zero_of_one_lt_re
      rw [re_natCast_mul]
      have : 1 < 3 * z.re := by linarith [hb.2.1]
      nlinarith)
  change AnalyticAt ℂ (fun z => Qcont z - negLogDerivZeta z) z
  simpa [sigmaTerm, mu] using h

lemma meromorphicAt_primeCorrection {z : ℂ} (hz : 0 < z.re) :
    MeromorphicAt primeCorrection z :=
  (meromorphicAt_Qcont hz).sub (meromorphicAt_negLogDerivZeta z)

lemma hasResidue_primeCorrection : HasResidue primeCorrection (1 / 2) (-(1 / 2)) := by
  have hm : AnalyticAt ℂ negLogDerivZeta (1 / 2) :=
    analyticAt_negLogDerivZeta (by norm_num)
      (by convert riemannZeta_ne_zero_of_mem_Ioo (x := 1 / 2) (by norm_num) using 1 <;> norm_num)
  have h := (hasResidue_Qcont_inv (k := 2) (by norm_num)).sub (hasResidue_zero_of_analyticAt hm)
  convert! h using 1 <;> norm_num [primeCorrection, mu, ArithmeticFunction.moebius_apply_prime Nat.prime_two]

lemma norm_primeCorrection_le_three {z : ℂ} (hz : 0 < z.re) :
    ‖primeCorrection z‖ ≤ ‖negLogDerivZeta (2 * z)‖ + ‖negLogDerivZeta (3 * z)‖ + ‖sigmaTail 4 z‖ := by
  have hQ := Qcont_eq_sum_add_tail 4 hz
  have h0 : sigmaTerm 0 z = 0 := by simp [sigmaTerm]
  have h1 : sigmaTerm 1 z = negLogDerivZeta z := by simp [sigmaTerm, mu]
  have he : primeCorrection z = sigmaTerm 2 z + sigmaTerm 3 z + sigmaTail 4 z := by
    rw [primeCorrection, hQ]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, h0, h1, zero_add]
    ring
  have hb (n : ℕ) : ‖sigmaTerm n z‖ ≤ ‖negLogDerivZeta (n * z)‖ := by
    rw [sigmaTerm, norm_mul]
    exact (mul_le_mul_of_nonneg_right (norm_mu_le_one n) (norm_nonneg _)).trans_eq (one_mul _)
  rw [he]
  exact norm_add₃_le.trans (by gcongr; exact hb 2; exact hb 3)

end GoldbachBoundaries.T0HInf
