import GoldbachBoundaries.ResidueClass.Definitions
import GoldbachBoundaries.PhiR.Fill.mellin_FL_pow

/-! # Restricted coefficients and Dirichlet series -/

noncomputable section

open Complex
open scoped LSeries.notation

namespace GoldbachBoundaries.ResidueClass

theorem mangoldtOne_eq_ite (q n : ℕ) :
    mangoldtOne q n = if (n : ZMod q) = 1 then ArithmeticFunction.vonMangoldt n else 0 := by
  classical
  simp [mangoldtOne, ArithmeticFunction.vonMangoldt.residueClass, Set.indicator_apply]

@[simp] theorem mangoldtOne_zero (q : ℕ) : mangoldtOne q 0 = 0 :=
  ArithmeticFunction.vonMangoldt.residueClass_apply_zero _

theorem mangoldtOne_nonneg (q n : ℕ) : 0 ≤ mangoldtOne q n :=
  ArithmeticFunction.vonMangoldt.residueClass_nonneg _ _

theorem mangoldtOne_le (q n : ℕ) : mangoldtOne q n ≤ ArithmeticFunction.vonMangoldt n :=
  ArithmeticFunction.vonMangoldt.residueClass_le _ _

/-- The two-fold and binary definitions agree by reindexing the ordered pairs. -/
theorem phiR_two (q : ℕ) : PhiR q 2 = Phi2 q := by
  funext s
  rw [PhiR, Phi2, ← (finTwoArrowEquiv ℕ).symm.tsum_eq]
  apply tsum_congr
  intro mn
  simp [Fin.prod_univ_two, Fin.sum_univ_two]

/-- The restricted tuple series converges absolutely on its initial half-plane. -/
theorem summable_norm_phiR (q : ℕ) {r : ℕ} (hr : 1 ≤ r) {s : ℂ} (hs : (r : ℝ) < s.re) :
    Summable (fun k : Fin r → ℕ =>
      ‖(∏ i, (mangoldtOne q (k i) : ℂ)) * ((∑ i, k i : ℕ) : ℂ) ^ (-s)‖) := by
  refine (PhiRProof.FillA.mellin_FL_pow' hr hs).1.of_nonneg_of_le (fun _ ↦ norm_nonneg _) ?_
  intro k
  rw [norm_mul, norm_mul, Complex.norm_prod, Complex.norm_prod]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  refine Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun i _ ↦ ?_
  rw [Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (mangoldtOne_nonneg _ _),
    Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  exact mangoldtOne_le _ _

/-- The restricted binary series converges absolutely for `Re s > 2`. -/
theorem summable_norm_phi2 (q : ℕ) {s : ℂ} (hs : 2 < s.re) :
    Summable (fun mn : ℕ × ℕ =>
      ‖(mangoldtOne q mn.1 : ℂ) * (mangoldtOne q mn.2 : ℂ) *
        ((mn.1 + mn.2 : ℕ) : ℂ) ^ (-s)‖) := by
  have h := summable_norm_phiR q (r := 2) (by omega) (by simpa using hs)
  simpa [Function.comp_def, Fin.prod_univ_two, Fin.sum_univ_two] using
    ((finTwoArrowEquiv ℕ).symm.summable_iff.mpr h)

theorem lSeriesSummable_mangoldtOne (q : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n ↦ (mangoldtOne q n : ℂ)) s :=
  LSeriesSummable_of_abscissaOfAbsConv_lt_re <|
    (ArithmeticFunction.vonMangoldt.abscissaOfAbsConv_residueClass_le_one (1 : ZMod q)).trans_lt
      (by exact_mod_cast hs)

variable (q : ℕ) [NeZero q]

/-- The character average of the negative logarithmic derivatives at level `q`. -/
def D (s : ℂ) : ℂ :=
  (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, -logDeriv χ.LFunction s

/-- Character orthogonality gives the Dirichlet series for `D` on `Re s > 1`. -/
theorem D_eq_lSeries {s : ℂ} (hs : 1 < s.re) :
    D q s = LSeries (fun n ↦ (mangoldtOne q n : ℂ)) s := by
  unfold mangoldtOne
  rw [ArithmeticFunction.vonMangoldt.LSeries_residueClass_eq (isUnit_one : IsUnit (1 : ZMod q)) hs]
  simp [D, logDeriv_apply, Finset.sum_neg_distrib, mul_neg, neg_mul]

end GoldbachBoundaries.ResidueClass
