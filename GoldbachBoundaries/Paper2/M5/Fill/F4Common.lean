import GoldbachBoundaries.Paper2.M5.Tk

/-!
# Filler F4: shared helpers

`evalH` as an iterated univariate evaluation (`MvPolynomial.finSuccEquiv`), and the swap of the two variables.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- `evalH` through `finSuccEquiv`: `H(z, w)` is the polynomial in `z` over `ℂ[w]` evaluated at `w`, then `z`. -/
lemma F4_evalH_eq (P : MvPolynomial (Fin 2) ℂ) (z w : ℂ) :
    evalH P z w = Polynomial.eval z (Polynomial.map (MvPolynomial.eval ![w])
      (MvPolynomial.finSuccEquiv ℂ 1 P)) := by
  rw [← MvPolynomial.eval_eq_eval_mv_eval']
  rfl

/-- Swapping the variables. -/
lemma F4_evalH_swap (P : MvPolynomial (Fin 2) ℂ) (z w : ℂ) :
    evalH (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) P) z w = evalH P w z := by
  unfold evalH
  rw [MvPolynomial.eval_rename]
  congr 2
  funext i
  fin_cases i <;> rfl

end GoldbachBoundaries.Paper2.M5
