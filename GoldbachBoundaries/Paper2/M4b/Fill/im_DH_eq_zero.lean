import GoldbachBoundaries.Paper2.M4b.ExG

/-!
# Fill, group E2: `im_DH_eq_zero`

`D_H(x)` is real for real `x > 2` when `H` has real coefficients. On the line `c = x/2` the integrand
`g(z) = k_H(z, x) Q(z) Q(x - z)` satisfies `g(conj z) = conj g(z)`, so `y ↦ g(c + iy)` has
`conj g(c + iy) = g(c - iy)`, and `∫ g(c + iy) dy` is fixed by conjugation (`integral_conj`,
`integral_comp_neg`). `VerticalIntegral' g c = (1/2πi) · i · ∫ g(c + iy) dy = (2π)⁻¹ ∫ g(c + iy) dy` is real.
No integrability is needed: if `g` is not integrable on the line both sides are `0`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M4b

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- `Q(conj w) = conj Q(w)`: termwise, `log p` is real and `p^{-conj w} = conj p^{-w}` for `p > 0`. -/
lemma Q_conj_E2 (w : ℂ) : Q (conj w) = conj (Q w) := by
  unfold Q
  rw [Complex.conj_tsum]
  congr 1
  funext p
  have hp : ((p : ℕ) : ℂ).arg ≠ Real.pi := by
    rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm
  rw [map_mul, Complex.conj_ofReal, ← map_neg, Complex.cpow_conj _ _ hp, Complex.conj_natCast]

/-- `H(conj z, conj w) = conj H(z, w)` for `H` with real coefficients. -/
lemma evalH_conj_E2 {H : MvPolynomial (Fin 2) ℂ} (hreal : ∀ m, (H.coeff m).im = 0) (z w : ℂ) :
    evalH H (conj z) (conj w) = conj (evalH H z w) := by
  unfold evalH
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [map_mul, map_prod]
  congr 1
  · exact (Complex.conj_eq_iff_im.mpr (hreal d)).symm
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_pow]
    congr 1
    fin_cases i <;> simp

/-- `k_H(conj z, x) = conj k_H(z, x)` for real `x` and `H` with real coefficients. -/
lemma kH_conj_E2 {H : MvPolynomial (Fin 2) ℂ} (hreal : ∀ m, (H.coeff m).im = 0) (z : ℂ) (x : ℝ) :
    kH H (conj z) x = conj (kH H z x) := by
  unfold kH KerS
  have hx : (x : ℂ) - conj z = conj ((x : ℂ) - z) := by rw [map_sub, Complex.conj_ofReal]
  have hGx : conj (Gamma (x : ℂ)) = Gamma x := by rw [← Complex.Gamma_conj, Complex.conj_ofReal]
  rw [hx, evalH_conj_E2 hreal, Complex.Gamma_conj, Complex.Gamma_conj, map_mul, map_div₀, map_mul, hGx]

/-- **`D_H` is real on the real axis when `H` has real coefficients.** `DH H x = (1/2πi)∫_{(x/2)} g` with
`g(z) = k_H(z, x)Q(z)Q(x - z)`, and `VerticalIntegral' g c = (2π)⁻¹∫ g(c + iy) dy`. On the line, `conj(c + iy) = c - iy`
and `g(conj z) = conj g(z)`: `K_x(conj z) = conj K_x(z)` (`Complex.Gamma_conj`, `x` real), `H(conj z, conj w) =
conj H(z, w)` (real coefficients: `MvPolynomial.eval` commutes with `conj` coefficientwise, `MvPolynomial.induction_on`
or `eval_eq` with `starRingEnd` and `hreal`), and `Q(conj w) = conj Q(w)` (termwise, `p^{-conj w} = conj p^{-w}` for a
positive real base, `Complex.cpow_conj`; `Complex.conj_tsum`). Hence `conj ∫ g(c + iy) dy = ∫ g(c - iy) dy =
∫ g(c + iy) dy` (`integral_conj`, `integral_comp_neg`), so the integral is real; this holds whether or not `g` is
integrable (the junk integral is `0`). Size: 100–200 lines. -/
theorem im_DH_eq_zero {H : MvPolynomial (Fin 2) ℂ} (hreal : ∀ m, (H.coeff m).im = 0) :
    ∀ x : ℝ, 2 < x → (DH H x).im = 0 := by
  intro x _
  set c : ℝ := ((x : ℂ)).re / 2 with hc
  set g : ℂ → ℂ := fun z => kH H z x * Q z * Q (x - z) with hg
  -- the reflection identity on the line
  have hrefl : ∀ y : ℝ, conj (g (c + y * I)) = g (c + (-y : ℝ) * I) := by
    intro y
    have hz : (c : ℂ) + ((-y : ℝ) : ℂ) * I = conj ((c : ℂ) + (y : ℂ) * I) := by
      simp [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    have hxz : (x : ℂ) - conj ((c : ℂ) + (y : ℂ) * I) = conj ((x : ℂ) - ((c : ℂ) + (y : ℂ) * I)) := by
      rw [map_sub, Complex.conj_ofReal]
    rw [hz, hg]
    simp only
    rw [hxz, kH_conj_E2 hreal, Q_conj_E2, Q_conj_E2, map_mul, map_mul]
  -- the integral is real
  have hint : conj (∫ y : ℝ, g (c + y * I)) = ∫ y : ℝ, g (c + y * I) := by
    rw [← integral_conj]
    refine (integral_congr_ae (Filter.Eventually.of_forall hrefl)).trans ?_
    exact integral_neg_eq_self (fun y : ℝ => g (c + (y : ℂ) * I)) volume
  have him : (∫ y : ℝ, g (c + y * I)).im = 0 := Complex.conj_eq_iff_im.mp hint
  have hDH : DH H x = (1 / (2 * Real.pi * I)) • (I • ∫ y : ℝ, g (c + y * I)) := rfl
  rw [hDH, smul_eq_mul, smul_eq_mul, ← mul_assoc]
  have hcoef : (1 / (2 * (Real.pi : ℂ) * I)) * I = ((1 / (2 * Real.pi) : ℝ) : ℂ) := by
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    push_cast
    field_simp
  rw [hcoef, Complex.im_ofReal_mul, him, mul_zero]

end GoldbachBoundaries.Paper2.M4b
