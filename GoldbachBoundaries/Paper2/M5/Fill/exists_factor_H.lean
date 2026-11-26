import GoldbachBoundaries.Paper2.M5.Fill.F4Common

/-!
# Filler F4: `exists_factor_H`

`(cl:eq:HG)`: a symmetric `H` with `H(1, w) ≡ 0` is `(z - 1)(w - 1)G`. View `H` as a polynomial in `z` over `ℂ[w]`
(`MvPolynomial.finSuccEquiv`); its value at `z = 1` vanishes at every `w`, hence is `0`, so `z - 1` divides it:
`H = (z - 1)G₁`. Symmetry gives `H(z, 1) = 0`, so `G₁(z, 1) = 0` for `z ≠ 1`, and for all `z` by continuity. The same
factorization applied to `G₁` with the variables swapped gives `G₁ = (w - 1)G`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- The factorization in the first variable: `P(1, w) ≡ 0` gives `P = (z - 1)G` as functions. -/
lemma F4_factor_z (P : MvPolynomial (Fin 2) ℂ) (h : ∀ w, evalH P 1 w = 0) :
    ∃ G : MvPolynomial (Fin 2) ℂ, ∀ z w, evalH P z w = (z - 1) * evalH G z w := by
  set p := MvPolynomial.finSuccEquiv ℂ 1 P with hp
  have h1 : Polynomial.eval 1 p = 0 := by
    apply MvPolynomial.funext
    intro s
    rw [map_zero]
    have hs : s = ![s 0] := by
      funext i; fin_cases i; rfl
    have := h (s 0)
    rw [F4_evalH_eq, ← hp] at this
    rw [hs, ← Polynomial.eval_map_apply, map_one]
    exact this
  obtain ⟨Q, hQ⟩ := (Polynomial.X_sub_C_dvd_sub_C_eval (a := (1 : MvPolynomial (Fin 1) ℂ)) (p := p))
  rw [h1, map_zero, sub_zero] at hQ
  refine ⟨(MvPolynomial.finSuccEquiv ℂ 1).symm Q, fun z w => ?_⟩
  rw [F4_evalH_eq, F4_evalH_eq, ← hp, AlgEquiv.apply_symm_apply, hQ, Polynomial.map_mul,
    Polynomial.eval_mul]
  simp

/-- The factorization in the second variable: `P(z, 1) ≡ 0` gives `P = (w - 1)G` as functions. -/
lemma F4_factor_w (P : MvPolynomial (Fin 2) ℂ) (h : ∀ z, evalH P z 1 = 0) :
    ∃ G : MvPolynomial (Fin 2) ℂ, ∀ z w, evalH P z w = (w - 1) * evalH G z w := by
  obtain ⟨G, hG⟩ := F4_factor_z (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) P)
    (fun w => by rw [F4_evalH_swap]; exact h w)
  refine ⟨MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) G, fun z w => ?_⟩
  rw [F4_evalH_swap, ← hG w z, F4_evalH_swap]

theorem exists_factor_H (H : MvPolynomial (Fin 2) ℂ) (hHs : ∀ z w, evalH H z w = evalH H w z)
    (hH1 : ∀ w, evalH H 1 w = 0) :
    ∃ G : MvPolynomial (Fin 2) ℂ, ∀ z w, evalH H z w = (z - 1) * (w - 1) * evalH G z w := by
  obtain ⟨G₁, hG₁⟩ := F4_factor_z H hH1
  have hG₁1 : ∀ z, evalH G₁ z 1 = 0 := by
    have hcont : Continuous fun z : ℂ => evalH G₁ z 1 := by
      unfold evalH
      exact (MvPolynomial.continuous_eval G₁).comp
        (continuous_pi fun i => by fin_cases i <;> simp <;> fun_prop)
    have hfun := Continuous.ext_on (dense_compl_singleton (1 : ℂ)) hcont continuous_const
      (fun z hz => by
        have hz' : z - 1 ≠ 0 := sub_ne_zero.mpr hz
        have := hG₁ z 1
        rw [hHs, hH1] at this
        exact (mul_eq_zero.mp this.symm).resolve_left hz')
    exact fun z => congrFun hfun z
  obtain ⟨G, hG⟩ := F4_factor_w G₁ hG₁1
  exact ⟨G, fun z w => by rw [hG₁, hG, mul_assoc]⟩

end GoldbachBoundaries.Paper2.M5
