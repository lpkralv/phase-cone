import GoldbachBoundaries.Paper2.M5.FilterII
import GoldbachBoundaries.Paper2.M5.Fill.F4Common

/-!
# Filler F4: `evalH_root_bound`

View `H` as a polynomial `P` in `w` over `ℂ[z]` (swap the variables, then `MvPolynomial.finSuccEquiv`); `P ≠ 0`. Its
leading coefficient `a ∈ ℂ[z]` is non-zero, so `E = {z : a(z) = 0}` is finite. For `z ∉ E` the specialization
`H(z, ·)` is a non-zero polynomial of degree `≤ d = natDegree P`, with at most `d` roots.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- A non-zero polynomial in one variable (as an `MvPolynomial (Fin 1)`) has finitely many zeros. -/
lemma F4_finite_zeros_fin1 (a : MvPolynomial (Fin 1) ℂ) (ha : a ≠ 0) :
    {z : ℂ | MvPolynomial.eval ![z] a = 0}.Finite := by
  set q : Polynomial ℂ := Polynomial.map (MvPolynomial.eval ![]) (MvPolynomial.finSuccEquiv ℂ 0 a)
  have hq : ∀ z, Polynomial.eval z q = MvPolynomial.eval ![z] a := by
    intro z
    exact (MvPolynomial.eval_eq_eval_mv_eval' (![] : Fin 0 → ℂ) z a).symm
  have hq0 : q ≠ 0 := by
    intro h0
    apply ha
    apply MvPolynomial.funext
    intro s
    have hs : s = ![s 0] := by
      funext i; fin_cases i; rfl
    rw [map_zero, hs, ← hq, h0, Polynomial.eval_zero]
  refine (Polynomial.finite_setOfPred_isRoot hq0).subset fun z hz => ?_
  simp only [Set.mem_ofPred_eq] at hz ⊢
  rw [Polynomial.IsRoot.def, hq]
  exact hz

theorem evalH_root_bound (H : MvPolynomial (Fin 2) ℂ) (hH0 : H ≠ 0) :
    ∃ (E : Set ℂ) (d : ℕ), E.Finite ∧ ∀ z ∉ E,
      {w : ℂ | evalH H z w = 0}.Finite ∧ {w : ℂ | evalH H z w = 0}.ncard ≤ d := by
  classical
  set H' := MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) H with hH'
  set P := MvPolynomial.finSuccEquiv ℂ 1 H' with hP
  have hH'0 : H' ≠ 0 := by
    intro h0
    apply hH0
    apply MvPolynomial.rename_injective _ (Equiv.injective (Equiv.swap (0 : Fin 2) 1))
    rw [← hH', h0, map_zero]
  have hP0 : P ≠ 0 := by
    intro h0
    apply hH'0
    have := congrArg (MvPolynomial.finSuccEquiv ℂ 1).symm h0
    rwa [hP, AlgEquiv.symm_apply_apply, map_zero] at this
  have heval : ∀ z w, evalH H z w = Polynomial.eval w (Polynomial.map (MvPolynomial.eval ![z]) P) := by
    intro z w
    rw [← F4_evalH_swap H w z, F4_evalH_eq]
  refine ⟨{z : ℂ | MvPolynomial.eval ![z] P.leadingCoeff = 0}, P.natDegree,
    F4_finite_zeros_fin1 _ (Polynomial.leadingCoeff_ne_zero.mpr hP0), fun z hz => ?_⟩
  simp only [Set.mem_ofPred_eq] at hz
  set pz := Polynomial.map (MvPolynomial.eval ![z]) P with hpz
  have hpz0 : pz ≠ 0 := by
    intro h0
    apply hz
    have := congrArg (fun p : Polynomial ℂ => p.coeff P.natDegree) h0
    simp only [hpz, Polynomial.coeff_map, Polynomial.coeff_zero] at this
    exact this
  have hset : {w : ℂ | evalH H z w = 0} = (pz.roots.toFinset : Set ℂ) := by
    ext w
    simp [heval, ← hpz, Polynomial.mem_roots hpz0]
  rw [hset]
  refine ⟨Finset.finite_toSet _, ?_⟩
  rw [Set.ncard_coe_finset]
  exact (Multiset.toFinset_card_le _).trans
    ((Polynomial.card_roots' pz).trans (Polynomial.natDegree_map_le))

end GoldbachBoundaries.Paper2.M5
