import GoldbachBoundaries.Paper2.M3.Test
import GoldbachBoundaries.Paper2.M3.Fill.GCommon

/-!
# Fill: `order_Mform_Tcont_nonneg` (group G)

`x ∈ (2B, 2]`. If `x - 1 ∈ Σ_Q`, put `u = x - 1`: the pairs with sum `1 + u` are `(1, u)`, `(u, 1)`
(`cor_one_add_pairs_proof`), so `Res_x Tcont = 𝓡(1 + u) = [u = 1] + [u ≠ 1] 2R_u/u` (`hasResidue_Tcont`,
`pairSum_one_add`), and `Res_u Qcont = R_u`. The residue of `Mform Tcont` at `x` is then `Γ(2) - 2Γ(1)R_1 + 1 = 0`
(`u = 1`) or `Γ(1 + u)2R_u/u - 2Γ(u)R_u = 0` (`Γ(1 + u) = uΓ(u)`). If `x - 1 ∉ Σ_Q`, then `x ∉ Π` (a pair with an
entry `1` would put `x - 1` in `Σ_Q`; a pair with no entry `1` has sum of real part `≤ 2B`), so `Tcont` is analytic at
`x`, `Qcont` at `x - 1`, and `x ≠ 2`: residue `0`. A meromorphic function with residue `0` has order `≥ 0`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M3

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1 GoldbachBoundaries.Paper2.M2

/-- **`Mform Tcont` is regular on `(2B, 2]`** ((Z1)-(Z3); `B_∞ < B`). `Tcont` is meromorphic on `σ > 2B_∞`, analytic off
`Π` (M1's `Tcont_props`), and `Mform Tcont` is meromorphic there (`meromorphicOn_Mform`, `halfPlane (2B_∞) ⊆ ℍ` by
M1's `half_le_Binf`). Let `x ∈ (2B, 2]` (`2B < 2`: `B < 1` by M1's `lem_B_iv_proof`). If `x ∉ Π`: `Tcont` is analytic at
`x`, and `x - 1 ∉ Σ_Q` (else `x = 1 + (x - 1) ∈ Π`), so `Qcont` is analytic at `x - 1`; `x ≠ 2` since `2 = 1 + 1 ∈ Π`.
If `x ∈ Π`, `x = a + b` with `a, b ∈ Σ_Q`: `a, b ≠ 1` would give `x ≤ 2B` (M1's `poleSetQ_re_le_Bsup`), so `x = 1 + u`
with `u ∈ Σ_Q` real, i.e. `u = 1` or `u = 1/k`, `k ≥ 2` squarefree (a real `ρ/n` is excluded by
`riemannZeta_ne_zero_of_mem_Ioo`). Since `1 + Re u = x > 2B`, M1's `cor_one_add_pairs_proof` and `cor_one_add_proof`
(with `F = Tcont`, `Tcont_eqOn_T`, `eventuallyEq_codiscreteWithin_of_eqOn`) give `Res_{1+1/k} Tcont = 2R_{1/k}k = 2μ(k)`
and `Res_2 Tcont = 1`; the cancellation is then that of `order_Mform_nonneg_of_test` (residue of `Mform Tcont` is
`2μ(k)Γ(1 + 1/k) - 2Γ(1/k)μ(k)/k = 0`, resp. `Γ(2) - 2Γ(1) + 1 = 0`, with order `≥ -1`). Size: 200–350 lines. -/
theorem order_Mform_Tcont_nonneg (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (h : Binf < Bsup) :
    ∀ x ∈ Ioc (2 * Bsup) 2, 0 ≤ meromorphicOrderAt (Mform Tcont) x := by
  intro x hx
  obtain ⟨hmero, hana, -⟩ := Tcont_props hZ1 hZ2 hZ3
  have hBh : 1 / 2 ≤ Bsup := (Bsup_facts hZ1).2.1
  have hx1 : 1 < (x : ℂ).re := by simp; linarith [hx.1]
  have hxB : (x : ℂ) ∈ halfPlane (2 * Binf) := by
    show 2 * Binf < (x : ℂ).re
    simp
    linarith [hx.1]
  have hM : MeromorphicAt (Mform Tcont) x := gc_meromorphicAt_Mform hx1 (hmero _ hxB)
  refine gc_order_nonneg_of_hasResidue_zero hM ?_
  by_cases hu : (x : ℂ) - 1 ∈ PoleSetQ
  · set u : ℂ := (x : ℂ) - 1 with hudef
    have hxu : (x : ℂ) = 1 + u := by rw [hudef]; ring
    have hure : u.re = x - 1 := by simp [hudef]
    have hpairs := cor_one_add_pairs_proof hZ1 hu (by rw [hure]; linarith [hx.1])
    have hT := hasResidue_Tcont hZ1 hZ2 hZ3 (s₀ := x) hxB
    rw [hxu, pairSum_one_add hu hpairs] at hT
    have hQ : HasResidue Qcont u (Rcoef u) := hasResidue_Qcont_Rcoef hu
    rw [hxu] at hx1 ⊢
    have hres := gc_hasResidue_Mform hx1 hT (by simpa using hQ)
    convert hres using 1
    simp only [add_sub_cancel_left]
    by_cases hu1 : u = 1
    · have h11 : (1 : ℂ) + 1 = 2 := by norm_num
      rw [hu1, ite_eq_left_of_eq_true _ _ (eq_self 1), ite_eq_left_of_eq_true _ _ (eq_true h11), Rcoef_one',
        Complex.Gamma_add_one 1 one_ne_zero, Complex.Gamma_one]
      ring
    · have h2 : (1 : ℂ) + u ≠ 2 := fun h2 => hu1 (by linear_combination h2)
      simp only [hu1, h2, ite_false, add_zero]
      have hu0 : u ≠ 0 := by
        intro h0
        have := re_pos_of_mem_poleSetQ hu
        rw [h0] at this
        simp at this
      exact (gc_cancel hu0).symm
  · have hP : (x : ℂ) ∉ Pinch := by
      rintro ⟨a, ha, b, hb, hab⟩
      by_cases ha1 : a = 1
      · exact hu (by rw [hab, ha1]; simpa using hb)
      by_cases hb1 : b = 1
      · exact hu (by rw [hab, hb1]; simpa using ha)
      have h1 := poleSetQ_re_le_Bsup hZ1 ha ha1
      have h2 := poleSetQ_re_le_Bsup hZ1 hb hb1
      have h3 := congrArg Complex.re hab
      simp only [ofReal_re, add_re] at h3
      linarith [hx.1]
    have hT : HasResidue Tcont x 0 := hasResidue_zero_of_analyticAt (hana _ ⟨hxB, hP⟩)
    have hQ : HasResidue Qcont ((x : ℂ) - 1) 0 := by
      refine hasResidue_zero_of_analyticAt (isQCont_Qcont.2.2 _ ⟨?_, hu⟩)
      show (0 : ℝ) < ((x : ℂ) - 1).re
      simp
      linarith [hx.1]
    have hx2 : (x : ℂ) ≠ 2 := by
      intro h2
      apply hu
      rw [h2]
      norm_num
      exact Or.inl (Or.inl rfl)
    have hres := gc_hasResidue_Mform hx1 hT hQ
    simpa [hx2] using hres

end GoldbachBoundaries.Paper2.M3
