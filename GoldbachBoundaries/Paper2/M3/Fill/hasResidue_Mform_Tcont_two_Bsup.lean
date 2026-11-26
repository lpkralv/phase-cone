import GoldbachBoundaries.Paper2.M3.Test
import GoldbachBoundaries.Paper2.M3.Fill.GCommon

/-!
# Fill: `hasResidue_Mform_Tcont_two_Bsup` (group G)

`1/2 < B < 1` (`lem_B_iv_proof`), so `x = 2B ∈ (1, 2)` and `2B > 2B_∞`: `Res_{2B} Tcont = 𝓡(2B)` (`hasResidue_Tcont`).
If `2B = 1 + 1/k` (`k ≥ 2`): `𝓡(2B) = A + 2μ(k)` (`pairSum_two_Bsup`), `Res_{1/k} Qcont = μ(k)/k`
(`hasResidue_Qcont_inv`, any `k ≥ 2`), and `Γ(1 + 1/k)·2μ(k) = 2Γ(1/k)μ(k)/k` cancels. Otherwise `𝓡(2B) = A` and the real
point `2B - 1 ∈ (0, 1)` is no `1/k`, so `Qcont` is analytic there. In both cases the residue of `Mform Tcont` at `2B` is
`Γ(2B)A` (`2B ≠ 2`), and `Γ(2B) = Real.Gamma (2B)` (`Complex.Gamma_ofReal`).
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M3

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1 GoldbachBoundaries.Paper2.M2

/-- **The residue of `Mform Tcont` at `2B`** ((Z1)-(Z3); `B_∞ < B`). `2B > 2B_∞`, so `Res_{2B} Tcont = 𝓡(2B)` (M1's
`hasResidue_Tcont`), `= A + 2μ(k)` if `2B = 1 + 1/k`, `= A` otherwise (`pairSum_two_Bsup`); times `Γ` (analytic at
`2B`, `TIdentity.HasResidue.mul_continuousAt'` or `HasResidue.mul_const` after `Γ(s) = Γ(2B) + O(s - 2B)`). The term
`-2Γ(s-1)Qcont(s-1)`: if `2B = 1 + 1/k` with `k` squarefree, its residue is `-2Γ(1/k)μ(k)/k = -2μ(k)Γ(2B)`
(M1's `hasResidue_Qcont_Rcoef`, `Rcoef_inv`); if `k` is not squarefree, `μ(k) = 0` and `1/k ∉ Σ_Q`, so `Qcont` is
analytic at `2B - 1`; if `2B - 1` is not of the form `1/k`, `2B - 1 ∉ Σ_Q` (real, in `(0, 1)`, as in
`order_Mform_Tcont_nonneg`) and `Qcont` is analytic there. The other terms are analytic at `2B ≠ 2`
(`hasResidue_zero_of_analyticAt`). Sum: `Γ(2B)A` (`Complex.Gamma_ofReal`). Size: 150–250 lines. -/
theorem hasResidue_Mform_Tcont_two_Bsup (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (h : Binf < Bsup) :
    HasResidue (Mform Tcont) ((2 * Bsup : ℝ) : ℂ) ((Real.Gamma (2 * Bsup) * Aconst : ℝ) : ℂ) := by
  obtain ⟨hB1, hB2, -, -⟩ := lem_B_iv_proof hZ1 h
  have hx1 : 1 < ((2 * Bsup : ℝ) : ℂ).re := by rw [ofReal_re]; linarith
  have hxB : 2 * Binf < ((2 * Bsup : ℝ) : ℂ).re := by rw [ofReal_re]; linarith
  have hx2 : ((2 * Bsup : ℝ) : ℂ) ≠ 2 := by
    intro h2
    have := congrArg Complex.re h2
    simp at this
    linarith
  have hT := hasResidue_Tcont hZ1 hZ2 hZ3 hxB
  obtain ⟨hp1, hp2⟩ := pairSum_two_Bsup hZ1 h
  have hG : Gamma ((2 * Bsup : ℝ) : ℂ) = ((Real.Gamma (2 * Bsup) : ℝ) : ℂ) := Complex.Gamma_ofReal _
  by_cases hk : ∃ k : ℕ, 2 ≤ k ∧ 2 * Bsup = 1 + 1 / (k : ℝ)
  · obtain ⟨k, hk2, hkB⟩ := hk
    rw [hp1 k hk2 hkB] at hT
    have hxk : ((2 * Bsup : ℝ) : ℂ) = 1 + 1 / (k : ℂ) := by rw [hkB]; push_cast; ring
    have hQ : HasResidue Qcont (((2 * Bsup : ℝ) : ℂ) - 1) (mu k / k) := by
      rw [hxk, add_sub_cancel_left]
      exact hasResidue_Qcont_inv hk2
    have hres := gc_hasResidue_Mform hx1 hT hQ
    rw [ite_eq_right_iff.2 (fun h => absurd h hx2), add_zero] at hres
    convert hres using 1
    have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    have hinv0 : 1 / (k : ℂ) ≠ 0 := by simpa using hk0
    rw [ofReal_mul, ← hG, hxk, add_sub_cancel_left, add_comm (1 : ℂ), Complex.Gamma_add_one _ hinv0]
    field_simp
    ring
  · push Not at hk
    rw [hp2 hk] at hT
    have hy : 2 * Bsup - 1 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have hQ : HasResidue Qcont (((2 * Bsup : ℝ) : ℂ) - 1) 0 := by
      have := gc_hasResidue_Qcont_real hy fun k hk2 _ hyk => by
        apply hk k hk2
        have hre := congrArg Complex.re hyk
        simp only [ofReal_re] at hre
        rw [one_div, Complex.inv_re, Complex.normSq_natCast, natCast_re] at hre
        rw [one_div]
        have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
        field_simp at hre ⊢
        linarith
      simpa using this
    have hres := gc_hasResidue_Mform hx1 hT hQ
    rw [ite_eq_right_iff.2 (fun h => absurd h hx2)] at hres
    convert hres using 1
    rw [hG]
    push_cast
    ring

end GoldbachBoundaries.Paper2.M3
