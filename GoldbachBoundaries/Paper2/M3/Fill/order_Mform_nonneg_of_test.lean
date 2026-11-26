import GoldbachBoundaries.Paper2.M3.Mellin
import GoldbachBoundaries.Paper2.M3.Fill.GCommon

/-!
# Fill: `order_Mform_nonneg_of_test` (group G)

`x ∈ (1, 2]`; `Mform T̃` is meromorphic at `x` (`gc_meromorphicAt_Mform`), and its residue there is
`Γ(x)Res_x T̃ - 2Γ(x - 1)Res_{x-1} Qcont + [x = 2]` (`gc_hasResidue_Mform`). It is `0` in each case, so the order is
`≥ 0` (`gc_order_nonneg_of_hasResidue_zero`).
* `x = 2`: `Res_2 T̃ = 1` (`hasResidue_two_of_codiscrete` on a disc `Δ(2, r) ⊆ U`), `Res_1 Qcont = 1`:
  `Γ(2) - 2Γ(1) + 1 = 0`.
* `x = 1 + 1/k` (a pole of `T̃`, `k ≥ 2` squarefree): `Res T̃ = 2μ(k)`, `Res_{1/k} Qcont = μ(k)/k`:
  `Γ(1 + 1/k)2μ(k) - 2Γ(1/k)μ(k)/k = 0`.
* otherwise (`x ∈ (1, 2)`, `T̃` of order `≥ 0`): `Res T̃ = 0`, and `x - 1 ∈ (0, 1)` is no `1/k` with `k ≥ 2` squarefree
  (else `x` would be a pole), so `Qcont` is analytic at `x - 1`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M3

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1 GoldbachBoundaries.Paper2.M2

/-- **Step 1: `𝓜̃` has no pole on `(1, 2]`** (unconditional). `Mform T̃` is meromorphic on `U ∩ ℍ`
(`meromorphicOn_Mform`). Let `x ∈ (1, 2]`; the terms `1/(s-2)` (`x ≠ 2`), `E`, `e`, `Γ` are analytic at `x`, so only
`Γ(s)T̃(s)` and `-2Γ(s-1)Qcont(s-1)` matter, each of order `≥ -1`.
* `x = 1 + 1/k`, `k ≥ 2` squarefree: `T̃` has residue `2μ(k)` (hypothesis); `Qcont` has residue `R_{1/k} = μ(k)/k` at
  `1/k` (M1's `hasResidue_Qcont_Rcoef`, `Rcoef_inv`; `HasResidue.comp_sub_const`). The residue of the sum is
  `2μ(k)Γ(1 + 1/k) - 2Γ(1/k)μ(k)/k = 0` (`Complex.Gamma_add_one`); with order `≥ -1`
  (`HasResidue.neg_one_le_meromorphicOrderAt`) a zero residue gives order `≥ 0` (`(s - x)·Mform → 0`, so
  `tendsto_nhds_iff_meromorphicOrderAt_nonneg` applied to `(s - x)·Mform` and `meromorphicOrderAt_mul`).
* `x ∈ (1, 2)` not of that form: `T̃` has order `≥ 0` at `x` (hypothesis, negated), and `x - 1 ∉ Σ_Q` (the real points
  of `Σ_Q` in `(0, 1)` are the `1/k`, `k ≥ 2` squarefree: a real `ρ/n` would give a real zero in `(0, 1)`, excluded by
  `riemannZeta_ne_zero_of_mem_Ioo`), so `Qcont` is analytic at `x - 1` (`M2.isQCont_Qcont`).
* `x = 2`: on a disc `Δ(2, r) ⊆ U`, `T̃` is meromorphic and equals `T` on `Δ(2, r) ∩ {σ > 2}`, so it has residue `1`
  (`lem_hsq_proof`, last clause, with `eventuallyEq_codiscreteWithin_of_eqOn`); `Qcont` has residue `R_1 = 1` at `1`
  (`Rcoef_one'`); the residue of `Mform T̃` at `2` is `Γ(2)·1 - 2Γ(1)·1 + 1 = 0`.
Size: 250–400 lines. -/
theorem order_Mform_nonneg_of_test {U : Set ℂ} {Tt : ℂ → ℂ} (h : IsTestPair U Tt) :
    ∀ x ∈ Ioc (1 : ℝ) 2, 0 ≤ meromorphicOrderAt (Mform Tt) x := by
  intro x hx
  obtain ⟨hU, hUx, hTt, hEq, hpol, hres⟩ := h
  have hxU := hUx x hx
  have hx1 : 1 < (x : ℂ).re := by simpa using hx.1
  have hTm : MeromorphicAt Tt x := hTt _ hxU
  have hM := gc_meromorphicAt_Mform hx1 hTm
  refine gc_order_nonneg_of_hasResidue_zero hM ?_
  rcases eq_or_lt_of_le hx.2 with hx2 | hx2
  · -- `x = 2`
    have hc : (x : ℂ) = 2 := by rw [hx2]; norm_num
    rw [hc] at hxU ⊢
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU 2 hxU
    have hT2 := (hasResidue_two_of_codiscrete Tt r hr (hTt.mono_set hball)
      (eventuallyEq_codiscreteWithin_of_eqOn fun z hz => hEq ⟨hball hz.1, hz.2⟩)).2
    have hQ : HasResidue Qcont ((2 : ℂ) - 1) 1 := by
      norm_num
      exact hasResidue_Qcont_one
    have hres2 := gc_hasResidue_Mform (x := 2) (by norm_num) hT2 hQ
    convert hres2 using 1
    have hG2 : Gamma 2 = 1 := by
      rw [show (2 : ℂ) = 1 + 1 by norm_num, Complex.Gamma_add_one 1 one_ne_zero, Complex.Gamma_one]
      ring
    rw [ite_eq_left_of_eq_true _ _ (eq_self 2), hG2, show (2 : ℂ) - 1 = 1 by norm_num, Complex.Gamma_one]
    ring
  · have hxI : x ∈ Ioo (1 : ℝ) 2 := ⟨hx.1, hx2⟩
    have hxne2 : (x : ℂ) ≠ 2 := by
      intro h2
      have := congrArg Complex.re h2
      simp at this
      linarith
    by_cases hneg : meromorphicOrderAt Tt x < 0
    · -- `x = 1 + 1/k`
      obtain ⟨k, hk2, hsq, hxk⟩ := (hpol x hxI).1 hneg
      have hTr := (hres k hk2 hsq).2
      rw [← hxk] at hTr
      have hQ : HasResidue Qcont ((x : ℂ) - 1) (mu k / k) := by
        rw [hxk, add_sub_cancel_left]
        exact hasResidue_Qcont_inv hk2
      have hres1 := gc_hasResidue_Mform hx1 hTr hQ
      rw [ite_eq_right_iff.2 (fun h => absurd h hxne2), add_zero] at hres1
      convert hres1 using 1
      have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
      have hinv0 : 1 / (k : ℂ) ≠ 0 := by simpa using hk0
      rw [hxk, add_sub_cancel_left, add_comm (1 : ℂ), Complex.Gamma_add_one _ hinv0]
      field_simp
      ring
    · -- regular point of `T̃`
      push Not at hneg
      have hTr := gc_hasResidue_zero_of_order_nonneg hTm hneg
      have hQ : HasResidue Qcont ((x : ℂ) - 1) 0 := by
        have := gc_hasResidue_Qcont_real (y := x - 1) ⟨by linarith [hx.1], by linarith⟩
          fun k hk2 hsq hyk => by
            have hxk : (x : ℂ) = 1 + 1 / (k : ℂ) := by
              push_cast at hyk
              linear_combination hyk
            exact absurd ((hpol x hxI).2 ⟨k, hk2, hsq, hxk⟩) (not_lt.2 hneg)
        simpa using this
      have hres0 := gc_hasResidue_Mform hx1 hTr hQ
      simpa [hxne2] using hres0

end GoldbachBoundaries.Paper2.M3
