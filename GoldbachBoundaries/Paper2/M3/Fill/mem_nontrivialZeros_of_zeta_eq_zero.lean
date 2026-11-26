import GoldbachBoundaries.Paper2.M3.Defs

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
namespace GoldbachBoundaries.Paper2.M3
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/- The functional-equation factor argument below is adapted from
PrimeNumberTheoremAnd/IEANTN/KadiriZeroCounting.lean (Apache-2.0),
`Kadiri.riemannZeta_one_sub_ne_zero_of_one_le_re`. -/
private lemma A1_reflected_ne_zero {w : ℂ}
    (hw_re : 1 ≤ w.re) (hcos : Complex.cos (↑Real.pi * w / 2) ≠ 0) :
    riemannZeta (1 - w) ≠ 0 := by
  have hw_neg_nat : ∀ n : ℕ, w ≠ -↑n := by
    intro n hn
    have hre' : w.re = -(n : ℝ) := by rw [hn]; simp
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    rw [hre'] at hw_re; linarith
  have hw_ne_one : w ≠ 1 := by
    rintro rfl
    refine hcos ?_
    have h2 : (↑Real.pi * (1 : ℂ) / 2) = ((Real.pi / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [h2, ← Complex.ofReal_cos, Real.cos_pi_div_two, Complex.ofReal_zero]
  have hpow : (2 * ↑Real.pi : ℂ) ^ (-w) ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff]; left
    norm_num [Complex.ofReal_ne_zero, Real.pi_ne_zero]
  have hGamma : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero hw_neg_nat
  have hzeta_w : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_le_re hw_re
  have hfe := riemannZeta_one_sub (s := w) hw_neg_nat hw_ne_one
  rw [hfe]
  exact mul_ne_zero
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hpow) hGamma) hcos) hzeta_w

/-- **Every zero that is not trivial lies in the strip** (functional equation; unconditional). Let `ζ(s) = 0`, `s` not
of the form `-2(n+1)`, `s ≠ 1`. `σ ≥ 1` is impossible (`riemannZeta_ne_zero_of_one_le_re`). If `σ ≤ 0` and `t ≠ 0`,
put `w = 1 - s`: `Re w ≥ 1`, and `riemannZeta_one_sub` writes `ζ(s) = ζ(1 - w)` as `2(2π)^{-w}Γ(w)cos(πw/2)ζ(w)`, where
`(2π)^{-w}`, `Γ(w)`, `ζ(w)` are non-zero and `cos(πw/2) = 0` forces `w` real. If `s = σ ≤ 0` is real: `σ = 0` gives
`ζ(0) = -1/2` (`riemannZeta_zero`); for `σ < 0`, `cos(π(1 - σ)/2) = 0` iff `1 - σ` is an odd integer `2m + 1`, i.e.
`σ = -2m`, `m ≥ 1`, a trivial zero, excluded. So `0 < σ < 1`. PNT+ has these steps
(`riemannZeta_one_sub_ne_zero_of_one_le_re`, `riemannZeta_ne_zero_of_re_nonpos_im_ne_zero`,
`riemannZeta_ne_zero_of_real_neg` in `PrimeNumberTheoremAnd/IEANTN/KadiriZeroCounting.lean`); copy the arguments, do
not import that file (it is not built here and pulls in much of `IEANTN`). Size: 80–150 lines. -/
theorem mem_nontrivialZeros_of_zeta_eq_zero {s : ℂ} (hs : riemannZeta s = 0) (htriv : ¬∃ n : ℕ, s = -2 * (n + 1))
    (h1 : s ≠ 1) : s ∈ NontrivialZeros := by
  have _ := h1
  refine ⟨hs, ?_, ?_⟩
  · by_contra hpos
    have hre : s.re ≤ 0 := le_of_not_gt hpos
    have hs0 : s ≠ 0 := by
      intro he
      rw [he, riemannZeta_zero] at hs
      norm_num at hs
    have hcos : Complex.cos (↑Real.pi * (1 - s) / 2) ≠ 0 := by
      intro hc
      obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp hc
      have he : 1 - s = 2 * (k : ℂ) + 1 := by
        apply mul_left_cancel₀ (show (Real.pi : ℂ) ≠ 0 by exact_mod_cast Real.pi_ne_zero)
        linear_combination 2 * hk
      have hsval : s = -2 * (k : ℂ) := by linear_combination -he
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := by
        have := congrArg Complex.re hsval
        simp at this
        linarith
      have hkpos : 0 < k := by
        have hk_nonneg : 0 ≤ k := by exact_mod_cast hk0
        have hkn : k ≠ 0 := by
          intro h
          exact hs0 (by simpa [h] using hsval)
        omega
      have hnat : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg (by omega)
      refine htriv ⟨k.toNat - 1, ?_⟩
      have hn : k.toNat - 1 + 1 = k.toNat := by
        have : 0 < k.toNat := by omega
        omega
      rw [show ((k.toNat - 1 : ℕ) : ℂ) + 1 = (k.toNat : ℂ) by
        exact_mod_cast hn]
      have hcast : (k.toNat : ℂ) = (k : ℂ) := by exact_mod_cast hnat
      simpa [hcast] using hsval
    have hn := A1_reflected_ne_zero (w := 1 - s) (by simp; linarith) hcos
    exact hn (by simpa using hs)
  · by_contra hlt
    exact riemannZeta_ne_zero_of_one_le_re (le_of_not_gt hlt) hs

end GoldbachBoundaries.Paper2.M3
