import GoldbachBoundaries.Paper2.M4b.MB

noncomputable section
open Complex
namespace GoldbachBoundaries.Paper2.M4b
open GoldbachBoundaries GoldbachBoundaries.Paper2

private lemma gamma_shift (w : ℂ) (hw : 0 < w.re) (n : ℕ) :
    Gamma (w + n) = (ascPochhammer ℂ n).eval w * Gamma w := by
  have hn : ∀ k : ℕ, w ≠ -k := by
    intro k hk
    have := hw
    rw [hk] at this
    simp only [neg_re, natCast_re] at this
    linarith [Nat.cast_nonneg (α := ℝ) k]
  exact (div_eq_iff (Gamma_ne_zero_of_re_pos hw)).mp
    (Gamma_add_nat_div_Gamma_eq w hn)

/-- **`k_H` as a rising combination** (first remark after `cl:thm:filter`). With `Re z > 0`, `Re(s - z) > 0`:
`Γ(s+i+j) ≠ 0` cancels in `cWH h i j s · Γ(z+i)Γ(s-z+j)/Γ(s+i+j) = h_{ij}Γ(z+i)Γ(s-z+j)/Γ(s)`;
`Γ(z+i) = z^{(i)}Γ(z)` and `Γ(s-z+j) = (s-z)^{(j)}Γ(s-z)` (induction on `i` with `Complex.Gamma_add_one` and
`ascPochhammer_succ_right`, or Mathlib's `Complex.Gamma_mul_ascPochhammer`-type lemma if present); so the sum is
`K_s(z) ∑ h_{ij} z^{(i)}(s-z)^{(j)} = K_s(z) H(z, s - z)` by `hrep` at `(z, s - z)`. Size: 80–150 lines. -/
theorem kH_eq_krise {H : MvPolynomial (Fin 2) ℂ} {N : ℕ} {h : ℕ → ℕ → ℂ} (hrep : IsRisingRep H N h)
    {z s : ℂ} (hz : 0 < z.re) (hsz : 0 < (s - z).re) : kH H z s = krise N (cWH h) z s := by
  have hs : 0 < s.re := by have := hsz; simp only [sub_re] at this; linarith
  unfold kH krise
  rw [hrep]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hG : Gamma (s + i + j) ≠ 0 := Gamma_ne_zero_of_re_pos (by
    simp only [add_re, natCast_re]; positivity)
  rw [gamma_shift z hz i, gamma_shift (s - z) hsz j]
  unfold cWH KerS
  field_simp
  <;> ring

end GoldbachBoundaries.Paper2.M4b
