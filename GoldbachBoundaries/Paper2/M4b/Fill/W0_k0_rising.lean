import GoldbachBoundaries.Paper2.M4b.MB

noncomputable section
open Complex
namespace GoldbachBoundaries.Paper2.M4b
open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **`W₀` and `k₀` as rising combinations** (`cl:prop:T0`, proof). Weight: `Wrise 2 cW0` has two non-zero terms,
`(1 - s)(p+q)^{-s}` and `s(s+1)pq(p+q)^{-(s+2)}`, and `(p+q)^{-s}/(p+q)² = (p+q)^{-(s+2)}` for `p + q ≠ 0`
(`Complex.cpow_sub`, `cpow_natCast`); `W₀` is `(p+q)^{-s}(1 - s + s(s+1)pq/(p+q)²)`. Kernel: with `Re z > 0`,
`Re(s - z) > 0` (so `Re s > 0`, `s ≠ 0, -1`, `Γ(s) ≠ 0`): `Γ(z+1) = zΓ(z)`, `Γ(s-z+1) = (s-z)Γ(s-z)`,
`Γ(s+2) = (s+1)sΓ(s)` (`Complex.Gamma_add_one`), so `krise 2 cW0 z s = K_s(z)[(1 - s) + z(s - z)]` and
`(1 - s) + z(s - z) = (z - 1)(s - 1 - z)`. Size: 80–150 lines. -/
theorem W0_k0_rising :
    (∀ s : ℂ, ∀ p q : ℕ, 0 < p + q → W0 s p q = Wrise 2 cW0 s p q) ∧
    ∀ z s : ℂ, 0 < z.re → 0 < (s - z).re → k0 z s = krise 2 cW0 z s := by
  constructor
  · intro s p q hpq
    have hn : ((p + q : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hpq)
    have he : (((p + q : ℕ) : ℂ)) ^ (-(s + 1 + 1)) =
        (((p + q : ℕ) : ℂ)) ^ (-s) / (((p + q : ℕ) : ℂ)) ^ 2 := by
      rw [show -(s + 1 + 1) = -s - (2 : ℂ) by ring, cpow_sub _ _ hn, cpow_ofNat]
    simp only [Wrise, Finset.sum_range_succ, Finset.sum_range_zero, cW0]
    norm_num only [Nat.reduceEqDiff, and_self, ite_true, and_false, false_and, ite_false, zero_mul, mul_zero, zero_add, add_zero, pow_zero, pow_one, mul_one, Nat.cast_zero, Nat.cast_one]
    rw [he]
    simp only [W0, Nat.cast_mul]
    ring
  · intro z s hz hsz
    have hs : 0 < s.re := by have := hsz; simp only [sub_re] at this; linarith
    have hz0 : z ≠ 0 := by intro h; simp [h] at hz
    have hsz0 : s - z ≠ 0 := by intro h; simp [h] at hsz
    have hs0 : s ≠ 0 := by intro h; simp [h] at hs
    have hs1 : s + 1 ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hG := Gamma_ne_zero_of_re_pos hs
    simp only [krise, Finset.sum_range_succ, Finset.sum_range_zero, cW0]
    norm_num
    rw [Gamma_add_one z hz0, Gamma_add_one (s - z) hsz0,
      Gamma_add_one (s + 1) hs1, Gamma_add_one s hs0]
    unfold k0 KerS
    field_simp
    <;> ring

end GoldbachBoundaries.Paper2.M4b
