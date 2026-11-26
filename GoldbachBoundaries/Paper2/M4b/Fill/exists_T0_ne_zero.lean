import GoldbachBoundaries.Paper2.M4b.ExG

/-!
# Fill, group E2: `exists_T0_ne_zero`

`T₀ ≢ 0` (the end of the proof of `cl:prop:T0`). For real `x ≥ 5` every term of `T₀(x)` is real,
`a(p,q) = log p log q (p+q)^{-x}(1 - x + x(x+1)pq/(p+q)²)`. The term `p = q = 2` is
`log²2 · 4^{-x}(x² - 3x + 4)/4`. With `K = 1 + x + x(x+1)/4` (`|1 - x + x(x+1)pq/(p+q)²| ≤ K` as
`0 ≤ pq/(p+q)² ≤ 1/4`) and `(p+q)^{-x} ≤ (p+q)^{-(x-3)} p^{-3/2} q^{-3/2}` (`(p+q)² ≥ pq`), every other term has
`p + q ≥ 5` and `|a(p,q)| ≤ K 5^{3-x} f(p) f(q)` with `f(p) = log p · p^{-3/2}`, so the rest has absolute value at most
`K 5^{3-x} C`, `C = ∑ f(p) f(q) < ∞` (`summable_norm_Q_terms` at `3/2`). Since `K ≤ x² - 3x + 4` for `x ≥ 5`,
`T₀(x) = 0` would give `log²2 (5/4)^x ≤ 500 C`, false for a large integer `x`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M4b

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- The real term of `T₀(x)` at `(p, q)`. -/
def aT0E2 (x : ℝ) (p q : ℕ) : ℝ :=
  Real.log p * Real.log q *
    (((p + q : ℕ) : ℝ) ^ (-x) * (1 - x + x * (x + 1) * ((p * q : ℕ) : ℝ) / ((p + q : ℕ) : ℝ) ^ 2))

/-- `log p · p^{-3/2}`. -/
def fT0E2 (p : ℕ) : ℝ := Real.log p * (p : ℝ) ^ (-(3 / 2 : ℝ))

lemma aT0E2_cast (x : ℝ) (p q : ℕ) : (aT0E2 x p q : ℂ) = W0log x p q := by
  unfold aT0E2 W0log W0
  rw [Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_cpow (Nat.cast_nonneg _)]
  push_cast
  ring

lemma fT0E2_nonneg (p : ℕ) : 0 ≤ fT0E2 p :=
  mul_nonneg (Real.log_natCast_nonneg p) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

lemma summable_fT0E2 : Summable fun p : Nat.Primes => ‖fT0E2 (p : ℕ)‖ := by
  have h := summable_norm_Q_terms (z := ((3 / 2 : ℝ) : ℂ)) (by simp; norm_num)
  refine h.congr fun p => ?_
  have hp : 0 < (p : ℕ) := p.2.pos
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos hp, Complex.norm_real, Real.norm_of_nonneg
    (Real.log_natCast_nonneg _), Real.norm_of_nonneg (fT0E2_nonneg _), fT0E2]
  simp

/-- `|1 - x + x(x+1)pq/(p+q)²| ≤ 1 + x + x(x+1)/4`. -/
lemma abs_factor_le_E2 {x : ℝ} (hx : 0 ≤ x) {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) :
    |1 - x + x * (x + 1) * ((p * q : ℕ) : ℝ) / ((p + q : ℕ) : ℝ) ^ 2| ≤ 1 + x + x * (x + 1) / 4 := by
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  push_cast
  have hm : 0 < ((p : ℝ) + q) ^ 2 := by positivity
  set r : ℝ := (p : ℝ) * q / ((p : ℝ) + q) ^ 2 with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r ≤ 1 / 4 := by
    rw [hr, div_le_iff₀ hm]; nlinarith [sq_nonneg ((p : ℝ) - q)]
  have heq : x * (x + 1) * ((p : ℝ) * q) / ((p : ℝ) + q) ^ 2 = x * (x + 1) * r := by
    rw [hr]; ring
  rw [heq, abs_le]
  have hxx : 0 ≤ x * (x + 1) := by positivity
  constructor
  · nlinarith [mul_nonneg hxx hr0]
  · nlinarith [mul_le_mul_of_nonneg_left hr1 hxx]

/-- `m^{-x} ≤ m^{-(x-3)} p^{-3/2} q^{-3/2}` when `pq ≤ m²`. -/
lemma rpow_split_le_E2 {x : ℝ} {m p q : ℝ} (hp : 0 < p) (hq : 0 < q) (hm : 0 < m) (hpq : p * q ≤ m ^ 2) :
    m ^ (-x) ≤ m ^ (-(x - 3)) * (p ^ (-(3 / 2 : ℝ)) * q ^ (-(3 / 2 : ℝ))) := by
  have h1 : m ^ (-x) = m ^ (-(x - 3)) * m ^ (-3 : ℝ) := by
    rw [← Real.rpow_add hm]; ring_nf
  have h2 : m ^ (-3 : ℝ) = (m ^ 2) ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hm.le]; norm_num
  rw [h1, h2, ← Real.mul_rpow hp.le hq.le]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (mul_pos hp hq) hpq (by norm_num))
    (Real.rpow_nonneg hm.le _)

/-- `|a(p,q)| ≤ K (p+q)^{-(x-3)} f(p) f(q)`. -/
lemma norm_aT0E2_le {x : ℝ} (hx : 3 ≤ x) {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) :
    ‖aT0E2 x p q‖ ≤ (1 + x + x * (x + 1) / 4) * ((p + q : ℕ) : ℝ) ^ (-(x - 3)) * (fT0E2 p * fT0E2 q) := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hm : (0 : ℝ) < ((p + q : ℕ) : ℝ) := by push_cast; linarith
  have hpq : (p : ℝ) * q ≤ ((p + q : ℕ) : ℝ) ^ 2 := by push_cast; nlinarith
  have hlp := Real.log_natCast_nonneg p
  have hlq := Real.log_natCast_nonneg q
  have hfac := abs_factor_le_E2 (by linarith : (0 : ℝ) ≤ x) hp hq
  have hpow := rpow_split_le_E2 (x := x) hp' hq' hm hpq
  have hrp : 0 ≤ ((p + q : ℕ) : ℝ) ^ (-x) := Real.rpow_nonneg hm.le _
  unfold aT0E2 fT0E2
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg hlp, abs_of_nonneg hlq,
    abs_of_nonneg hrp]
  calc Real.log p * Real.log q * (((p + q : ℕ) : ℝ) ^ (-x) *
        |1 - x + x * (x + 1) * ((p * q : ℕ) : ℝ) / ((p + q : ℕ) : ℝ) ^ 2|)
      ≤ Real.log p * Real.log q * ((((p + q : ℕ) : ℝ) ^ (-(x - 3)) *
          ((p : ℝ) ^ (-(3 / 2 : ℝ)) * (q : ℝ) ^ (-(3 / 2 : ℝ)))) * (1 + x + x * (x + 1) / 4)) := by
        gcongr
    _ = _ := by ring

lemma five_le_of_ne_E2 {pq : Nat.Primes × Nat.Primes}
    (hne : pq ≠ (⟨2, Nat.prime_two⟩, ⟨2, Nat.prime_two⟩)) : 5 ≤ (pq.1 : ℕ) + (pq.2 : ℕ) := by
  obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := pq
  show 5 ≤ p + q
  have h1 := hp.two_le
  have h2 := hq.two_le
  have hp3 : p ≠ 2 → 3 ≤ p := fun h => by omega
  have hq3 : q ≠ 2 → 3 ≤ q := fun h => by omega
  by_cases e1 : p = 2
  · by_cases e2 : q = 2
    · subst e1; subst e2; exact absurd rfl hne
    · have := hq3 e2; omega
  · have := hp3 e1; omega

/-- **`T₀ ≢ 0`** (the end of the proof of `cl:prop:T0`). For real `x ≥ 3` the term `p = q = 2` of `T₀(x)` is
`log²2 · 4^{-x}(x² - 3x + 4)/4`; every other term has `p + q ≥ 5` and `|1 - x + x(x+1)pq/(p+q)²| ≤ 1 + x + x(x+1)/4`
(`pq ≤ (p+q)²/4`), so the rest is at most `(1 + x + x(x+1)/4) 5^{3-x} ∑ log p log q (p+q)^{-3}` (`(p+q)^{-x} ≤
5^{3-x}(p+q)^{-3}`; the last sum converges, `hypR_kerG_WT` at `σ = 3`). Multiply by `4^x/x²`: the main term tends to
`log²2/4 > 0` and the rest is `O((4/5)^x) → 0`, so `T₀(x) ≠ 0` for large real `x`. No numerical constant is needed
(the tail constant `T(3)` stays unspecified; mpmath gives `T₀(x)/(term at (2,2)) = 6.45, 2.29, 1.39, 1.04` at
`x = 3, 6, 10, 20`). Isolating the term:
`tsum_eq_add_tsum_ite` at `((2,2) : Primes × Primes)`, with `Summable.tsum_le_tsum` on the rest. Size: 200–350
lines. -/
theorem exists_T0_ne_zero : ∃ s : ℂ, 2 < s.re ∧ T0 s ≠ 0 := by
  classical
  -- the constant `C = ∑ f(p) f(q)`
  have hb : Summable fun pq : Nat.Primes × Nat.Primes => fT0E2 (pq.1 : ℕ) * fT0E2 (pq.2 : ℕ) :=
    summable_mul_of_summable_norm (R := ℝ) (f := fun p : Nat.Primes => fT0E2 (p : ℕ))
      (g := fun p : Nat.Primes => fT0E2 (p : ℕ)) summable_fT0E2 summable_fT0E2
  set C : ℝ := ∑' pq : Nat.Primes × Nat.Primes, fT0E2 (pq.1 : ℕ) * fT0E2 (pq.2 : ℕ) with hCdef
  have hl2 : 0 < Real.log 2 ^ 2 := by have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity
  -- choose the point
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (500 * C / Real.log 2 ^ 2) (by norm_num : (1 : ℝ) < 5 / 4)
  set N : ℕ := n + 5 with hN
  set x : ℝ := (N : ℝ) with hxdef
  have hx5 : (5 : ℝ) ≤ x := by rw [hxdef, hN]; push_cast; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have hx3 : (3 : ℝ) ≤ x := by linarith
  refine ⟨(x : ℂ), by simp; linarith, ?_⟩
  -- `T₀(x)` is the real series
  have hT : T0 (x : ℂ) = ((∑' pq : Nat.Primes × Nat.Primes, aT0E2 x (pq.1 : ℕ) (pq.2 : ℕ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    simp only [T0, Dser, aT0E2_cast]
  rw [hT, Complex.ofReal_ne_zero]
  intro h0
  set K : ℝ := 1 + x + x * (x + 1) / 4 with hK
  have hK0 : 0 < K := by rw [hK]; positivity
  -- summability of the real terms
  have hsa : Summable fun pq : Nat.Primes × Nat.Primes => aT0E2 x (pq.1 : ℕ) (pq.2 : ℕ) := by
    refine Summable.of_norm_bounded (hb.mul_left K) fun pq => ?_
    refine (norm_aT0E2_le hx3 pq.1.2.one_le pq.2.2.one_le).trans ?_
    have hm : (1 : ℝ) ≤ (((pq.1 : ℕ) + (pq.2 : ℕ) : ℕ) : ℝ) := by
      have := pq.1.2.one_le; exact_mod_cast (by omega : 1 ≤ (pq.1 : ℕ) + (pq.2 : ℕ))
    have hle : (((pq.1 : ℕ) + (pq.2 : ℕ) : ℕ) : ℝ) ^ (-(x - 3)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hm (by linarith)
    have hfg := mul_nonneg (fT0E2_nonneg (pq.1 : ℕ)) (fT0E2_nonneg (pq.2 : ℕ))
    calc K * (((pq.1 : ℕ) + (pq.2 : ℕ) : ℕ) : ℝ) ^ (-(x - 3)) * (fT0E2 (pq.1 : ℕ) * fT0E2 (pq.2 : ℕ))
        ≤ K * 1 * (fT0E2 (pq.1 : ℕ) * fT0E2 (pq.2 : ℕ)) := by gcongr
      _ = _ := by ring
  set two : Nat.Primes × Nat.Primes := (⟨2, Nat.prime_two⟩, ⟨2, Nat.prime_two⟩) with htwo
  rw [hsa.tsum_eq_add_tsum_ite two] at h0
  -- the tail
  have htail : ‖∑' pq : Nat.Primes × Nat.Primes,
      (if pq = two then 0 else aT0E2 x (pq.1 : ℕ) (pq.2 : ℕ))‖ ≤ K * (5 : ℝ) ^ (-(x - 3)) * C := by
    refine tsum_of_norm_bounded (hb.hasSum.mul_left (K * (5 : ℝ) ^ (-(x - 3)))) fun pq => ?_
    have hfg := mul_nonneg (fT0E2_nonneg (pq.1 : ℕ)) (fT0E2_nonneg (pq.2 : ℕ))
    split_ifs with h
    · rw [norm_zero]; have : 0 ≤ (5 : ℝ) ^ (-(x - 3)) := by positivity
      positivity
    · refine (norm_aT0E2_le hx3 pq.1.2.one_le pq.2.2.one_le).trans ?_
      have h5 : (5 : ℝ) ≤ (((pq.1 : ℕ) + (pq.2 : ℕ) : ℕ) : ℝ) := by
        exact_mod_cast five_le_of_ne_E2 h
      have hle : (((pq.1 : ℕ) + (pq.2 : ℕ) : ℕ) : ℝ) ^ (-(x - 3)) ≤ (5 : ℝ) ^ (-(x - 3)) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) h5 (by linarith)
      calc K * (((pq.1 : ℕ) + (pq.2 : ℕ) : ℕ) : ℝ) ^ (-(x - 3)) * (fT0E2 (pq.1 : ℕ) * fT0E2 (pq.2 : ℕ))
          ≤ K * (5 : ℝ) ^ (-(x - 3)) * (fT0E2 (pq.1 : ℕ) * fT0E2 (pq.2 : ℕ)) := by gcongr
        _ = _ := by ring
  -- the main term
  have h4 : (4 : ℝ) ^ (-x) = ((4 : ℝ) ^ N)⁻¹ := by
    rw [Real.rpow_neg (by norm_num), hxdef, Real.rpow_natCast]
  have h5 : (5 : ℝ) ^ (-(x - 3)) = 125 * ((5 : ℝ) ^ N)⁻¹ := by
    rw [show -(x - 3) = 3 + -x by ring, Real.rpow_add (by norm_num), Real.rpow_neg (by norm_num), hxdef,
      Real.rpow_natCast]
    norm_num
  have hmain : aT0E2 x 2 2 = Real.log 2 ^ 2 * ((4 : ℝ) ^ N)⁻¹ * ((x ^ 2 - 3 * x + 4) / 4) := by
    unfold aT0E2
    rw [show ((2 + 2 : ℕ) : ℝ) = 4 by norm_num, h4]
    push_cast
    ring
  have hmain' : aT0E2 x (two.1 : ℕ) (two.2 : ℕ) = aT0E2 x 2 2 := rfl
  rw [hmain', hmain] at h0
  -- `T₀(x) = 0` forces `main ≤ |tail|`
  have hle : Real.log 2 ^ 2 * ((4 : ℝ) ^ N)⁻¹ * ((x ^ 2 - 3 * x + 4) / 4) ≤
      K * (125 * ((5 : ℝ) ^ N)⁻¹) * C := by
    rw [← h5]
    have h0' : Real.log 2 ^ 2 * ((4 : ℝ) ^ N)⁻¹ * ((x ^ 2 - 3 * x + 4) / 4) =
        -∑' pq : Nat.Primes × Nat.Primes, (if pq = two then 0 else aT0E2 x (pq.1 : ℕ) (pq.2 : ℕ)) := by
      linarith
    rw [h0']
    exact (neg_le_abs _).trans (by simpa [Real.norm_eq_abs] using htail)
  -- `K ≤ x² - 3x + 4` for `x ≥ 5`
  have hKle : K ≤ x ^ 2 - 3 * x + 4 := by rw [hK]; nlinarith
  have h4pos : (0 : ℝ) < (4 : ℝ) ^ N := by positivity
  have h5pos : (0 : ℝ) < (5 : ℝ) ^ N := by positivity
  have hC0 : 0 ≤ C := tsum_nonneg fun pq => mul_nonneg (fT0E2_nonneg _) (fT0E2_nonneg _)
  -- so `log²2 · 5^N ≤ 500 C · 4^N`
  have hkey : Real.log 2 ^ 2 * (5 : ℝ) ^ N ≤ 500 * C * (4 : ℝ) ^ N := by
    have h1 : Real.log 2 ^ 2 * ((4 : ℝ) ^ N)⁻¹ * (K / 4) ≤ K * (125 * ((5 : ℝ) ^ N)⁻¹) * C := by
      refine le_trans ?_ hle
      gcongr
    have h2 : Real.log 2 ^ 2 * ((4 : ℝ) ^ N)⁻¹ ≤ 500 * ((5 : ℝ) ^ N)⁻¹ * C := by
      have := (mul_le_mul_iff_of_pos_right (by positivity : (0 : ℝ) < K / 4)).mp
        (by nlinarith [h1] : Real.log 2 ^ 2 * ((4 : ℝ) ^ N)⁻¹ * (K / 4) ≤
          500 * ((5 : ℝ) ^ N)⁻¹ * C * (K / 4))
      exact this
    have h3 := mul_le_mul_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ (4 : ℝ) ^ N * (5 : ℝ) ^ N)
    have e1 : Real.log 2 ^ 2 * ((4 : ℝ) ^ N)⁻¹ * ((4 : ℝ) ^ N * (5 : ℝ) ^ N) =
        Real.log 2 ^ 2 * (5 : ℝ) ^ N := by field_simp
    have e2 : 500 * ((5 : ℝ) ^ N)⁻¹ * C * ((4 : ℝ) ^ N * (5 : ℝ) ^ N) = 500 * C * (4 : ℝ) ^ N := by
      field_simp
    linarith
  -- contradiction with the choice of `n`
  have hpow : (5 / 4 : ℝ) ^ n ≤ (5 / 4 : ℝ) ^ N := pow_le_pow_right₀ (by norm_num) (by omega)
  have hdiv : (5 / 4 : ℝ) ^ N = (5 : ℝ) ^ N / (4 : ℝ) ^ N := div_pow _ _ _
  have hfin : 500 * C < Real.log 2 ^ 2 * ((5 : ℝ) ^ N / (4 : ℝ) ^ N) := by
    rw [div_lt_iff₀ hl2] at hn
    rw [← hdiv]
    nlinarith
  rw [mul_div_assoc', lt_div_iff₀ h4pos] at hfin
  linarith

end GoldbachBoundaries.Paper2.M4b
