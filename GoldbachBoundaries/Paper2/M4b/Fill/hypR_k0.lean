import GoldbachBoundaries.Paper2.M4b.ExG
import GoldbachBoundaries.Paper2.M4b.Fill.E1Common

noncomputable section
open Complex
namespace GoldbachBoundaries.Paper2.M4b
open GoldbachBoundaries GoldbachBoundaries.Paper2

private lemma W0_real (x : ℝ) (p q : ℕ) : (W0 x p q).im = 0 := by
  have he : (((p + q : ℕ) : ℂ) ^ (-(x : ℂ))).im = 0 := by
    simpa using E1_cpow_real (p + q) (-x)
  simp only [W0, mul_im, div_im, sub_im, add_im, one_im, ofReal_im,
    natCast_im, pow_two, mul_im, zero_sub, zero_add, add_zero, zero_mul, mul_zero,
    sub_zero, zero_div, he]

private lemma hypR_k0_weight {ω : ℕ → ℝ} (hω : PrimeWeight ω) :
    HypR Aff.idL k0 (wtd ω W0) (primeSum ω) := by
  apply E1_hypR_rising hω 2 cW0 differentiableOn_cW0
  · intro s pq
    unfold wtd
    rw [W0_k0_rising.1 s (pq.1 : ℕ) (pq.2 : ℕ) (by have := pq.1.prop.pos; omega)]
  · exact W0_k0_rising.2
  · intro x _ pq
    simp [wtd, mul_im, W0_real]

/-- **(R) for `T₀` and `G₀`** (no hypothesis). Weights: `W0log = wtd log W0` (`W0log_eq_wtd`), and on primes
`W₀ = Wrise 2 cW0` (`W0_k0_rising`, `p + q > 0`; transfer with `dser_congr` and, for summability and holomorphy,
termwise equality on primes). Absolute convergence, holomorphy and the identity: `rising_summable_eq`,
`rising_differentiableOn` (`differentiableOn_cW0`) with `ω = log`, resp. `ω = 1`; the kernels agree on the line
(`W0_k0_rising`: `Re z = c > 0`, `Re(s - z) = σ - c > 1`). Reality: for real `x` every term
`log p log q (p+q)^{-x}(1 - x + x(x+1)pq/(p+q)²)` is real (`Complex.im_tsum`). Size: 100–200 lines. -/
theorem hypR_k0 : HypR Aff.idL k0 W0log Q ∧ HypR Aff.idL k0 W0 P := by
  constructor
  · simpa only [← W0log_eq_wtd, primeSum_log] using hypR_k0_weight primeWeight_log
  · simpa only [wtd_one, primeSum_one] using hypR_k0_weight primeWeight_one

end GoldbachBoundaries.Paper2.M4b
