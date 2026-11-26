import GoldbachBoundaries.Paper2.M4a.Fill.DCommon

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M4a

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/- Filler for `K2_kr` (`Kernel.lean`): the kernel bound with `|t|` bounded on `C`, times the polynomial
factor, against `e^{-π|y|}`. -/
/-- **(K2) for `k_r`** ((Z6)). `L(s) = s`, `D_L = {1 < σ < 3}`. Let `C ⊆ D_L` be compact and `0 < x₁ ≤ x₂ < Re s` on
`C`. If `C = ∅` there is nothing to prove; otherwise `σ₁ = min_C Re s > x₂` and `σ₂ = max_C Re s`, `T = max_C |Im s|`
are attained (`IsCompact.exists_isMinOn` etc.). `norm_KerS_le_kernelt` gives
`|K_s(x + iy)| ≤ C'(1 + |y|)^A(1 + |t - y|)^A(1 + T)^A e^{-π(|y| + |t - y| - |t|)/2}`, and
`|y| + |t - y| - |t| ≥ 2|y| - 2T`, `1 + |t - y| ≤ (1 + T)(1 + |y|)`. The factor
`|(z - 1)(s - 1 - z)|^r ≤ ((2 + x₂ + |y|)(3 + T + |y|))^r ≤ c(1 + |y|)^{2r}`. So
`|k_r(x + iy, s)| ≤ c'(1 + |y|)^{2A+2r}e^{-π|y|}`, and `(1 + |y|)^{N+2}e^{-π|y|}` is bounded on `ℝ` (continuous, and
`→ 0` at infinity: `Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero` after `u = 1 + |y|`), giving `M/(1 + |y|)²`. Size: 150–250 lines. -/
theorem K2_kr (hZ6 : Z6) (r : ℕ) : K2 Aff.idL (kr r) :=
  FillD.K2_kr' hZ6 r

end GoldbachBoundaries.Paper2.M4a
