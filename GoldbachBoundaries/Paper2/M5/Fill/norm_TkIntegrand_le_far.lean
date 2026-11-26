import GoldbachBoundaries.Paper2.M5.Fill.T2Common

/-!
# Fill: `norm_TkIntegrand_le_far`

`T2.norm_far` (`Fill/T2Common.lean`): field 8 of the package bounds `F` by `C|Im w|^N` on the strip, M1's
`norm_KerS_mul_pow_le` gives `|K_s(w)| ≤ C(1+|Im w|)^{-(⌈N⌉+3)}` uniformly on `K`, and paper 1's `norm_Qcont_le_log`
with `ε = min_K σ - c₂ - 1/2` gives `|Qcont(s - w)| ≤ C log|Im(s - w)| ≤ C(1 + T)(1 + |Im w|)`.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2

theorem norm_TkIntegrand_le_far (hRH : RiemannHypothesis) {m : ℕ} (hm : 1 ≤ m) {F H : ℂ → ℂ} (hP : TkPack m F H)
    {K : Set ℂ} (hK : IsCompact K) {c₁ c₂ : ℝ} (hc₁ : (m : ℝ) - 1 / 2 < c₁) (hc₁₂ : c₁ ≤ c₂)
    (hc₂ : ∀ s ∈ K, c₂ + 1 / 2 < s.re) :
    ∃ M Y : ℝ, ∀ s ∈ K, ∀ w : ℂ, c₁ ≤ w.re → w.re ≤ c₂ → Y ≤ |w.im| →
      ‖KerS s w * F w * Qcont (s - w)‖ ≤ M / (1 + |w.im|) ^ 2 :=
  T2.norm_far hRH hm hP hK hc₁ hc₁₂ hc₂

end GoldbachBoundaries.Paper2.M5
