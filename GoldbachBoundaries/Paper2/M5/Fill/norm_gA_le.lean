import GoldbachBoundaries.Paper2.M5.Fill.F1Common

/-! # Filler F1: `norm_gA_le` (statement verbatim from `Paper2/M5/FilterI.lean`; proof in `F1Common.lean`) -/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

theorem norm_gA_le (hRH : RiemannHypothesis) (H : MvPolynomial (Fin 2) ℂ) {K : Set ℂ} (hK : IsCompact K)
    {c₁ c₂ : ℝ} (hc₁ : 1 / 2 < c₁) (hc₁₂ : c₁ ≤ c₂) (hc₂ : ∀ s ∈ K, c₂ + 1 / 2 < s.re) :
    ∃ M : ℝ, ∀ s ∈ K, ∀ z : ℂ, c₁ ≤ z.re → z.re ≤ c₂ → ‖gA H s z‖ ≤ M / (1 + |z.im|) ^ 2 :=
  F1_norm_gA_le hRH H hK hc₁ hc₁₂ hc₂

end GoldbachBoundaries.Paper2.M5
