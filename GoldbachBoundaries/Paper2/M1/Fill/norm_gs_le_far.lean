import GoldbachBoundaries.Paper2.M1.Fill.E1Common

/-!
# Filler E1: `norm_gs_le_far`

The proof is `E1_norm_gs_le_far` in `E1Common.lean`: a good height `H` (`exists_goodHeight`), `Y = H + |τ₀|`,
`nr:lem:growthQ` at `w` and at `s - w` (`norm_Qcont_le_growth`), the kernel bound with `n = 4`
(`norm_KerS_mul_pow_le`), and `log x ≤ x - 1`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M1

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **The integrand far from the real axis** (Z1, Z2, Z3). For `δ > 0`, `B_∞ + 2δ ≤ c₁`, `c₂ + B_∞ + 2δ ≤ σ₁`, there
are `C, Y` such that for `s` in the rectangle `σ₁ ≤ σ ≤ σ₂`, `|τ| ≤ τ₀` and `c₁ ≤ Re w ≤ c₂`, `|Im w| ≥ Y`: neither
`w` nor `s - w` is in `Σ_Q`, and `|K_s(w) Q(w) Q(s - w)| ≤ C (1 + |Im w|)^{-2}`. (`Y = H + τ₀` for a good height
`H`; `norm_Qcont_le_growth` at `w` and at `s - w`, whose real part is `≥ σ₁ - c₂ ≥ B_∞ + 2δ`; `norm_KerS_mul_pow_le`
with `n = 4`.) Uses: `exists_goodHeight`, `norm_Qcont_le_growth`, `not_mem_poleSetQ_of_goodHeight`,
`norm_KerS_mul_pow_le`, `half_le_Binf`. Size: 150–250 lines. -/
theorem norm_gs_le_far (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) {δ : ℝ} (hδ : 0 < δ) {c₁ c₂ σ₁ σ₂ τ₀ : ℝ}
    (hc₁ : Binf + 2 * δ ≤ c₁) (hσ₁ : c₂ + Binf + 2 * δ ≤ σ₁) :
    ∃ C Y : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → |s.im| ≤ τ₀ → ∀ w : ℂ, c₁ ≤ w.re → w.re ≤ c₂ →
      Y ≤ |w.im| → w ∉ PoleSetQ ∧ s - w ∉ PoleSetQ ∧
        ‖KerS s w * Qcont w * Qcont (s - w)‖ ≤ C / (1 + |w.im|) ^ 2 :=
  E1_norm_gs_le_far hZ1 hZ2 hZ3 hδ hc₁ hσ₁

end GoldbachBoundaries.Paper2.M1
