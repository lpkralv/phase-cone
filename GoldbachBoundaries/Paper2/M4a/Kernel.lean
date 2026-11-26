import GoldbachBoundaries.Paper2.M4a.Order
import GoldbachBoundaries.Paper2.M4a.Fill.norm_inv_Gamma_le
import GoldbachBoundaries.Paper2.M4a.Fill.norm_KerS_le_kernelt
import GoldbachBoundaries.Paper2.M4a.Fill.integral_kernelt_le
import GoldbachBoundaries.Paper2.M4a.Fill.K2_kr

/-!
# M4a: kernel bounds (`cl:lem:kernelt`, (K2) for `k_r`)

`K_s(w) = Γ(w)Γ(s - w)/Γ(s)`. (Z6) bounds the two `Γ`'s in the numerator; `1/Γ(s)` grows at most like
`(1 + |t|)^A e^{π|t|/2}` on vertical strips `σ₁ ≤ σ ≤ σ₂` (`norm_inv_Gamma_le`; the paper uses the product formula,
the reflection formula with (Z6) is shorter). The integral bound of `cl:lem:kernelt` is elementary (split `ℝ` into
the segment between `0` and `t` and the two outer rays). (K2) for `k_r` on compact `C ⊆ D_L` is the kernel bound with
`|t|` bounded, times the polynomial `((z - 1)(s - 1 - z))^r`, against `e^{-π|y|}`.

Both targets carry RH by review choice 1; neither proof uses it.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M4a

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-! ## Lemmas

Proved in `Fill/`, one file per lemma (same name, same statement): `norm_inv_Gamma_le`, `norm_KerS_le_kernelt`, `integral_kernelt_le`, `K2_kr`. -/

/-! ## Targets -/

/-- `lem_kernelt` of `Paper2/Statements.lean`, statement verbatim. -/
theorem lem_kernelt_proof (hRH : RiemannHypothesis) (hZ6 : Z6) :
    (∀ x₁ x₂ σ₁ σ₂ : ℝ, 0 < x₁ → x₁ ≤ x₂ → x₂ < σ₁ → σ₁ ≤ σ₂ → ∃ C A : ℝ,
      ∀ x ∈ Icc x₁ x₂, ∀ y : ℝ, ∀ σ ∈ Icc σ₁ σ₂, ∀ t : ℝ,
        ‖KerS (σ + t * I) (x + y * I)‖ ≤ C * (1 + |y|) ^ A * (1 + |t - y|) ^ A * (1 + |t|) ^ A *
          Real.exp (-(Real.pi / 2 * (|y| + |t - y| - |t|)))) ∧
    ∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, ∀ t : ℝ,
      Integrable (fun y : ℝ => (1 + |y|) ^ B * (1 + |t - y|) ^ B *
        Real.exp (-(Real.pi / 2 * (|y| + |t - y| - |t|)))) ∧
      ∫ y : ℝ, (1 + |y|) ^ B * (1 + |t - y|) ^ B * Real.exp (-(Real.pi / 2 * (|y| + |t - y| - |t|))) ≤
        C * (1 + |t|) ^ (2 * B + 1) := by
  have _ := hRH  -- RH (choice 1) is not used
  exact ⟨norm_KerS_le_kernelt hZ6, integral_kernelt_le⟩

/-- `rem_order_kr_K2` of `Paper2/Statements.lean`, statement verbatim. -/
theorem rem_order_kr_K2_proof (hRH : RiemannHypothesis) (hZ6 : Z6) (r : ℕ) : K2 Aff.idL (kr r) := by
  have _ := hRH  -- RH (choice 1) is not used
  exact K2_kr hZ6 r

end GoldbachBoundaries.Paper2.M4a
