import GoldbachBoundaries.ResidueClass.JensenCount

/-! # Local logarithmic derivatives with separated evaluation points -/

noncomputable section

open Complex Set

namespace GoldbachBoundaries.ResidueClass

variable {q : ℕ} [NeZero q]

private theorem strip_zero_ne_one {χ : DirichletCharacter ℂ q} {ρ : ℂ}
    (hρ : ρ ∈ primitiveZeros χ) : ρ ≠ 1 := by
  intro h
  have hlt := hρ.2.2
  simp [h] at hlt

/-- Use the ζ input for the principal character and the Dirichlet input for
the other characters, with one constant and threshold for the family. -/
theorem exists_logDeriv_primitive_local_bound (hZ3 : Paper2.Z3) (hLocal : LogDerivPrimitiveLocal q) :
    ∃ A T₀ : ℝ, 0 ≤ A ∧ 2 ≤ T₀ ∧
      ∀ (χ : DirichletCharacter ℂ q) (z : ℂ), 0 < z.re → z.re ≤ 2 → T₀ ≤ |z.im| →
        primitiveL χ z ≠ 0 →
        ‖logDeriv (primitiveL χ) z -
          ∑ᶠ ρ ∈ {ρ ∈ primitiveZeros χ | |ρ.im - z.im| ≤ 1},
            (primitiveMult χ ρ : ℂ) / (z - ρ)‖ ≤ A * Real.log (2 + |z.im|) := by
  obtain ⟨Aζ, hζ⟩ := hZ3
  obtain ⟨Aχ, T₀, hAχ, hT, hχ⟩ := hLocal
  let A := max Aζ Aχ
  have hA : 0 ≤ A := hAχ.trans (le_max_right _ _)
  refine ⟨A, T₀, hA, hT, fun χ z hz₀ hz₂ hz hne ↦ ?_⟩
  have hlog : 0 ≤ Real.log (2 + |z.im|) := Real.log_nonneg (by linarith [abs_nonneg z.im])
  by_cases h : χ = 1
  · subst χ
    rw [primitiveL_one] at hne ⊢
    have heq :
        (∑ᶠ ρ ∈ {ρ ∈ primitiveZeros (1 : DirichletCharacter ℂ q) | |ρ.im - z.im| ≤ 1},
          (primitiveMult (1 : DirichletCharacter ℂ q) ρ : ℂ) / (z - ρ)) =
        ∑ᶠ ρ ∈ {ρ : ℂ | ρ ∈ NontrivialZeros ∧ |ρ.im - z.im| ≤ 1},
          (zetaMult ρ : ℂ) / (z - ρ) := by
      apply finsum_mem_congr
      · rw [primitiveZeros_one]
      · intro ρ hρ
        have hp : ρ ∈ primitiveZeros (1 : DirichletCharacter ℂ q) :=
          (primitiveZeros_one (q := q)).symm ▸ hρ.1
        rw [primitiveMult_one (strip_zero_ne_one hp)]
    rw [heq, logDeriv_apply]
    calc
      _ ≤ Aζ * Real.log |z.im| := hζ z (by linarith) hz₂ (hT.trans hz) hne
      _ ≤ A * Real.log |z.im| :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.log_nonneg (by linarith [hT.trans hz]))
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith [hT.trans hz]) (by linarith)) hA
  · exact (hχ χ h z hz₀ hz₂ hz hne).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hlog)

/-- Away from the strip zeros by distance at least `d`, the local formula
bounds the primitive logarithmic derivative by its remainder plus the
Jensen mass bound divided by `d`. -/
theorem exists_norm_logDeriv_primitive_le_of_separated_of_high_critical {T : ℝ}
    (hline : ∀ (χ : DirichletCharacter ℂ q) ρ, ρ ∈ primitiveZeros χ →
      T ≤ |ρ.im| → ρ.re = 1 / 2) (hZ3 : Paper2.Z3)
    (hLocal : LogDerivPrimitiveLocal q) :
    ∃ A B T₀ : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 2 ≤ T₀ ∧ T + 1 ≤ T₀ ∧
      ∀ (χ : DirichletCharacter ℂ q) (z : ℂ) (d : ℝ), 0 < d → 0 < z.re → z.re ≤ 2 →
        T₀ ≤ |z.im| → primitiveL χ z ≠ 0 →
        (∀ ρ ∈ primitiveZeros χ, |ρ.im - z.im| ≤ 1 → d ≤ ‖z - ρ‖) →
        ‖logDeriv (primitiveL χ) z‖ ≤ A * Real.log (2 + |z.im|) + B * Real.log (|z.im| + 4) / d := by
  classical
  obtain ⟨A, T₀, hA, hT, hlocal⟩ := exists_logDeriv_primitive_local_bound hZ3 hLocal
  obtain ⟨B, hB, hmass⟩ := exists_primitive_unit_radius_mass_bound_of_high_critical hline
  refine ⟨A, B, max T₀ (T + 1), hA, hB, hT.trans (le_max_left _ _), le_max_right _ _, fun χ z d hd hz₀ hz₂ hz hne hdist ↦ ?_⟩
  let W : Set ℂ := {ρ ∈ primitiveZeros χ | |ρ.im - z.im| ≤ 1}
  have hW : W.Finite := by
    refine (finite_zeroWindow χ (z.im - 1) (z.im + 1)).subset fun ρ hρ ↦ ?_
    have h := abs_le.mp hρ.2
    exact ⟨hρ.1, by constructor <;> linarith⟩
  let Q : ℂ := ∑ᶠ ρ ∈ W, (primitiveMult χ ρ : ℂ) / (z - ρ)
  have hQ : ‖Q‖ ≤ B * Real.log (|z.im| + 4) / d := by
    have hsum : ‖Q‖ ≤ (∑ᶠ ρ ∈ W, (primitiveMult χ ρ : ℝ)) / d := by
      simp only [Q, finsum_mem_eq_finite_toFinset_sum _ hW, Finset.sum_div]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun ρ hρ ↦ ?_))
      have hρW := hW.mem_toFinset.mp hρ
      rw [norm_div, Complex.norm_natCast]
      exact div_le_div_of_nonneg_left (by positivity) hd (hdist ρ hρW.1 hρW.2)
    exact hsum.trans (div_le_div_of_nonneg_right (hmass χ z.im ((le_max_right _ _).trans hz)) hd.le)
  calc
    _ = ‖(logDeriv (primitiveL χ) z - Q) + Q‖ := by rw [sub_add_cancel]
    _ ≤ ‖logDeriv (primitiveL χ) z - Q‖ + ‖Q‖ := norm_add_le _ _
    _ ≤ _ := add_le_add (hlocal χ z hz₀ hz₂ ((le_max_left _ _).trans hz) hne) hQ

theorem exists_norm_logDeriv_primitive_le_of_separated (hGRH : GRH q) (hZ3 : Paper2.Z3)
    (hLocal : LogDerivPrimitiveLocal q) :
    ∃ A B T₀ : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 2 ≤ T₀ ∧
      ∀ (χ : DirichletCharacter ℂ q) (z : ℂ) (d : ℝ), 0 < d → 0 < z.re → z.re ≤ 2 →
        T₀ ≤ |z.im| → primitiveL χ z ≠ 0 →
        (∀ ρ ∈ primitiveZeros χ, |ρ.im - z.im| ≤ 1 → d ≤ ‖z - ρ‖) →
        ‖logDeriv (primitiveL χ) z‖ ≤ A * Real.log (2 + |z.im|) + B * Real.log (|z.im| + 4) / d := by
  obtain ⟨A, B, T₀, hA, hB, hT, _, h⟩ := exists_norm_logDeriv_primitive_le_of_separated_of_high_critical
    (T := 0) (fun χ ρ hρ _ ↦ hGRH χ ρ hρ) hZ3 hLocal
  exact ⟨A, B, T₀, hA, hB, hT, h⟩

end GoldbachBoundaries.ResidueClass
