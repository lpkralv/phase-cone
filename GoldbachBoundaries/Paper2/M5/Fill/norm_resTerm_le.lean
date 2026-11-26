import GoldbachBoundaries.Paper2.M5.Fill.F2Common
import GoldbachBoundaries.Paper2.M5.Fill.summable_zeros_inv_sq

/-!
# Fill: `norm_resTerm_le`

`η resTerm(s, ρ) = R_ρ · k_H(ρ, s) · (η Qcont(s - ρ))` with `s = 1 + iτ₀ + η`, `ρ = 1/2 + iγ` (RH). The three factors:
`|R_ρ| = m(ρ) ≤ C log(|γ| + 3)` (M4a's `Rcoef_div_of_RH` with `n = 1`, M2's `zetaMult_le_log`);
`|k_H(ρ, s)| ≤ K(1 + |γ|)^{-4}` (`norm_kH_mul_pow_le`: `Re ρ = 1/2 < 1 ≤ Re s ≤ 5/4`, `|Im s| = |τ₀|`);
`η|Qcont(s - ρ)| ≤ C log(|τ₀ - γ| + 3)` (`Qleft_iii`: `Re(s - ρ) = 1/2 + η ∈ (1/2, 3/4]`). With `log x ≤ x - 1` the
product is `≤ B(1 + |γ|)^{-2}`, summable by `summable_zeros_inv_sq`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

theorem norm_resTerm_le (hRH : RiemannHypothesis) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (H : MvPolynomial (Fin 2) ℂ)
    (τ₀ : ℝ) :
    ∃ μ : NontrivialZeros → ℝ, Summable μ ∧ ∀ η : ℝ, 0 < η → η ≤ 1 / 4 → ∀ ρ : NontrivialZeros,
      ‖(η : ℂ) * resTerm H (1 + τ₀ * I + η) ρ‖ ≤ μ ρ := by
  obtain ⟨Cq, hCq⟩ := Qleft_iii hRH hZ1 hZ2 hZ3
  obtain ⟨Cm, hCm⟩ := M2.zetaMult_le_log hZ1 hZ2
  obtain ⟨K, hK⟩ := norm_kH_mul_pow_le H (x₁ := 1 / 2) (x₂ := 1 / 2) (σ₁ := 1) (σ₂ := 5 / 4) (τ := |τ₀|)
    (by norm_num) (by norm_num) 4
  set B : ℝ := 2 * |Cm| * |K| * (|Cq| * (|τ₀| + 3)) with hB
  refine ⟨fun ρ => B * (1 / (1 + |(ρ : ℂ).im|) ^ 2), (summable_zeros_inv_sq hZ1 hZ2).mul_left B, ?_⟩
  intro η hη hη' ρ
  set s : ℂ := 1 + τ₀ * I + η with hs
  set γ : ℝ := (ρ : ℂ).im with hγ
  have hre : (ρ : ℂ).re = 1 / 2 := sigmaFinite_re_eq_half hRH ρ.2
  have hsre : s.re = 1 + η := by simp [hs]
  have hsim : s.im = τ₀ := by simp [hs]
  have hwre : (s - ρ).re = 1 / 2 + η := by rw [sub_re, hsre, hre]; ring
  have hwim : (s - ρ).im = τ₀ - γ := by rw [sub_im, hsim]
  -- the `Q` factor
  obtain ⟨-, hQ⟩ := hCq (s - ρ) (by rw [hwre]; linarith) (by rw [hwre]; linarith)
  rw [hwre, hwim] at hQ
  have hγ0 : 0 ≤ |γ| := abs_nonneg γ
  have hτ0 : 0 ≤ |τ₀| := abs_nonneg τ₀
  have hlogpos : 0 ≤ Real.log (|τ₀ - γ| + 3) := Real.log_nonneg (by have := abs_nonneg (τ₀ - γ); linarith)
  have hQ' : η * ‖Qcont (s - ρ)‖ ≤ |Cq| * ((|τ₀| + 3) * (1 + |γ|)) := by
    have h1 : (1 / 2 + η - 1 / 2) = η := by ring
    rw [h1] at hQ
    have h2 : Real.log (|τ₀ - γ| + 3) ≤ (|τ₀| + 3) * (1 + |γ|) := by
      have h3 := Real.log_le_sub_one_of_pos (x := |τ₀ - γ| + 3) (by have := abs_nonneg (τ₀ - γ); linarith)
      have h4 : |τ₀ - γ| ≤ |τ₀| + |γ| := abs_sub _ _
      nlinarith
    calc η * ‖Qcont (s - ρ)‖ ≤ Cq * Real.log (|τ₀ - γ| + 3) := hQ
      _ ≤ |Cq| * Real.log (|τ₀ - γ| + 3) := mul_le_mul_of_nonneg_right (le_abs_self _) hlogpos
      _ ≤ |Cq| * ((|τ₀| + 3) * (1 + |γ|)) := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
  -- the residue factor
  have hR : ‖Rcoef (ρ : ℂ)‖ ≤ |Cm| * (2 * (1 + |γ|)) := by
    have h1 := M4a.Rcoef_div_of_RH hRH (n := 1) le_rfl squarefree_one ρ.2
    simp only [Nat.cast_one, div_one] at h1
    have hmu : mu 1 = 1 := by simp [mu]
    rw [h1, hmu, one_mul, norm_neg, Complex.norm_natCast]
    have h2 := hCm ρ ρ.2
    have h3 := Real.log_le_sub_one_of_pos (x := |γ| + 3) (by linarith)
    have hlog0 : 0 ≤ Real.log (|γ| + 3) := Real.log_nonneg (by linarith)
    calc (zetaMult (ρ : ℂ) : ℝ) ≤ Cm * Real.log (|γ| + 3) := h2
      _ ≤ |Cm| * Real.log (|γ| + 3) := mul_le_mul_of_nonneg_right (le_abs_self _) hlog0
      _ ≤ |Cm| * (2 * (1 + |γ|)) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
  -- the kernel factor
  have ha : 0 < 1 + |γ| := by linarith
  have hk : ‖kH H (ρ : ℂ) s‖ ≤ |K| / (1 + |γ|) ^ 4 := by
    have h := hK s (by rw [hsre]; linarith) (by rw [hsre]; linarith) (by rw [hsim]) ρ (by rw [hre]) (by rw [hre])
    rw [le_div_iff₀ (by positivity)]
    exact h.trans (le_abs_self K)
  -- assemble
  have heq : (η : ℂ) * resTerm H s ρ = Rcoef (ρ : ℂ) * kH H (ρ : ℂ) s * ((η : ℂ) * Qcont (s - ρ)) := by
    unfold resTerm kH; ring
  rw [heq, norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hη.le]
  have hQn : 0 ≤ η * ‖Qcont (s - ρ)‖ := by positivity
  calc ‖Rcoef (ρ : ℂ)‖ * ‖kH H (ρ : ℂ) s‖ * (η * ‖Qcont (s - ρ)‖)
      ≤ (|Cm| * (2 * (1 + |γ|))) * (|K| / (1 + |γ|) ^ 4) * (|Cq| * ((|τ₀| + 3) * (1 + |γ|))) := by
        gcongr
    _ = B * (1 / (1 + |γ|) ^ 2) := by
        rw [hB]; field_simp

end GoldbachBoundaries.Paper2.M5
