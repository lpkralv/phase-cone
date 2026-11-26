import GoldbachBoundaries.Paper2.M4b.Fill.DCommon

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M4b

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/- Filler for `K2_kerSq` (`Kernels.lean`). Instead of M4a's `norm_KerS_le_kernelt` this bounds the three factors
directly: (Z6) for `Γ(z/2)` and `Γ(s - z/2)`, and `1/Γ` bounded on the compact `C` (continuity of the entire `1/Γ`).
With `u = |y|`, `|t| ≤ R` on `C`: `|y/2|/2 + |t - y/2|/2 ≥ u/2 - R/2`, so
`|kerSq| ≤ c(1 + u)^{x₂/2 + R}e^{-πu/2} ≤ M/(1 + u)²` (`FillD.exists_rpow_mul_exp_half_le`). -/

/-- **(K2) for `∑(p²+q²)^{-s}`** ((Z6)). `L(s) = 2s`, `D_L = {1/2 < σ < 3/2}`. Let `C ⊆ D_L` be compact, `0 < x₁ ≤ x₂` with
`x₂ < 2σ` on `C`; `C = ∅` is trivial. `kerSq(x + iy, s) = ½K_s(w)`, `w = (x + iy)/2`, `Re w ∈ [x₁/2, x₂/2]` and
`x₂/2 < σ₁ := min_C σ` (attained, `IsCompact.exists_isMinOn`), `σ₂ = max_C σ`, `T = max_C |t|`. M4a's
`norm_KerS_le_kernelt` (on `[x₁/2, x₂/2]`, `[σ₁, σ₂]`) gives
`|K_s(w)| ≤ C(1+|y/2|)^A(1+|t - y/2|)^A(1+|t|)^A e^{-π(|y/2| + |t - y/2| - |t|)/2}`, and
`|y/2| + |t - y/2| - |t| ≥ |y| - 2T`, `1 + |t - y/2| ≤ (1 + T)(1 + |y|)`. So `|kerSq| ≤ C'(1+|y|)^{2A}e^{-π|y|/2}`, and
M4a's `DCommon.exists_rpow_mul_exp_le` (after `π|y|/2 = π(|y|/2)`) bounds it by `M/(1+|y|)²`. As M4a's `K2_kr`.
Size: 150–250 lines. -/
theorem K2_kerSq (hZ6 : Z6) : K2 Aff.twoL kerSq := by
  intro C hC _ x₁ x₂ hx₁ hx₁₂ hre
  rcases C.eq_empty_or_nonempty with hCe | hne
  · exact ⟨0, fun x _ s hs => absurd hs (by rw [hCe]; exact Set.notMem_empty s)⟩
  have hre' : ∀ s ∈ C, x₂ < 2 * s.re := fun s hs => by simpa [twoL_app] using hre s hs
  obtain ⟨s₀, hs₀, hmin⟩ := hC.exists_isMinOn hne Complex.continuous_re.continuousOn
  obtain ⟨R, hR⟩ := hC.isBounded.exists_norm_le
  obtain ⟨B, hB⟩ :=
    hC.exists_bound_of_continuousOn Complex.differentiable_one_div_Gamma.continuous.continuousOn
  have hσ₁ : x₂ < 2 * s₀.re := hre' s₀ hs₀
  have hσ₁R : s₀.re ≤ R := (Complex.re_le_norm s₀).trans (hR s₀ hs₀)
  have hR0 : 0 ≤ R := (norm_nonneg _).trans (hR s₀ hs₀)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB s₀ hs₀)
  have hx₂ : 0 ≤ x₂ := by linarith
  obtain ⟨C₁, hC₁0, hC₁⟩ := FillD.Z6' hZ6 (x₁ := x₁ / 2) (x₂ := x₂ / 2) (by linarith) (by linarith)
  obtain ⟨C₂, hC₂0, hC₂⟩ := FillD.Z6' hZ6 (x₁ := s₀.re - x₂ / 2) (x₂ := R) (by linarith) (by linarith)
  obtain ⟨K, hK0, hK⟩ := FillD.exists_rpow_mul_exp_half_le (x₂ / 2 + R)
  set D : ℝ := 1 / 2 * C₁ * C₂ * B * (1 + R) ^ R * Real.exp (Real.pi * R / 2) with hD
  have hD0 : 0 ≤ D := by positivity
  refine ⟨D * K, fun x hx s hs y => ?_⟩
  set u : ℝ := |y| with hu
  have hu0 : 0 ≤ u := abs_nonneg y
  have hsn : ‖s‖ ≤ R := hR s hs
  have hσ : s₀.re ≤ s.re := hmin hs
  have hsre : s.re ≤ R := (Complex.re_le_norm s).trans hsn
  have ht : |s.im| ≤ R := (Complex.abs_im_le_norm s).trans hsn
  set t := s.im with htdef
  have e1 : ((x : ℂ) + y * I) / 2 = ((x / 2 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * I := by push_cast; ring
  have e2 : s - ((x : ℂ) + y * I) / 2 = ((s.re - x / 2 : ℝ) : ℂ) + ((t - y / 2 : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [htdef]
  have hnorm : ‖kerSq (x + y * I) s‖ =
      1 / 2 * ‖Gamma (((x / 2 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * I)‖ *
        ‖Gamma (((s.re - x / 2 : ℝ) : ℂ) + ((t - y / 2 : ℝ) : ℂ) * I)‖ * ‖(Gamma s)⁻¹‖ := by
    rw [kerSq, e2, e1, div_eq_mul_inv, norm_mul, norm_mul, norm_mul]
    norm_num
  -- the three factors
  have hy2 : |y / 2| = u / 2 := by rw [abs_div, abs_two]
  have hty : u / 2 - R ≤ |t - y / 2| := by
    have := abs_sub_abs_le_abs_sub (y / 2) t
    rw [abs_sub_comm] at this; linarith
  have hty' : |t - y / 2| ≤ R + u := by
    have := abs_sub t (y / 2); linarith
  have b1 : ‖Gamma (((x / 2 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * I)‖ ≤
      C₁ * (1 + u) ^ (x₂ / 2) * Real.exp (-(Real.pi * |y / 2| / 2)) := by
    refine (hC₁ (x / 2) ⟨by linarith [hx.1], by linarith [hx.2]⟩ (y / 2)).trans ?_
    gcongr
    rw [hy2]; linarith
  have b2 : ‖Gamma (((s.re - x / 2 : ℝ) : ℂ) + ((t - y / 2 : ℝ) : ℂ) * I)‖ ≤
      C₂ * ((1 + R) ^ R * (1 + u) ^ R) * Real.exp (-(Real.pi * |t - y / 2| / 2)) := by
    refine (hC₂ (s.re - x / 2) ⟨by linarith [hx.2], by linarith [hx.1]⟩ (t - y / 2)).trans ?_
    gcongr
    exact FillD.rpow_le_of_le_mul (abs_nonneg _) hu0 hR0 hR0 (by nlinarith)
  have b3 : ‖(Gamma s)⁻¹‖ ≤ B := hB s hs
  have pe : Real.exp (-(Real.pi * |y / 2| / 2)) * Real.exp (-(Real.pi * |t - y / 2| / 2)) ≤
      Real.exp (Real.pi * R / 2) * Real.exp (-(Real.pi * u / 2)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.2
    rw [hy2]
    nlinarith [Real.pi_pos]
  have hcomb : (1 + u) ^ (x₂ / 2) * (1 + u) ^ R = (1 + u) ^ (x₂ / 2 + R) :=
    (Real.rpow_add (by linarith) _ _).symm
  have hfin := hK u hu0
  rw [hnorm]
  have hp1 : 0 ≤ (1 + u) ^ (x₂ / 2) := Real.rpow_nonneg (by linarith) _
  have hp2 : 0 ≤ (1 + u) ^ R := Real.rpow_nonneg (by linarith) _
  have hp3 : 0 ≤ (1 + R) ^ R := Real.rpow_nonneg (by linarith) _
  calc 1 / 2 * ‖Gamma (((x / 2 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℂ) * I)‖ *
        ‖Gamma (((s.re - x / 2 : ℝ) : ℂ) + ((t - y / 2 : ℝ) : ℂ) * I)‖ * ‖(Gamma s)⁻¹‖
      ≤ 1 / 2 * (C₁ * (1 + u) ^ (x₂ / 2) * Real.exp (-(Real.pi * |y / 2| / 2))) *
        (C₂ * ((1 + R) ^ R * (1 + u) ^ R) * Real.exp (-(Real.pi * |t - y / 2| / 2))) * B := by
        gcongr
    _ = 1 / 2 * C₁ * C₂ * B * (1 + R) ^ R * ((1 + u) ^ (x₂ / 2) * (1 + u) ^ R) *
        (Real.exp (-(Real.pi * |y / 2| / 2)) * Real.exp (-(Real.pi * |t - y / 2| / 2))) := by ring
    _ ≤ 1 / 2 * C₁ * C₂ * B * (1 + R) ^ R * ((1 + u) ^ (x₂ / 2) * (1 + u) ^ R) *
        (Real.exp (Real.pi * R / 2) * Real.exp (-(Real.pi * u / 2))) := by gcongr
    _ = D * ((1 + u) ^ (x₂ / 2 + R) * Real.exp (-(Real.pi * u / 2))) := by rw [hD, ← hcomb]; ring
    _ ≤ D * (K / (1 + u) ^ 2) := by gcongr
    _ = D * K / (1 + |y|) ^ 2 := by rw [hu]; ring

end GoldbachBoundaries.Paper2.M4b
