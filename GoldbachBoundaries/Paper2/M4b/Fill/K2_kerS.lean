import GoldbachBoundaries.Paper2.M4b.Fill.DCommon

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M4b

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/- Filler for `K2_kerS` (`Kernels.lean`): (Z6) for both factors of `K(w) = Γ(w)Γ(2 - w)`, with real parts in
`[(x₁ - σ₂ + 1)/2, (x₂ + R + 1)/2]` and `[(3 - x₂ + σ₁)/2, (3 + R)/2]` (`σ₁ = min_C σ`, `σ₂ = max_C σ < 1`,
`R ≥ |s|` on `C`), then `|Im w| ≥ (|y| - R)/2` and `FillD.exists_rpow_mul_exp_half_le`. -/

/-- **(K2) for `S`** ((Z6)). `L(s) = 2s + 1`, `D_L = {0 < σ < 1}`. For compact `C ⊆ D_L` and `[x₁, x₂]` with `0 < x₁`,
`x₂ < 2σ + 1` on `C`: `kerS(x + iy, s) = ½Γ(w)Γ(2 - w)` with `w = (x - σ + 1)/2 + i(y - t)/2`.
`Re w ≥ (x₁ - σ₂ + 1)/2 > 0` (`σ₂ = max_C σ < 1`) and `Re(2 - w) = (3 - x + σ)/2 ≥ (3 - x₂ + σ₁)/2 > 0`
(`x₂ < 2σ₁ + 1`), both in a compact subinterval of `(0, ∞)`. (Z6) twice (the second at `Im(2 - w) = -Im w`):
`|K(w)| ≤ C²(1 + |Im w|)^{2a}e^{-π|Im w|}`, and `|Im w| ≥ (|y| - T)/2`, `T = max_C |t|`. So
`|kerS| ≤ C'(1 + |y|)^{2a}e^{-π|y|/2}`, then `M/(1+|y|)²` as in `K2_kerSq`. Size: 150–250 lines. -/
theorem K2_kerS (hZ6 : Z6) : K2 Aff.twoOneL kerS := by
  intro C hC hCD x₁ x₂ hx₁ hx₁₂ hre
  rcases C.eq_empty_or_nonempty with hCe | hne
  · exact ⟨0, fun x _ s hs => absurd hs (by rw [hCe]; exact Set.notMem_empty s)⟩
  have hre' : ∀ s ∈ C, x₂ < 2 * s.re + 1 := fun s hs => by simpa [twoOneL_app] using hre s hs
  have hlt1 : ∀ s ∈ C, s.re < 1 := fun s hs => by
    have h : (Aff.twoOneL.app s).re < 3 := (hCD hs).2
    rw [twoOneL_app] at h
    simp at h
    linarith
  obtain ⟨s₀, hs₀, hmin⟩ := hC.exists_isMinOn hne Complex.continuous_re.continuousOn
  obtain ⟨s₁, hs₁, hmax⟩ := hC.exists_isMaxOn hne Complex.continuous_re.continuousOn
  obtain ⟨R, hR⟩ := hC.isBounded.exists_norm_le
  have hσ₁ : x₂ < 2 * s₀.re + 1 := hre' s₀ hs₀
  have hσ₂ : s₁.re < 1 := hlt1 s₁ hs₁
  have hσ₁₂ : s₀.re ≤ s₁.re := hmin hs₁
  have hσ₁R : s₀.re ≤ R := (Complex.re_le_norm s₀).trans (hR s₀ hs₀)
  have hσ₂R : -s₁.re ≤ R := by
    have := (Complex.abs_re_le_norm s₁).trans (hR s₁ hs₁); rw [abs_le] at this; linarith
  have hR0 : 0 ≤ R := (norm_nonneg _).trans (hR s₀ hs₀)
  have hx₂ : 0 ≤ x₂ := by linarith
  set a₂ : ℝ := (x₂ + R + 1) / 2 with ha₂
  set b₂ : ℝ := (3 + R) / 2 with hb₂
  have ha₂0 : 0 ≤ a₂ := by rw [ha₂]; linarith
  have hb₂0 : 0 ≤ b₂ := by rw [hb₂]; linarith
  obtain ⟨C₁, hC₁0, hC₁⟩ :=
    FillD.Z6' hZ6 (x₁ := (x₁ - s₁.re + 1) / 2) (x₂ := a₂) (by linarith) (by rw [ha₂]; linarith)
  obtain ⟨C₂, hC₂0, hC₂⟩ :=
    FillD.Z6' hZ6 (x₁ := (3 - x₂ + s₀.re) / 2) (x₂ := b₂) (by linarith) (by rw [hb₂]; linarith)
  obtain ⟨K, hK0, hK⟩ := FillD.exists_rpow_mul_exp_half_le (a₂ + b₂)
  set D : ℝ := 1 / 2 * C₁ * C₂ * (1 + R) ^ a₂ * (1 + R) ^ b₂ * Real.exp (Real.pi * R / 2) with hD
  have hD0 : 0 ≤ D := by positivity
  refine ⟨D * K, fun x hx s hs y => ?_⟩
  set u : ℝ := |y| with hu
  have hu0 : 0 ≤ u := abs_nonneg y
  have hsn : ‖s‖ ≤ R := hR s hs
  have hσlo : s₀.re ≤ s.re := hmin hs
  have hσhi : s.re ≤ s₁.re := hmax hs
  have hsre : |s.re| ≤ R := (Complex.abs_re_le_norm s).trans hsn
  have ht : |s.im| ≤ R := (Complex.abs_im_le_norm s).trans hsn
  rw [abs_le] at hsre
  set t := s.im with htdef
  have e1 : ((x : ℂ) + y * I - s + 1) / 2 =
      (((x - s.re + 1) / 2 : ℝ) : ℂ) + (((y - t) / 2 : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [htdef]
  have e2 : (2 : ℂ) - ((((x - s.re + 1) / 2 : ℝ) : ℂ) + (((y - t) / 2 : ℝ) : ℂ) * I) =
      (((3 - x + s.re) / 2 : ℝ) : ℂ) + (((t - y) / 2 : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp <;> ring
  have hnorm : ‖kerS (x + y * I) s‖ =
      1 / 2 * (‖Gamma ((((x - s.re + 1) / 2 : ℝ) : ℂ) + (((y - t) / 2 : ℝ) : ℂ) * I)‖ *
        ‖Gamma ((((3 - x + s.re) / 2 : ℝ) : ℂ) + (((t - y) / 2 : ℝ) : ℂ) * I)‖) := by
    rw [kerS, KS, e1, e2, norm_mul, norm_mul]
    norm_num
  -- the imaginary part `v = |y - t|/2`
  set v : ℝ := |(y - t) / 2| with hv
  have hv' : |(t - y) / 2| = v := by rw [hv, abs_div, abs_div, abs_sub_comm]
  have hv0 : 0 ≤ v := abs_nonneg _
  have hvlo : (u - R) / 2 ≤ v := by
    rw [hv, abs_div, abs_two]
    have := abs_sub_abs_le_abs_sub y t
    linarith
  have hvhi : 1 + v ≤ (1 + R) * (1 + u) := by
    have h : v ≤ (u + R) / 2 := by
      rw [hv, abs_div, abs_two]
      have := abs_sub y t
      linarith
    nlinarith
  have b1 : ‖Gamma ((((x - s.re + 1) / 2 : ℝ) : ℂ) + (((y - t) / 2 : ℝ) : ℂ) * I)‖ ≤
      C₁ * ((1 + R) ^ a₂ * (1 + u) ^ a₂) * Real.exp (-(Real.pi * v / 2)) := by
    refine (hC₁ ((x - s.re + 1) / 2) ⟨by linarith [hx.1], by rw [ha₂]; linarith [hx.2]⟩
      ((y - t) / 2)).trans ?_
    rw [← hv]
    gcongr
    exact FillD.rpow_le_of_le_mul hv0 hu0 hR0 ha₂0 hvhi
  have b2 : ‖Gamma ((((3 - x + s.re) / 2 : ℝ) : ℂ) + (((t - y) / 2 : ℝ) : ℂ) * I)‖ ≤
      C₂ * ((1 + R) ^ b₂ * (1 + u) ^ b₂) * Real.exp (-(Real.pi * v / 2)) := by
    refine (hC₂ ((3 - x + s.re) / 2) ⟨by linarith [hx.2], by rw [hb₂]; linarith [hx.1]⟩
      ((t - y) / 2)).trans ?_
    rw [hv']
    gcongr
    exact FillD.rpow_le_of_le_mul hv0 hu0 hR0 hb₂0 hvhi
  have pe : Real.exp (-(Real.pi * v / 2)) * Real.exp (-(Real.pi * v / 2)) ≤
      Real.exp (Real.pi * R / 2) * Real.exp (-(Real.pi * u / 2)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.2
    nlinarith [Real.pi_pos]
  have hcomb : (1 + u) ^ a₂ * (1 + u) ^ b₂ = (1 + u) ^ (a₂ + b₂) :=
    (Real.rpow_add (by linarith) _ _).symm
  have hfin := hK u hu0
  rw [hnorm]
  have hp1 : 0 ≤ (1 + u) ^ a₂ := Real.rpow_nonneg (by linarith) _
  have hp2 : 0 ≤ (1 + u) ^ b₂ := Real.rpow_nonneg (by linarith) _
  have hp3 : 0 ≤ (1 + R) ^ a₂ := Real.rpow_nonneg (by linarith) _
  have hp4 : 0 ≤ (1 + R) ^ b₂ := Real.rpow_nonneg (by linarith) _
  calc 1 / 2 * (‖Gamma ((((x - s.re + 1) / 2 : ℝ) : ℂ) + (((y - t) / 2 : ℝ) : ℂ) * I)‖ *
        ‖Gamma ((((3 - x + s.re) / 2 : ℝ) : ℂ) + (((t - y) / 2 : ℝ) : ℂ) * I)‖)
      ≤ 1 / 2 * ((C₁ * ((1 + R) ^ a₂ * (1 + u) ^ a₂) * Real.exp (-(Real.pi * v / 2))) *
        (C₂ * ((1 + R) ^ b₂ * (1 + u) ^ b₂) * Real.exp (-(Real.pi * v / 2)))) := by
        gcongr
    _ = 1 / 2 * C₁ * C₂ * (1 + R) ^ a₂ * (1 + R) ^ b₂ * ((1 + u) ^ a₂ * (1 + u) ^ b₂) *
        (Real.exp (-(Real.pi * v / 2)) * Real.exp (-(Real.pi * v / 2))) := by ring
    _ ≤ 1 / 2 * C₁ * C₂ * (1 + R) ^ a₂ * (1 + R) ^ b₂ * ((1 + u) ^ a₂ * (1 + u) ^ b₂) *
        (Real.exp (Real.pi * R / 2) * Real.exp (-(Real.pi * u / 2))) := by gcongr
    _ = D * ((1 + u) ^ (a₂ + b₂) * Real.exp (-(Real.pi * u / 2))) := by rw [hD, ← hcomb]; ring
    _ ≤ D * (K / (1 + u) ^ 2) := by gcongr
    _ = D * K / (1 + |y|) ^ 2 := by rw [hu]; ring

end GoldbachBoundaries.Paper2.M4b
