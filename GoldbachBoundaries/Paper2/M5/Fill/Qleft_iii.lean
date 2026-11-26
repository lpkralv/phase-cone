import GoldbachBoundaries.Paper2.M5.General
import GoldbachBoundaries.Paper2.M5.Fill.QCommon
import GoldbachBoundaries.Paper2.M5.Fill.poleSetQ_re_cases
import GoldbachBoundaries.Paper2.M5.Fill.norm_sigmaTail_four_le
import GoldbachBoundaries.Paper2.M5.Fill.norm_negLogDerivZeta_le_of_sep

/-! Filler group Q: `Qleft_iii` (`Qleft.lean`). `η = Re w - 1/2`, `Q(w) = A(w) - A(2w) - A(3w) + tail`.
`η‖A(w)‖`: for `|v| ≥ 2`, `norm_negLogDerivZeta_le_of_sep` with `δ = η` (under RH `‖w - ρ‖ ≥ Re(w - ρ) = η`); for
`|v| < 2`, the compact rectangle `[1/2, 3/4] × [-2, 2]` (`exists_bound_weighted_negLogDeriv` at `a = 1/2`).
`η‖A(2w)‖`: for `|v| ≥ 1`, the same lemma at `2w` with `δ = 1/2`; for `|v| < 1`, the rectangle `[1, 3/2] × [-2, 2]`
at `a = 1`. `A(3w)` and the tail are bounded. -/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **`cl:lem:Qleft`(iii) for `Qcont`** (RH, (Z1)-(Z3)). -/
theorem Qleft_iii (hRH : RiemannHypothesis) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) :
    ∃ C : ℝ, ∀ w : ℂ, 1 / 2 < w.re → w.re ≤ 3 / 4 →
      w ∉ PoleSetQ ∧ (w.re - 1 / 2) * ‖Qcont w‖ ≤ C * Real.log (|w.im| + 3) := by
  obtain ⟨Ks, hKs⟩ := norm_negLogDerivZeta_le_of_sep hZ1 hZ2 hZ3
  obtain ⟨T, hT⟩ := norm_sigmaTail_four_le
  set K3 := ∑' m : ℕ, ArithmeticFunction.vonMangoldt m * (m : ℝ) ^ (-(3 / 2 : ℝ)) with hK3def
  have hK3 : 0 ≤ K3 :=
    tsum_nonneg fun m => mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
  have hRHre : ∀ ρ ∈ NontrivialZeros, ρ.re = 1 / 2 := fun ρ hρ => sigmaFinite_re_eq_half hRH hρ
  obtain ⟨B1, hB1⟩ := exists_bound_weighted_negLogDeriv (1 / 2)
    (K := (Icc (1 / 2 : ℝ) (3 / 4)) ×ℂ (Icc (-2 : ℝ) 2)) (isCompact_Icc.reProdIm isCompact_Icc)
    (fun x hx => by
      rw [Complex.mem_reProdIm] at hx
      rcases eq_or_lt_of_le hx.1.1 with h | h
      · exact Or.inl h.symm
      · refine Or.inr ⟨fun h1 => ?_, fun hz => ?_⟩
        · rw [h1] at hx
          norm_num at hx
        · have := hRHre x ⟨hz, by linarith, by linarith [hx.1.2]⟩
          linarith)
  obtain ⟨B2, hB2⟩ := exists_bound_weighted_negLogDeriv 1
    (K := (Icc (1 : ℝ) (3 / 2)) ×ℂ (Icc (-2 : ℝ) 2)) (isCompact_Icc.reProdIm isCompact_Icc)
    (fun x hx => by
      rw [Complex.mem_reProdIm] at hx
      rcases eq_or_lt_of_le hx.1.1 with h | h
      · exact Or.inl h.symm
      · refine Or.inr ⟨fun h1 => ?_, riemannZeta_ne_zero_of_one_lt_re h⟩
        rw [h1] at h
        norm_num at h)
  set Ks0 := max Ks 0 with hKs0def
  have hKs0 : 0 ≤ Ks0 := le_max_right _ _
  -- the separation lemma with a non-negative constant
  have hsepK : ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 → 2 ≤ |z.im| → riemannZeta z ≠ 0 → ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      (∀ ρ ∈ NontrivialZeros, |ρ.im - z.im| ≤ 1 → δ ≤ ‖z - ρ‖) →
        ‖negLogDerivZeta z‖ ≤ Ks0 / δ * Real.log (|z.im| + 3) := by
    intro z h1 h2 h3 h4 δ hδ hδ1 hsep
    refine (hKs z h1 h2 h3 h4 δ hδ hδ1 hsep).trans ?_
    have : 0 ≤ Real.log (|z.im| + 3) := Real.log_nonneg (by linarith [abs_nonneg z.im])
    gcongr
    exact le_max_left _ _
  refine ⟨2 * Ks0 + |B1| + |B2| + K3 + |T|, fun w hw1 hw2 => ?_⟩
  have hη0 : 0 < w.re - 1 / 2 := by linarith
  have hlog1 : 1 ≤ Real.log (|w.im| + 3) := one_le_log_add_three (abs_nonneg _)
  have hlog0 : 0 ≤ Real.log (|w.im| + 3) := by linarith
  refine ⟨fun hw => ?_, ?_⟩
  · rcases poleSetQ_re_cases hRH hw with h | ⟨h, -⟩ | h
    · rw [h] at hw2
      norm_num at hw2
    · linarith
    · linarith
  -- `η ‖A(w)‖`
  have ha1 : (w.re - 1 / 2) * ‖negLogDerivZeta w‖ ≤ (Ks0 + |B1|) * Real.log (|w.im| + 3) := by
    by_cases hv : 2 ≤ |w.im|
    · have hζ : riemannZeta w ≠ 0 := fun hz => by
        have := hRHre w ⟨hz, by linarith, by linarith⟩
        linarith
      have h := hsepK w (by linarith) (by linarith) hv hζ (w.re - 1 / 2) hη0 (by linarith)
        (fun ρ hρ _ => by
          have h1 := Complex.re_le_norm (w - ρ)
          rw [Complex.sub_re, hRHre ρ hρ] at h1
          exact h1)
      calc (w.re - 1 / 2) * ‖negLogDerivZeta w‖
          ≤ (w.re - 1 / 2) * (Ks0 / (w.re - 1 / 2) * Real.log (|w.im| + 3)) :=
            mul_le_mul_of_nonneg_left h hη0.le
        _ = Ks0 * Real.log (|w.im| + 3) := by
            have hne : w.re - 1 / 2 ≠ 0 := hη0.ne'
            rw [← mul_assoc, mul_comm (w.re - 1 / 2), div_mul_cancel₀ Ks0 hne]
        _ ≤ _ := by
            have := abs_nonneg B1
            nlinarith
    · push Not at hv
      have hmem : w ∈ (Icc (1 / 2 : ℝ) (3 / 4)) ×ℂ (Icc (-2 : ℝ) 2) := by
        rw [Complex.mem_reProdIm]
        exact ⟨⟨hw1.le, hw2⟩, abs_le.mp hv.le⟩
      have h := hB1 w hmem hw1
      calc (w.re - 1 / 2) * ‖negLogDerivZeta w‖ ≤ B1 := h
        _ ≤ |B1| := le_abs_self _
        _ ≤ |B1| * Real.log (|w.im| + 3) := le_mul_of_one_le_right (abs_nonneg _) hlog1
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hlog0
  -- `η ‖A(2w)‖`
  have h2re : (2 * w).re = 2 * w.re := by simp
  have h2im : (2 * w).im = 2 * w.im := by simp
  have ha2 : (w.re - 1 / 2) * ‖negLogDerivZeta (2 * w)‖ ≤ (Ks0 + |B2|) * Real.log (|w.im| + 3) := by
    by_cases hv : 1 ≤ |w.im|
    · have hζ : riemannZeta (2 * w) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by rw [h2re]; linarith)
      have him : |(2 * w).im| = 2 * |w.im| := by rw [h2im, abs_mul]; norm_num
      have h := hsepK (2 * w) (by rw [h2re]; linarith) (by rw [h2re]; linarith) (by rw [him]; linarith) hζ
        (1 / 2) (by norm_num) (by norm_num)
        (fun ρ hρ _ => by
          have h1 := Complex.re_le_norm (2 * w - ρ)
          rw [Complex.sub_re, hRHre ρ hρ, h2re] at h1
          linarith)
      rw [him] at h
      have hl := log_mul_add_three_le (abs_nonneg w.im) (by norm_num : (0 : ℝ) ≤ 2) (by norm_num)
      have h' : ‖negLogDerivZeta (2 * w)‖ ≤ 4 * Ks0 * Real.log (|w.im| + 3) := by
        calc ‖negLogDerivZeta (2 * w)‖ ≤ Ks0 / (1 / 2) * Real.log (2 * |w.im| + 3) := h
          _ ≤ Ks0 / (1 / 2) * (2 * Real.log (|w.im| + 3)) := by gcongr
          _ = _ := by ring
      have hn := norm_nonneg (negLogDerivZeta (2 * w))
      have := abs_nonneg B2
      nlinarith
    · push Not at hv
      have hmem : 2 * w ∈ (Icc (1 : ℝ) (3 / 2)) ×ℂ (Icc (-2 : ℝ) 2) := by
        rw [Complex.mem_reProdIm, h2re, h2im]
        obtain ⟨hv1, hv2⟩ := abs_le.mp hv.le
        exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
      have h := hB2 (2 * w) hmem (by rw [h2re]; linarith)
      rw [h2re] at h
      have e : (w.re - 1 / 2) * ‖negLogDerivZeta (2 * w)‖ =
          (2 * w.re - 1) * ‖negLogDerivZeta (2 * w)‖ / 2 := by ring
      rw [e]
      calc (2 * w.re - 1) * ‖negLogDerivZeta (2 * w)‖ / 2 ≤ B2 / 2 := by linarith
        _ ≤ |B2| := by linarith [le_abs_self B2, abs_nonneg B2]
        _ ≤ |B2| * Real.log (|w.im| + 3) := le_mul_of_one_le_right (abs_nonneg _) hlog1
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hlog0
  -- `A(3w)` and the tail
  have ha3 : ‖negLogDerivZeta (3 * w)‖ ≤ K3 :=
    norm_negLogDerivZeta_le_of_re (by norm_num) (by simp; linarith)
  have ht : ‖sigmaTail 4 w‖ ≤ T := hT w (by linarith)
  have hQ := norm_Qcont_le_four (w := w) (by linarith)
  have hT0 : T ≤ |T| := le_abs_self T
  have hrest : (w.re - 1 / 2) * (‖negLogDerivZeta (3 * w)‖ + ‖sigmaTail 4 w‖) ≤
      (K3 + |T|) * Real.log (|w.im| + 3) := by
    have h1 : ‖negLogDerivZeta (3 * w)‖ + ‖sigmaTail 4 w‖ ≤ K3 + |T| := by linarith
    have h2 : 0 ≤ ‖negLogDerivZeta (3 * w)‖ + ‖sigmaTail 4 w‖ := by positivity
    calc (w.re - 1 / 2) * (‖negLogDerivZeta (3 * w)‖ + ‖sigmaTail 4 w‖) ≤ 1 * (K3 + |T|) :=
          mul_le_mul (by linarith) h1 h2 zero_le_one
      _ ≤ (K3 + |T|) * Real.log (|w.im| + 3) := by
          rw [one_mul]
          have : 0 ≤ K3 + |T| := by positivity
          nlinarith
  calc (w.re - 1 / 2) * ‖Qcont w‖
      ≤ (w.re - 1 / 2) * (‖negLogDerivZeta w‖ + ‖negLogDerivZeta (2 * w)‖ + ‖negLogDerivZeta (3 * w)‖ +
          ‖sigmaTail 4 w‖) := mul_le_mul_of_nonneg_left hQ hη0.le
    _ = (w.re - 1 / 2) * ‖negLogDerivZeta w‖ + (w.re - 1 / 2) * ‖negLogDerivZeta (2 * w)‖ +
          (w.re - 1 / 2) * (‖negLogDerivZeta (3 * w)‖ + ‖sigmaTail 4 w‖) := by ring
    _ ≤ (Ks0 + |B1|) * Real.log (|w.im| + 3) + (Ks0 + |B2|) * Real.log (|w.im| + 3) +
          (K3 + |T|) * Real.log (|w.im| + 3) := by linarith
    _ = _ := by ring

end GoldbachBoundaries.Paper2.M5
