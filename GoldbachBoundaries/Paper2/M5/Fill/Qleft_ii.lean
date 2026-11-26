import GoldbachBoundaries.Paper2.M5.General
import GoldbachBoundaries.Paper2.M5.Fill.QCommon
import GoldbachBoundaries.Paper2.M5.Fill.norm_sigmaTail_four_le
import GoldbachBoundaries.Paper2.M5.Fill.exists_sep_height

/-! Filler group Q: `Qleft_ii` (`Qleft.lean`). `Y'` from `exists_sep_height`, `δ = 1/(1 + C log Y)`. For `w` with
`Re w ∈ [1/3, 1]`, `|Im w| = Y'` and `δ ≤ |n Im w - γ|` for all zeros and `n ≤ 3`: `w ∉ Σ_Q` (a point of `Σ_Q` is real,
a zero, or has real part `≤ 1/4`), and each `‖A(nw)‖` is `≤ ∑ Λ(m) m^{-2}` (when `Re nw ≥ 2`) or
`≤ K δ⁻¹ log(3Y' + 3)` (`norm_negLogDerivZeta_le_of_sep`, the window zeros at distance `≥ |nY' - γ| ≥ δ`). The point
`x - iY'` uses `ρ̄` (`conj_mem_nontrivialZeros`). -/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **`cl:lem:Qleft`(ii) for `Qcont`** (RH, (Z1)-(Z3)). -/
theorem Qleft_ii (hRH : RiemannHypothesis) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) :
    ∃ C : ℝ, ∀ Y : ℝ, 3 ≤ Y → ∃ Y' ∈ Icc Y (Y + 1), ∀ x ∈ Icc (1 / 3 : ℝ) 1,
      (x + Y' * I : ℂ) ∉ PoleSetQ ∧ (x - Y' * I : ℂ) ∉ PoleSetQ ∧
      ‖Qcont (x + Y' * I)‖ ≤ C * Real.log Y ^ 2 ∧ ‖Qcont (x - Y' * I)‖ ≤ C * Real.log Y ^ 2 := by
  obtain ⟨Ks, hKs0, hKs⟩ := exists_sep_bound_nonneg hZ1 hZ2 hZ3
  obtain ⟨T, hT⟩ := norm_sigmaTail_four_le
  obtain ⟨Cs, hCs0, hCs⟩ := exists_sep_height hZ1 hZ2
  set K2 := ∑' m : ℕ, ArithmeticFunction.vonMangoldt m * (m : ℝ) ^ (-(2 : ℝ)) with hK2def
  have hK2 : 0 ≤ K2 :=
    tsum_nonneg fun m => mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
  refine ⟨3 * K2 + 9 * Ks * (1 + Cs) + |T|, fun Y hY => ?_⟩
  obtain ⟨Y', hY'mem, hsep⟩ := hCs Y hY
  set L := Real.log Y with hLdef
  have hL1 : 1 ≤ L := by
    rw [hLdef, ← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  set δ := 1 / (1 + Cs * L) with hδdef
  have hden : 0 < 1 + Cs * L := by positivity
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := by
    rw [hδdef, div_le_one hden]
    nlinarith
  have hY'3 : 3 ≤ Y' := le_trans hY hY'mem.1
  -- the key estimate for a point at height `±Y'`
  have key : ∀ w : ℂ, 1 / 3 ≤ w.re → w.re ≤ 1 → |w.im| = Y' →
      (∀ n : ℕ, 1 ≤ n → n ≤ 3 → ∀ ρ ∈ NontrivialZeros, δ ≤ |(n : ℝ) * w.im - ρ.im|) →
      w ∉ PoleSetQ ∧ ‖Qcont w‖ ≤ (3 * K2 + 9 * Ks * (1 + Cs) + |T|) * L ^ 2 := by
    intro w hw1 hw2 hwim hws
    refine ⟨fun hw => ?_, ?_⟩
    · rcases poleSetQ_cases_RH hRH hw with h | h | h
      · rw [h, abs_zero] at hwim; linarith
      · have := hws 1 le_rfl (by norm_num) w h
        simp at this
        linarith
      · linarith
    have hterm : ∀ n : ℕ, 1 ≤ n → n ≤ 3 →
        ‖negLogDerivZeta ((n : ℂ) * w)‖ ≤ K2 + Ks / δ * Real.log (3 * Y' + 3) := by
      intro n hn1 hn3
      have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      have hn3' : (n : ℝ) ≤ 3 := by exact_mod_cast hn3
      have hre : ((n : ℂ) * w).re = n * w.re := by simp
      have him : ((n : ℂ) * w).im = n * w.im := by simp
      have habs : |((n : ℂ) * w).im| = n * Y' := by
        rw [him, abs_mul, hwim, Nat.abs_cast]
      have hlogpos : 0 ≤ Real.log (3 * Y' + 3) := Real.log_nonneg (by linarith)
      have hKδ : 0 ≤ Ks / δ * Real.log (3 * Y' + 3) := by positivity
      by_cases h2 : 2 ≤ (n : ℝ) * w.re
      · have := norm_negLogDerivZeta_le_of_re (x := 2) (by norm_num) (s := (n : ℂ) * w) (by rw [hre]; exact h2)
        linarith
      · push Not at h2
        have hζ : riemannZeta ((n : ℂ) * w) ≠ 0 := by
          by_cases h1 : 1 ≤ (n : ℝ) * w.re
          · exact riemannZeta_ne_zero_of_one_le_re (by rw [hre]; exact h1)
          · push Not at h1
            intro hz
            have hmem : (n : ℂ) * w ∈ NontrivialZeros := ⟨hz, by rw [hre]; nlinarith, by rw [hre]; exact h1⟩
            have := hws n hn1 hn3 _ hmem
            rw [him, sub_self, abs_zero] at this
            linarith
        have h := hKs ((n : ℂ) * w) (by rw [hre]; nlinarith) (by rw [hre]; linarith)
          (by rw [habs]; nlinarith) hζ δ hδ0 hδ1 (fun ρ hρ _ => by
            have h1 := Complex.abs_im_le_norm ((n : ℂ) * w - ρ)
            rw [Complex.sub_im, him] at h1
            exact (hws n hn1 hn3 ρ hρ).trans h1)
        rw [habs] at h
        have hmono : Real.log ((n : ℝ) * Y' + 3) ≤ Real.log (3 * Y' + 3) :=
          Real.log_le_log (by positivity) (by nlinarith)
        have : Ks / δ * Real.log ((n : ℝ) * Y' + 3) ≤ Ks / δ * Real.log (3 * Y' + 3) :=
          mul_le_mul_of_nonneg_left hmono (by positivity)
        linarith
    have h1 := hterm 1 le_rfl (by norm_num)
    have h2 := hterm 2 (by norm_num) (by norm_num)
    have h3 := hterm 3 (by norm_num) (by norm_num)
    push_cast at h1 h2 h3
    rw [one_mul] at h1
    have ht := hT w hw1
    have hQ := norm_Qcont_le_four (w := w) (by linarith)
    -- `log(3Y' + 3) ≤ 3 log Y` and `1/δ ≤ (1 + C) log Y`
    have hlogY : Real.log (3 * Y' + 3) ≤ 3 * L := by
      rw [hLdef, show (3 : ℝ) * Real.log Y = Real.log (Y ^ 3) by rw [Real.log_pow]; push_cast; ring]
      refine Real.log_le_log (by linarith) ?_
      have hY2 : 9 ≤ Y ^ 2 := by nlinarith
      have : 9 * Y ≤ Y ^ 3 := by nlinarith [mul_le_mul_of_nonneg_left hY2 (by linarith : (0 : ℝ) ≤ Y)]
      nlinarith [hY'mem.2]
    have hinvδ : 1 / δ ≤ (1 + Cs) * L := by
      rw [hδdef, one_div_one_div]
      nlinarith
    have hmain : Ks / δ * Real.log (3 * Y' + 3) ≤ 3 * Ks * (1 + Cs) * L ^ 2 := by
      have hl0 : 0 ≤ Real.log (3 * Y' + 3) := Real.log_nonneg (by linarith)
      calc Ks / δ * Real.log (3 * Y' + 3) = Ks * (1 / δ) * Real.log (3 * Y' + 3) := by ring
        _ ≤ Ks * ((1 + Cs) * L) * (3 * L) := by gcongr
        _ = 3 * Ks * (1 + Cs) * L ^ 2 := by ring
    have hL2 : 1 ≤ L ^ 2 := by nlinarith
    have hc : 0 ≤ 3 * K2 + |T| := by positivity
    have hT' := le_abs_self T
    calc ‖Qcont w‖ ≤ 3 * (K2 + Ks / δ * Real.log (3 * Y' + 3)) + |T| := by linarith
      _ ≤ 3 * K2 + |T| + 9 * Ks * (1 + Cs) * L ^ 2 := by linarith
      _ ≤ (3 * K2 + |T|) * L ^ 2 + 9 * Ks * (1 + Cs) * L ^ 2 := by nlinarith
      _ = _ := by ring
  refine ⟨Y', hY'mem, fun x hx => ?_⟩
  have hp := key ((x : ℂ) + Y' * I) (by simpa using hx.1) (by simpa using hx.2)
    (by rw [show ((x : ℂ) + Y' * I).im = Y' by simp]; exact abs_of_nonneg (by linarith))
    (fun n hn1 hn3 ρ hρ => by simpa using hsep n hn1 hn3 ρ hρ)
  have hm := key ((x : ℂ) - Y' * I) (by simpa using hx.1) (by simpa using hx.2)
    (by rw [show ((x : ℂ) - Y' * I).im = -Y' by simp, abs_neg]; exact abs_of_nonneg (by linarith))
    (fun n hn1 hn3 ρ hρ => by
      have h := hsep n hn1 hn3 (conj ρ) (conj_mem_nontrivialZeros hρ)
      have e : ((x : ℂ) - Y' * I).im = -Y' := by simp
      rw [e]
      rw [Complex.conj_im] at h
      calc 1 / (1 + Cs * L) ≤ |(n : ℝ) * Y' - -ρ.im| := h
        _ = |(n : ℝ) * -Y' - ρ.im| := by
            rw [← abs_neg]; congr 1; ring)
  exact ⟨hp.1, hm.1, hp.2, hm.2⟩

end GoldbachBoundaries.Paper2.M5
