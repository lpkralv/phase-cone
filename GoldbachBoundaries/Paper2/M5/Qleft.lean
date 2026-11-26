import GoldbachBoundaries.Paper2.M5.General
import GoldbachBoundaries.Paper2.M5.Fill.norm_negLogDerivZeta_le_of_sep
import GoldbachBoundaries.Paper2.M5.Fill.norm_sigmaTail_four_le
import GoldbachBoundaries.Paper2.M5.Fill.exists_sep_height
import GoldbachBoundaries.Paper2.M5.Fill.Qleft_i
import GoldbachBoundaries.Paper2.M5.Fill.Qleft_ii
import GoldbachBoundaries.Paper2.M5.Fill.Qleft_iii

/-!
# M5: `cl:lem:Qleft`, the growth of `Q` at and left of the critical line (RH, (Z1)-(Z3))

The paper's proof, made explicit. For `Re w ≥ 1/3`, paper 1's `Qcont w = ∑_n μ(n) A(nw)` (`A = -ζ'/ζ`) splits as
`A(w) - A(2w) - A(3w) + sigmaTail 4 w` (`Qcont_eq_sum_add_tail 4`; the term `n = 0` is `0`), and the tail is bounded
(`norm_sigmaTail_four_le`). Each of the first three terms is bounded by (Z3) once every zero `ρ'` with
`|γ' - Im(nw)| ≤ 1` is at distance `≥ δ` from `nw`: `|A(nw)| ≤ C δ⁻¹ log(|Im(nw)| + 3)`
(`norm_negLogDerivZeta_le_of_sep`, (Z3) plus M1's window count `sum_zetaMult_window_le`), or by the Dirichlet series
when `Re(nw) > 1` (M1's `norm_negLogDerivZeta_le_of_re`).

* (i) `Re w = x₀ ∈ (1/3, 1/2)`: the distances are `≥ 1/2 - x₀`, `≥ 2x₀ - 1/2`, and `Re(3w) > 1`.
* (ii) `Re w ∈ [1/3, 1]`, `Im w = ±Y'`: the distances are `≥ |nY' - γ'| ≥ δ(Y) = 1/(1 + C log Y)` for a height `Y'` that
  the measure argument provides (`exists_sep_height`), so `|Q| ≤ C δ⁻¹ log Y ≤ C' log² Y`.
* (iii) `Re w = 1/2 + η`: `η/|w - ρ'| ≤ η/Re(w - ρ') = 1` under RH (and the two compact rectangles near the real axis).

The target `lem_Qleft_proof` is assembled at the end; the bounds are stated for `Qcont` and transferred to any `Qc`
with `IsQCont` by M1's `isQCont_eventuallyEq` (the points are off `Σ_Q`).
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-! ## Lemmas

Proved in `Fill/`, one file per lemma (same name, same statement): `norm_negLogDerivZeta_le_of_sep`, `norm_sigmaTail_four_le`, `exists_sep_height`, `Qleft_i`, `Qleft_ii`, `Qleft_iii`. -/

/-! ## Target -/

/-- `lem_Qleft` of `Paper2/Statements.lean`, statement verbatim. -/
theorem lem_Qleft_proof (hRH : RiemannHypothesis) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) :
    (∀ x₀ : ℝ, 1 / 3 < x₀ → x₀ < 1 / 2 → ∃ C : ℝ, ∀ Qc : ℂ → ℂ, IsQCont Qc → ∀ y : ℝ,
      (x₀ + y * I : ℂ) ∉ PoleSetQ ∧ ‖Qc (x₀ + y * I)‖ ≤ C * Real.log (|y| + 3)) ∧
    (∃ C : ℝ, ∀ Y : ℝ, 3 ≤ Y → ∃ Y' ∈ Icc Y (Y + 1), ∀ Qc : ℂ → ℂ, IsQCont Qc →
      ∀ x ∈ Icc (1 / 3 : ℝ) 1,
        (x + Y' * I : ℂ) ∉ PoleSetQ ∧ (x - Y' * I : ℂ) ∉ PoleSetQ ∧
        ‖Qc (x + Y' * I)‖ ≤ C * Real.log Y ^ 2 ∧ ‖Qc (x - Y' * I)‖ ≤ C * Real.log Y ^ 2) ∧
    ∃ C : ℝ, ∀ Qc : ℂ → ℂ, IsQCont Qc → ∀ w : ℂ, 1 / 2 < w.re → w.re ≤ 3 / 4 →
      w ∉ PoleSetQ ∧ (w.re - 1 / 2) * ‖Qc w‖ ≤ C * Real.log (|w.im| + 3) := by
  obtain ⟨C₂, h2⟩ := Qleft_ii hRH hZ1 hZ2 hZ3
  obtain ⟨C₃, h3⟩ := Qleft_iii hRH hZ1 hZ2 hZ3
  refine ⟨fun x₀ hx₀ hx₀' => ?_, ⟨C₂, fun Y hY => ?_⟩, ⟨C₃, fun Qc hQc w hw hw' => ?_⟩⟩
  · obtain ⟨C, hC⟩ := Qleft_i hRH hZ1 hZ2 hZ3 x₀ hx₀ hx₀'
    refine ⟨C, fun Qc hQc y => ?_⟩
    obtain ⟨hn, hb⟩ := hC y
    have hpos : (x₀ + y * I : ℂ) ∈ halfPlane 0 := by
      show 0 < ((x₀ : ℂ) + y * I).re
      simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one, sub_zero, add_zero]
      linarith
    rw [(isQCont_eventuallyEq hQc).1 _ ⟨hpos, hn⟩]
    exact ⟨hn, hb⟩
  · obtain ⟨Y', hY', hb⟩ := h2 Y hY
    refine ⟨Y', hY', fun Qc hQc x hx => ?_⟩
    obtain ⟨hn1, hn2, hb1, hb2⟩ := hb x hx
    have hx0 : 0 < x := by linarith [hx.1]
    have hp1 : (x + Y' * I : ℂ) ∈ halfPlane 0 := by
      show 0 < ((x : ℂ) + Y' * I).re
      simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one, sub_zero, add_zero]
      exact hx0
    have hp2 : (x - Y' * I : ℂ) ∈ halfPlane 0 := by
      show 0 < ((x : ℂ) - Y' * I).re
      simp only [sub_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one, sub_zero]
      exact hx0
    rw [(isQCont_eventuallyEq hQc).1 _ ⟨hp1, hn1⟩, (isQCont_eventuallyEq hQc).1 _ ⟨hp2, hn2⟩]
    exact ⟨hn1, hn2, hb1, hb2⟩
  · obtain ⟨hn, hb⟩ := h3 w hw hw'
    have hpos : w ∈ halfPlane 0 := by
      show 0 < w.re
      linarith
    rw [(isQCont_eventuallyEq hQc).1 _ ⟨hpos, hn⟩]
    exact ⟨hn, hb⟩

end GoldbachBoundaries.Paper2.M5
