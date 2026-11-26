import GoldbachBoundaries.Phi2.Proof.M1Continuation
import GoldbachBoundaries.Paper2.M5.Fill.noMeromorphicExtensionAt_of_line_blowup
import GoldbachBoundaries.Paper2.M5.Fill.exists_ordinate_in_interval
import GoldbachBoundaries.Density
import GoldbachBoundaries.Phi2.Fill.zetaMult_conj
import GoldbachBoundaries.Phi2.Fill.summable_norm_zeroCoef
import GoldbachBoundaries.Phi2.Fill.negLogDerivZeta_two_fifths
import GoldbachBoundaries.Phi2.Fill.negLogDerivZeta_good_height
import GoldbachBoundaries.Phi2.Fill.rect_kernelL
import GoldbachBoundaries.Phi2.Fill.«verticalIntegral'_kernelL_zero_shift»
import GoldbachBoundaries.Phi2.Fill.«norm_verticalIntegral'_kernelL_two_fifths_le»

/-!
**Change against Sol's (5).** Sol shifts the inverse Mellin line to `Re w = -1/2`, crossing `w = 0` (residue
`-log 2π`) and getting `R(t) = O(t^{1/2})`. We stop at `Re w = 2/5`: the remainder `O(t^{-2/5})` already makes the
leftover of `hL²` an `O(t^{-9/10})`, integrable against `t^{σ-1}` for `σ > 9/10`, which is all the radial limit needs.
This avoids `ψ` on `Re w ≤ 1/3`, the pole of `Γ` at `0`, and the constant `-log 2π` (which belongs to `phi2Main`'s
pole at `s = 1` and plays no part at `τ ≠ 0`). The line `2/5` and the window `1/3 ≤ Re w ≤ 1` are those of paper 2's
Theorem F (`M5.Jfil`, `M5.Qleft_ii`), so the good heights and bounds of M5 apply nearly verbatim.

(Z1) is not a premise: under RH it is proved (`Z1_of_RH`, real proof from `zetaMult_conj`).
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics ComplexConjugate

namespace GoldbachBoundaries.Phi2Proof

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-! ## Lemmas proved in `Fill/`

One file per lemma, same name and statement, proved at the end of its file and imported above: `zetaMult_conj`, `summable_norm_zeroCoef`, `negLogDerivZeta_two_fifths`, `negLogDerivZeta_good_height`, `rect_kernelL`, `verticalIntegral'_kernelL_zero_shift`, `norm_verticalIntegral'_kernelL_two_fifths_le`. -/

/-! ## (Z1) from RH -/

/-- **(Z1) holds under RH** (real proof): `ρ̄` is a zero of the same multiplicity, and `1 - ρ̄ = ρ` on the critical
line. -/
theorem Z1_of_RH (hRH : RiemannHypothesis) : Z1 := by
  intro ρ hρ
  have hc : conj ρ ∈ NontrivialZeros := conj_mem_nontrivialZeros hρ
  have hre : ρ.re = 1 / 2 := sigmaFinite_re_eq_half hRH hρ
  have h1 : 1 - conj ρ = ρ := by
    apply Complex.ext
    · simp [hre]; norm_num
    · simp
  refine ⟨⟨hc, zetaMult_conj hρ⟩, ?_, ?_⟩
  · rw [h1]; exact hρ
  · rw [h1]

/-! ## Bounds on the zeros and on `ψ` -/

/-! ## The second contour shift, across the zeros -/

/-- **The explicit formula** (RH, (Z2), (Z3); real proof): `hL(t) = -∑_ρ a_ρ t^{-ρ} + R(t)`, `|R(t)| ≤ C t^{-2/5}`,
for all `t > 0`. -/
theorem hL_explicit (hRH : RiemannHypothesis) (hZ2 : Z2) (hZ3 : Z3) :
    ∃ C : ℝ, ∀ t : ℝ, 0 < t → ‖(hL t : ℂ) + zeroSum t‖ ≤ C * t ^ (-(2 / 5 : ℝ)) := by
  obtain ⟨C, hC⟩ := norm_verticalIntegral'_kernelL_two_fifths_le hRH hZ2 hZ3
  refine ⟨C, fun t ht => ?_⟩
  have h1 := FL_eq_verticalIntegral' (c := 2) (by norm_num) ht
  have h2 := verticalIntegral'_kernelL_shift hRH (b := 3 / 4) (c := 2) (by norm_num) (by norm_num)
    (by norm_num) ht
  have h3 := verticalIntegral'_kernelL_zero_shift hRH hZ2 hZ3 ht
  have heq : (hL t : ℂ) + zeroSum t = VerticalIntegral' (kernelL t) (2 / 5) := by
    simp only [hL]
    push_cast
    rw [h1, h2, h3]
    ring
  rw [heq]
  exact hC t ht

end GoldbachBoundaries.Phi2Proof
