import GoldbachBoundaries.Paper2.M2.LW
import GoldbachBoundaries.Paper2.M2.Fill.far_tail
import GoldbachBoundaries.Paper2.M2.Fill.far_tail_numeric
import GoldbachBoundaries.Paper2.M2.Fill.ncard_far_shell_le
import GoldbachBoundaries.Paper2.M2.Fill.norm_far_term_le
import GoldbachBoundaries.Paper2.M2.Fill.pinchPairs_other_mem
import GoldbachBoundaries.Paper2.M2.Fill.summable_pinchPairs_one_add
import GoldbachBoundaries.Paper2.M2.Fill.summable_tsum_le_of_shells

/-!
# M2: far pairs (`nr:lem:far`)

`B < 1`, `s₀ = 1 + v`, `0 < Re v ≤ 1`, `|Im v| ≤ Y`. A pair `(a, b) ≠ (1, v), (v, 1)` with `a + b = s₀` has
`a, b ≠ 1` and `1 - B < Re a, Re b ≤ B` (M1's `poleSetQ_re_le_Bsup`). Its term is at most
`C₃(1 + |t|)⁴ e^{-π|t|}`, `t = Im a`, for `|t| ≥ 2Y` (`nr:lem:Q`(iii) for `R_a`, `R_b`; (Z6) on `[1 - B, B]` for
`Γ(a)`, `Γ(b)`; `1/Γ` bounded on the compact set `{1 ≤ Re ≤ 2, |Im| ≤ Y}`), and at most `C log(j + 4)` pairs have
`j ≤ |Im a| < j + 1` (`nr:lem:Q`(iii) on two unit windows; the pair is determined by `a`). Summing shells
`j ≥ ⌊H⌋` gives a tail `≤ e^{-H}` for `H ≥ H₀`.

**Integrated layout.** The seven lemmas this file stated with `sorry` (`pinchPairs_other_mem`, `norm_far_term_le`,
`ncard_far_shell_le`, `summable_tsum_le_of_shells`, `far_tail_numeric`, `far_tail`, `summable_pinchPairs_one_add`) are
proved in `Fill/<name>.lean`, statements unchanged, each with its sketch as docstring; the fill files import `LW.lean`
(and each other where needed), and this file imports them.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M2

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-! ## Target: `lem_far` -/

/-- `lem_far` of `Paper2/Statements.lean`, statement verbatim. -/
theorem lem_far_proof (hZ1 : Z1) (hZ2 : Z2) (hZ6 : Z6) (hB : Bsup < 1) {Y : ℝ} (hY : 0 < Y) :
    (∀ v : ℂ, 0 < v.re → v.re ≤ 1 → |v.im| ≤ Y → ∀ p ∈ pinchPairs (1 + v), p ≠ (1, v) → p ≠ (v, 1) →
      p.1 ∈ PoleSetQ \ {1} ∧ p.2 ∈ PoleSetQ \ {1} ∧
        p.1.re ∈ Ioc (1 - Bsup) Bsup ∧ p.2.re ∈ Ioc (1 - Bsup) Bsup) ∧
    ∃ H₀ : ℝ, 2 * Y + 2 ≤ H₀ ∧ ∀ H : ℝ, H₀ ≤ H → ∀ v : ℂ, 0 < v.re → v.re ≤ 1 → |v.im| ≤ Y →
      Summable (fun p : {p : ℂ × ℂ // p ∈ pinchPairs (1 + v) ∧ p ≠ (1, v) ∧ p ≠ (v, 1) ∧ H < |p.1.im|} =>
        ‖Rcoef p.1.1 * Rcoef p.1.2 * betaB p.1.1 p.1.2‖) ∧
      ∑' p : {p : ℂ × ℂ // p ∈ pinchPairs (1 + v) ∧ p ≠ (1, v) ∧ p ≠ (v, 1) ∧ H < |p.1.im|},
        ‖Rcoef p.1.1 * Rcoef p.1.2 * betaB p.1.1 p.1.2‖ ≤ Real.exp (-H) :=
  ⟨fun _ hv _ _ _ hp h1 h2 => pinchPairs_other_mem hZ1 hv hp h1 h2, far_tail hZ1 hZ2 hZ6 hB hY⟩

/-! ## Target: `lem_far_abs` -/

/-- `lem_far_abs` of `Paper2/Statements.lean`, statement verbatim. -/
theorem lem_far_abs_proof (hZ1 : Z1) (hZ2 : Z2) (hZ6 : Z6) (hB : Bsup < 1) :
    ∀ v : ℂ, 0 < v.re → v.re ≤ 1 →
      Summable fun p : pinchPairs (1 + v) => ‖Rcoef p.1.1 * Rcoef p.1.2 * betaB p.1.1 p.1.2‖ :=
  summable_pinchPairs_one_add hZ1 hZ2 hZ6 hB

end GoldbachBoundaries.Paper2.M2
