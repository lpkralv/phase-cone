import GoldbachBoundaries.Paper2.M3.Landau
import GoldbachBoundaries.Paper2.M3.Fill.Gamma_mul_Qcont_eq_of_mem
import GoldbachBoundaries.Paper2.M3.Fill.Rcoef_eq_zero_of_mem_mellinConvSet
import GoldbachBoundaries.Paper2.M3.Fill.exists_differentiableOn_balls
import GoldbachBoundaries.Paper2.M3.Fill.integrableOn_hErr_mul_cpow_of_mem
import GoldbachBoundaries.Paper2.M3.Fill.laplaceConvSet_phiH
import GoldbachBoundaries.Paper2.M3.Fill.laplace_phiH_eq_Mcal
import GoldbachBoundaries.Paper2.M3.Fill.measurable_phiH
import GoldbachBoundaries.Paper2.M3.Fill.mem_mellinConvSet_of_differentiableOn_balls

/-!
# M3: the abscissa of `𝓜` (Steps 2-4 of `nr:thm:test`, `nr:rem:classical`(ii))

Two results, used by `Test.lean` and `Classical.lean`.

**A lower end for `𝓜` from a holomorphic continuation** (`mem_mellinConvSet_of_differentiableOn_balls`, Step 2 of
`nr:thm:test`). With `t = e^{-u}`, `𝓜(s) = 𝓛(s)` for `φ = phiH` (`laplace_phiH_eq_Mcal`), and the convergence set of
`𝓛` is `mellinConvSet` (`laplaceConvSet_phiH`). If `𝓜` agrees on `σ > 2` with a function holomorphic on discs centred
at the points of a real segment `(a, 2]`, then every `x > a` is in `mellinConvSet`: otherwise `σ_c ∈ (a, 2]`, and
Landau (`lem_Landau_proof`) is contradicted at the disc centred at `σ_c`.

**A zero bound from a point of convergence** (`re_le_of_mem_mellinConvSet`, Steps 3-4 with `σ_c` replaced by any
`x ∈ mellinConvSet`, which is how `nr:rem:classical`(ii) reads them): if `x ∈ mellinConvSet` then
`N(z) = ∫_0^1 h(t)t^{z-1} dt` converges for `Re z > x/2` (Cauchy-Schwarz), `Γ(z)Q(z) = e(z) + 1/(z-1) + N(z)` there,
so `Q` has no pole `a ≠ 1` with `Re a > x/2`; a zero with `β ≥ 1/2` is such a pole (`R_ρ = -m(ρ) ≠ 0`,
`Rcoef_of_half_le_re`), so it has `β ≤ x/2`.

The general lemma `exists_differentiableOn_balls` (removable singularities on discs centred at real points) feeds the
first result in both `Test.lean` and `Classical.lean`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M3

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-! ## Real lemmas -/

/-- Step 4 with `x` in place of `1`: a point of convergence `x` of `𝓜` bounds every zero with `β ≥ 1/2` by `x/2`. -/
theorem re_le_of_mem_mellinConvSet {x : ℝ} (hx : x ∈ mellinConvSet) {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros)
    (hre : 1 / 2 ≤ ρ.re) : ρ.re ≤ x / 2 := by
  by_contra h
  push Not at h
  have hP : ρ ∈ PoleSetQ := Or.inr ⟨1, le_rfl, squarefree_one, ρ, hρ, by simp⟩
  have h0 := Rcoef_eq_zero_of_mem_mellinConvSet hx hP h (ne_one_of_mem_nontrivialZeros hρ)
  rw [Rcoef_of_half_le_re hρ hre] at h0
  have hm : (1 : ℕ) ≤ zetaMult ρ := one_le_zetaMult hρ
  have : (zetaMult ρ : ℂ) = 0 := neg_eq_zero.mp h0
  have : zetaMult ρ = 0 := by exact_mod_cast this
  omega

end GoldbachBoundaries.Paper2.M3
