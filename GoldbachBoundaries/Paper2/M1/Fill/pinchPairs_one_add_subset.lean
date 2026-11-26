import GoldbachBoundaries.Paper2.M1.Residue
import GoldbachBoundaries.Paper2.M1.Fill.poleSetQ_re_le_Bsup

/-!
# Fill: `pinchPairs_one_add_subset`

A pair `(a, b) ∈ Σ_Q²` with `a + b = 1 + u` and `a, b ≠ 1` has `Re a + Re b ≤ 2B` (`poleSetQ_re_le_Bsup`), which
contradicts `2B < 1 + Re u`. So `a = 1` (then `b = u`) or `b = 1` (then `a = u`).
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M1

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **The pair condition** (Z1): if `1 + Re u > 2B`, every ordered pair with sum `1 + u` other than `(1, u)`, `(u, 1)` would
have `a, b ≠ 1`, hence `Re a + Re b ≤ 2B` (`poleSetQ_re_le_Bsup`). Uses: `poleSetQ_re_le_Bsup`.
Size: 40–80 lines. -/
theorem pinchPairs_one_add_subset (hZ1 : Z1) {u : ℂ} (hu : u ∈ PoleSetQ) (h : 2 * Bsup < 1 + u.re) :
    pinchPairs (1 + u) ⊆ {(1, u), (u, 1)} := by
  rintro ⟨a, b⟩ ⟨ha, hb, hab⟩
  simp only at ha hb hab
  simp only [mem_insert_iff, mem_singleton_iff, Prod.mk.injEq]
  by_cases ha1 : a = 1
  · left
    refine ⟨ha1, ?_⟩
    subst ha1
    linear_combination hab
  · by_cases hb1 : b = 1
    · right
      refine ⟨?_, hb1⟩
      subst hb1
      linear_combination hab
    · exfalso
      have h1 := poleSetQ_re_le_Bsup hZ1 ha ha1
      have h2 := poleSetQ_re_le_Bsup hZ1 hb hb1
      have hre : a.re + b.re = 1 + u.re := by
        have := congrArg Complex.re hab
        simpa using this
      linarith

end GoldbachBoundaries.Paper2.M1
