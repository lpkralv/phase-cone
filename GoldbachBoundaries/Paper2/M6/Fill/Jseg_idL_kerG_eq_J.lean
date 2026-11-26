import GoldbachBoundaries.Paper2.M6.Defs

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M6

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **`Jseg` for `L(s) = s`, `k = K_s(z)` is paper 1's `J`.** Both are the parametrised segment integral of the
same kernel (`KerS = Kern` by definition, `idL.app s = s`), and `s - a - b = s - b - a`. -/
theorem Jseg_idL_kerG_eq_J (a b s : ℂ) : Jseg Aff.idL kerG a b s = ThmA.J a b s := by
  simp only [Jseg, ThmA.J, ThmA.segInt, M4a.app_idL, kerG, KerS, ThmA.Kern]
  have h : s - a - b = s - b - a := by ring
  rw [h]

end GoldbachBoundaries.Paper2.M6
