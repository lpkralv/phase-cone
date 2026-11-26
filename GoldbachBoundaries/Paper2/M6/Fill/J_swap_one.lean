import GoldbachBoundaries.Paper2.M6.Defs

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M6

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **`J_{b1} = J_{1b}`** (every `b`, `s`). Substitute `τ ↦ 1 - τ` (`intervalIntegral.integral_comp_sub_left`):
`b + (1 - τ)(s - b - 1) = s - (1 + τ(s - b - 1))`, and `K_s(s - w) = K_s(w)` (M1's `KerS_sub_symm`). -/
theorem J_swap_one (b s : ℂ) : ThmA.J b 1 s = ThmA.J 1 b s := by
  simp only [ThmA.J, ThmA.segInt]
  have h1 : s - 1 - b = s - b - 1 := by ring
  rw [h1]
  congr 1
  have := intervalIntegral.integral_comp_sub_left
    (fun τ : ℝ => ThmA.Kern s (b + (τ : ℂ) * (s - b - 1))) (a := 0) (b := 1) (1 : ℝ)
  simp only [sub_zero, sub_self] at this
  rw [← this]
  congr 1
  funext τ
  have : b + ((1 - τ : ℝ) : ℂ) * (s - b - 1) = s - (1 + (τ : ℂ) * (s - b - 1)) := by
    push_cast; ring
  rw [this]
  exact M1.KerS_sub_symm s _

end GoldbachBoundaries.Paper2.M6
