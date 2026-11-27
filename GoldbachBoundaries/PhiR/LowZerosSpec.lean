import GoldbachBoundaries.Defs
import Mathlib.Data.Fin.VecNotation

namespace GoldbachBoundaries.PhiRProof

open Set GoldbachBoundaries

def start : Fin 4 → ℕ :=
  ![14134725141734693790457251983562, 21022039638771554992628479593896,
    25010857580145688763213790992562, 30424876125859513210311897530584]

noncomputable def lo (i : Fin 4) : ℝ := (start i : ℝ) / ↑(10 ^ 30 : ℕ)
noncomputable def hi (i : Fin 4) : ℝ := (↑(start i + 1) : ℝ) / ↑(10 ^ 30 : ℕ)

/-- The low-zero input for step 3, using only the release's definitions and rational endpoints. -/
def ReleaseLowZeros : Prop :=
  ∃ ρ : Fin 4 → ℂ, Function.Injective ρ ∧
    (∀ i, (ρ i).im ∈ Ioo (lo i) (hi i) ∧ (ρ i).re = 1 / 2 ∧ zetaMult (ρ i) = 1) ∧
    {z : ℂ | z ∈ NontrivialZeros ∧ z.im ∈ Ioc 0 32} = Set.range ρ

end GoldbachBoundaries.PhiRProof
