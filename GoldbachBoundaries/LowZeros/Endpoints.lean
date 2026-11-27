/- Adapted from a pilot built on the zeta project by Mercuri and Mehta
   (Apache-2.0); uses its certified evaluation. -/

module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace Pilot

def start : Fin 4 → ℕ :=
  ![14134725141734693790457251983562, 21022039638771554992628479593896,
    25010857580145688763213790992562, 30424876125859513210311897530584]

noncomputable def lo (i : Fin 4) : ℝ := (start i : ℝ) / ↑(10 ^ 30 : ℕ)
noncomputable def hi (i : Fin 4) : ℝ := (↑(start i + 1) : ℝ) / ↑(10 ^ 30 : ℕ)

end Pilot
