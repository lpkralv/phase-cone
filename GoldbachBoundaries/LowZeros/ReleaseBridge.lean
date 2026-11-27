/- Adapted from a pilot built on the zeta project by Mercuri and Mehta
   (Apache-2.0); uses its certified evaluation. -/

import GoldbachBoundaries.LowZeros.LowZeros
import GoldbachBoundaries.PhiR.LowZerosSpec

namespace GoldbachBoundaries.PhiRProof

open Set

/-- The four certified low zeros discharge the release's low-height premise. -/
theorem releaseLowZeros_proved : ReleaseLowZeros := by
  obtain ⟨ρ, hρ, hloc, hset⟩ := Pilot.zerosThrough32
  refine ⟨ρ, hρ, ?_, ?_⟩
  · intro i
    obtain ⟨him, hre, horder⟩ := hloc i
    exact ⟨him, hre, by simp [zetaMult, horder]⟩
  · ext z
    constructor
    · rintro ⟨hz, him⟩
      rw [← hset]
      exact ⟨hz.1, him⟩
    · rintro ⟨i, rfl⟩
      have hmem : ρ i ∈ {z : ℂ | riemannZeta z = 0 ∧ z.im ∈ Ioc 0 32} := by
        rw [hset]
        exact ⟨i, rfl⟩
      refine ⟨⟨hmem.1, ?_, ?_⟩, hmem.2⟩ <;> rw [(hloc i).2.1] <;> norm_num

end GoldbachBoundaries.PhiRProof
