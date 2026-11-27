import GoldbachBoundaries.LowZeros.ReleaseBridge
import GoldbachBoundaries.PhiR.D0Tail

open Filter Topology

namespace GoldbachBoundaries.PhiRProof

open GoldbachBoundaries.Paper2

/-- The unsubtracted real-point limit is nonzero and changes sign between consecutive arities. -/
theorem phiR_tendsto_ne_zero (hRH : RiemannHypothesis) (hZ2 : Z2) (hZ3 : Z3)
    {r : ℕ} (hr : 2 ≤ r) :
    ∃ L : ℝ, L ≠ 0 ∧ (r ≤ 5639249912025015212 → L < 0) ∧
      (5639249912025015213 ≤ r → 0 < L) ∧
      Tendsto (fun η : ℝ => (η : ℂ) * PhiRc r ((r : ℂ) - 1 + η)) (𝓝[>] 0) (𝓝 (L : ℂ)) := by
  simpa only [gapN] using phiR_tendsto_ne_zero_RH hRH hZ2 hZ3 releaseLowZeros_proved hr

end GoldbachBoundaries.PhiRProof
