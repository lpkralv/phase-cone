import GoldbachBoundaries.T0HInf.Cutoff
import GoldbachBoundaries.T0HInf.PrimeMellin
import GoldbachBoundaries.T0HInf.ZeroCoefficients
import GoldbachBoundaries.T0HInf.RemainderBoundProof

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
namespace GoldbachBoundaries.T0HInf
open GoldbachBoundaries Paper2
open _root_.GoldbachBoundaries.Phi2HInf (StirlingStrip)

theorem L_explicit (x : ℝ) :
    L x = U x + primeSquareCoef * (x : ℂ) ^ (-(1 / 2 : ℂ)) + R x := by
  unfold R
  ring

theorem remainder_bound (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3)
    (hStir : StirlingStrip) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ Ioc (0 : ℝ) 1, ‖R x‖ ≤ K * x ^ (-remainderAbscissa) := by
  exact remainder_bound_aux hH hZ1 hZ2 hZ3 hStir

end GoldbachBoundaries.T0HInf
