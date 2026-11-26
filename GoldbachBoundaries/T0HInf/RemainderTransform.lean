import GoldbachBoundaries.T0HInf.ExplicitFormula
import GoldbachBoundaries.T0HInf.Catalogue
import GoldbachBoundaries.T0HInf.RhatProof

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
namespace GoldbachBoundaries.T0HInf
open GoldbachBoundaries Paper2
open _root_.GoldbachBoundaries.Phi2HInf (StirlingStrip)

theorem meromorphicOn_Rhat (hZ1 : Z1) (hZ2 : Z2) : MeromorphicOn Rhat (halfPlane 0) := by
  exact meromorphicOn_Rhat_aux hZ1 hZ2

theorem Rhat_eq_integral (hZ1 : Z1) (hZ2 : Z2) {z : ℂ} (hz : 1 < z.re) :
    IntegrableOn (fun x : ℝ => R x * (x : ℂ) ^ (z - 1)) (Ioc (0 : ℝ) 1) ∧
      Rhat z = ∫ x in Ioc (0 : ℝ) 1, R x * (x : ℂ) ^ (z - 1) := by
  exact Rhat_eq_integral_aux hZ1 hZ2 hz

end GoldbachBoundaries.T0HInf
