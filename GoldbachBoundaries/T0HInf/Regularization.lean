import GoldbachBoundaries.T0HInf.ErrorContinuation
import GoldbachBoundaries.T0HInf.RegularizationIdentity

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
namespace GoldbachBoundaries.T0HInf
open GoldbachBoundaries Paper2
open _root_.GoldbachBoundaries.Phi2HInf (StirlingStrip)

theorem meromorphicOn_W (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3)
    (hStir : StirlingStrip) {E : Finset NontrivialZeros} (hE : IsCutoff E) :
    MeromorphicOn (W E) (halfPlane crossingAbscissa) := by
  exact meromorphicOn_W_aux hH hZ1 hZ2 hZ3 hStir hE

theorem t0_reg_identity (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3)
    (hStir : StirlingStrip) {E : Finset NontrivialZeros} (hE : IsCutoff E) :
    EqOn (T0c E) T0 (halfPlane 2) := by
  exact t0_reg_identity_aux hZ1 hZ2 E

theorem t0_hinf_continuation (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3)
    (hStir : StirlingStrip) {E : Finset NontrivialZeros} (hE : IsCutoff E) :
    MeromorphicOn (T0c E) HH ∧ EqOn (T0c E) T0 (halfPlane 2) := by
  refine ⟨?_, t0_reg_identity hH hZ1 hZ2 hZ3 hStir hE⟩
  intro s hs
  have hcross : s ∈ halfPlane crossingAbscissa := by
    have hb := (cutoff_bounds hH).2.2.2.2
    change crossingAbscissa < s.re
    change 1 < s.re at hs
    linarith
  have hm := ((meromorphicOn_C hH hZ1 hZ2 s hs).add
    (meromorphicOn_W hH hZ1 hZ2 hZ3 hStir hE s hcross)).mul
      (differentiable_one_div_Gamma.analyticAt s).meromorphicAt
  convert hm using 1
  ext z
  simp only [T0c, Pi.add_apply, Pi.mul_apply, div_eq_mul_inv, one_div]

end GoldbachBoundaries.T0HInf
