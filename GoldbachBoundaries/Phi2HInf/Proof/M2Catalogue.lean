import GoldbachBoundaries.Phi2HInf.Fill.meromorphicOn_M0
import GoldbachBoundaries.Paper2.Statements
import GoldbachBoundaries.Phi2HInf.Fill.hasResidue_C
import GoldbachBoundaries.Phi2HInf.Fill.analyticOn_M0_strip

/-! Route B §4.3. Local finiteness is strictly inside `HH`, never on its boundary. -/
noncomputable section
open Complex Filter Topology Set Metric
namespace GoldbachBoundaries.Phi2HInf
open GoldbachBoundaries Paper2 Phi2Proof

theorem hasResidue_Phi2cHInf (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3)
    (hStir : StirlingStrip) {s : ℂ} (hs : 1 < s.re) (hsB : s.re < 1 + (1 - Bsup)) :
    HasResidue Phi2cHInf s (collisionAtom s / Gamma s) := by
  have hM := analyticOn_M0_strip hH hZ1 hZ2 hStir s ⟨hs, hsB⟩
  have hA := (differentiableOn_A hZ1 hZ2 hZ3 hStir).analyticOnNhd
    (isOpen_halfPlane _) s (show s ∈ halfPlane (1 / 2) by change 1 / 2 < s.re; linarith)
  have hC := (hasResidue_C hH hZ1 hZ2 hStir hs).add_analyticAt hA
  have hΓ : ContinuousAt (fun z : ℂ => 1 / Gamma z) s :=
    by simpa only [one_div] using differentiable_one_div_Gamma.continuous.continuousAt (x := s)
  have hres := (hasResidue_zero_of_analyticAt hM).add' (hC.mul_continuousAt' hΓ)
  change HasResidue (fun z => M0 z + (C z + A z) / Gamma z) s (collisionAtom s / Gamma s)
  simpa only [div_eq_mul_inv, one_mul, zero_add] using hres


end GoldbachBoundaries.Phi2HInf
