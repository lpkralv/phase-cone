import GoldbachBoundaries.Phi2.Fill.ACommon

/-! Filler A: `mellin_FL` (M1). Proof in `Phi2/Fill/ACommon.lean` (`FillA.mellin_FL_aux`, a port of `TIdentity.mellin_Fw`). -/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics

namespace GoldbachBoundaries.Phi2Proof

open GoldbachBoundaries

/-- **Mellin transform of `FL`** (no RH): `∫_0^∞ FL(t) t^{z-1} dt = Γ(z) ψ(z)` for `Re z > 1`, with the integrand
integrable. Uses: `TIdentity.mellin_Fw` (G9b), `ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div`.
Size 80–150. -/
theorem mellin_FL {z : ℂ} (hz : 1 < z.re) :
    IntegrableOn (fun t : ℝ => (FL t : ℂ) * (t : ℂ) ^ (z - 1)) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), (FL t : ℂ) * (t : ℂ) ^ (z - 1) = Gamma z * negLogDerivZeta z :=
  FillA.mellin_FL_aux hz

end GoldbachBoundaries.Phi2Proof
