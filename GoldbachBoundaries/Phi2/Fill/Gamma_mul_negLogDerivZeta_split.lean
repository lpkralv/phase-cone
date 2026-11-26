import GoldbachBoundaries.Phi2.Fill.ACommon

/-! Filler A: `Gamma_mul_negLogDerivZeta_split` (M1). Proof in `Phi2/Fill/ACommon.lean` (`FillA.Gamma_mul_negLogDerivZeta_split'`, a port of `TIdentity.Gamma_mul_Q_eq_split`). -/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics

namespace GoldbachBoundaries.Phi2Proof

open GoldbachBoundaries

/-- **Split of `Γψ` at `t = 1`** (no RH): `Γ(z)ψ(z) = 1/(z-1) + m₁(z) + e₁(z)` for `Re z > 1`.
Uses: `TIdentity.Gamma_mul_Q_eq_split` (G9e), `mellin_FL`. Size 60–120. -/
theorem Gamma_mul_negLogDerivZeta_split {z : ℂ} (hz : 1 < z.re) :
    Gamma z * negLogDerivZeta z = 1 / (z - 1) + m1L z + e1L z :=
  FillA.Gamma_mul_negLogDerivZeta_split' hz

end GoldbachBoundaries.Phi2Proof
