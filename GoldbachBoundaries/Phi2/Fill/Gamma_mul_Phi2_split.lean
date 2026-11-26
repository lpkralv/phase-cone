import GoldbachBoundaries.Phi2.Fill.ACommon

/-! Filler A: `Gamma_mul_Phi2_split` (M1). Proof in `Phi2/Fill/ACommon.lean` (`FillA.Gamma_mul_Phi2_split'`, a port of `TIdentity.Gamma_mul_T_eq_split`). -/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics

namespace GoldbachBoundaries.Phi2Proof

open GoldbachBoundaries

/-- **Split of `ΓΦ₂` at `t = 1`** (no RH): `Γ(s)Φ₂(s) = 1/(s-2) + 2m₁(s-1) + R(s) + E₂(s)` for `Re s > 2`.
Uses: `TIdentity.Gamma_mul_T_eq_split` (G9f), `mellin_FL_sq`. Size 80–150. -/
theorem Gamma_mul_Phi2_split {s : ℂ} (hs : 2 < s.re) :
    Gamma s * Phi2 s = 1 / (s - 2) + 2 * m1L (s - 1) + RrL s + E2L s :=
  FillA.Gamma_mul_Phi2_split' hs

end GoldbachBoundaries.Phi2Proof
