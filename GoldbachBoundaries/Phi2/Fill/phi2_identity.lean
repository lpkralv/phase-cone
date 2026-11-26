import GoldbachBoundaries.Phi2.Fill.ACommon

/-! Filler A: `phi2_identity` (M1). Proof in `Phi2/Fill/ACommon.lean` (`FillA.phi2_identity'`, the algebra of `thm_T_identity_proof`). -/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics

namespace GoldbachBoundaries.Phi2Proof

open GoldbachBoundaries

/-- **The `Φ₂` identity** (no RH): `Φ₂ = phi2Main + Hphi2` on `σ > 2`. The algebra of `thm_T_identity_proof`.
Uses: `Gamma_mul_negLogDerivZeta_split` at `s - 1`, `Gamma_mul_Phi2_split`, `Gamma_add_one`. Size 40–80. -/
theorem phi2_identity {s : ℂ} (hs : 2 < s.re) : Phi2 s = phi2Main s + Hphi2 s :=
  FillA.phi2_identity' hs

end GoldbachBoundaries.Phi2Proof
