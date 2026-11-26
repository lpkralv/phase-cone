import GoldbachBoundaries.Phi2.Fill.ACommon

/-! Filler A: `mellin_FL_sq` (M1). Proof in `Phi2/Fill/ACommon.lean` (`FillA.mellin_FL_sq'`, a port of `TIdentity.mellin_Fw_sq`). -/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics

namespace GoldbachBoundaries.Phi2Proof

open GoldbachBoundaries

/-- **Mellin transform of `FL²`** (no RH): for `Re s > 2` the double series `Φ₂(s)` converges absolutely and
`∫_0^∞ FL(t)² t^{s-1} dt = Γ(s) Φ₂(s)`. Uses: `TIdentity.mellin_Fw_sq` (G9c). Size 120–220. -/
theorem mellin_FL_sq {s : ℂ} (hs : 2 < s.re) :
    Summable (fun mn : ℕ × ℕ => ‖((ArithmeticFunction.vonMangoldt mn.1 : ℝ) : ℂ) *
      ((ArithmeticFunction.vonMangoldt mn.2 : ℝ) : ℂ) * (((mn.1 + mn.2 : ℕ) : ℂ)) ^ (-s)‖) ∧
      ∫ t in Ioi (0 : ℝ), ((FL t ^ 2 : ℝ) : ℂ) * (t : ℂ) ^ (s - 1) = Gamma s * Phi2 s := by
  obtain ⟨hsum, -, hval⟩ := FillA.mellin_FL_sq' hs
  refine ⟨hsum, ?_⟩
  rw [← hval, mellin]
  simp only [smul_eq_mul, mul_comm]

end GoldbachBoundaries.Phi2Proof
