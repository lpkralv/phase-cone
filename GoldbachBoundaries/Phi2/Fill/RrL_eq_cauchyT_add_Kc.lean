import GoldbachBoundaries.Phi2.Proof.M3Base
import GoldbachBoundaries.Phi2.Fill.CCommon
import GoldbachBoundaries.Phi2.Fill.integral_zeroSum_sq

noncomputable section
open Complex Filter Topology Set Metric MeasureTheory Asymptotics
namespace GoldbachBoundaries.Phi2Proof
open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **`R = cauchyT + Kc` on `σ > 1`** (RH, (Z2), (Z3)): both integrands are integrable on `(0, 1]` (`|hL|² ≤ C t^{-2b}`
for any `b ∈ (1/2, min(1, σ/2))`, `norm_hL_le`; `integral_zeroSum_sq`), so the integral splits.
Uses: `norm_hL_le`, `integral_zeroSum_sq`, `hL_explicit`, `norm_zeroSum_le`. Size 50–100. -/
theorem RrL_eq_cauchyT_add_Kc (hRH : RiemannHypothesis) (hZ2 : Z2) (hZ3 : Z3) {s : ℂ} (hs : 1 < s.re) :
    RrL s = cauchyT s + Kc s := by
  have hh := C_hsq_integrable hRH hs
  obtain ⟨hz, hzeq⟩ := integral_zeroSum_sq hRH hZ2 hs
  have hk : IntegrableOn (fun t : ℝ =>
      (((hL t ^ 2 : ℝ) : ℂ) - zeroSum t ^ 2) * (t : ℂ) ^ (s - 1)) (Ioc 0 1) := by
    exact (hh.sub hz).congr_fun (fun t _ => by dsimp; ring) measurableSet_Ioc
  calc
    RrL s = ∫ t in Ioc (0 : ℝ) 1,
        (zeroSum t ^ 2 * (t : ℂ) ^ (s - 1) +
        (((hL t ^ 2 : ℝ) : ℂ) - zeroSum t ^ 2) * (t : ℂ) ^ (s - 1)) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro t _
      ring
    _ = cauchyT s + Kc s := by rw [integral_add hz hk, hzeq]; rfl

end GoldbachBoundaries.Phi2Proof
