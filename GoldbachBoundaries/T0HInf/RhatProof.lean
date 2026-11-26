import GoldbachBoundaries.T0HInf.PrimeMellin
import GoldbachBoundaries.T0HInf.ZeroMellin
import GoldbachBoundaries.T0HInf.Catalogue

/-! The finite-interval remainder has a meromorphic transform on Re z > 0. -/
noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
namespace GoldbachBoundaries.T0HInf
open GoldbachBoundaries Paper2

lemma meromorphicOn_Rhat_aux (hZ1 : Z1) (hZ2 : Z2) : MeromorphicOn Rhat (halfPlane 0) := by
  intro z hz
  have hΓ : MeromorphicAt Gamma z := PhiRProof.meromorphicAt_Gamma z
  have hQ := meromorphicAt_Qcont hz
  have hE := differentiable_EL.analyticAt z |>.meromorphicAt
  have hC := meromorphicOn_singleC hZ1 hZ2 z (mem_univ _)
  have hp := (analyticAt_const (v := primeSquareCoef) (x := z)).meromorphicAt.div
    ((analyticAt_id.sub analyticAt_const).meromorphicAt : MeromorphicAt (fun z : ℂ => z - 1 / 2) z)
  have hlin : MeromorphicAt (fun w : ℂ => 1 - w) z :=
    ((analyticAt_const (v := (1 : ℂ)) (x := z)).sub analyticAt_id).meromorphicAt
  have h := ((((hlin.mul hΓ).mul hQ).sub hE).sub hC).sub hp
  convert h using 1
  ext w
  rfl

lemma integral_primeSquare {z : ℂ} (hz : 1 / 2 < z.re) :
    IntegrableOn (fun x : ℝ => primeSquareCoef * (x : ℂ) ^ (-(1 / 2 : ℂ)) * (x : ℂ) ^ (z - 1)) (Ioc 0 1) ∧
      (∫ x in Ioc (0 : ℝ) 1, primeSquareCoef * (x : ℂ) ^ (-(1 / 2 : ℂ)) * (x : ℂ) ^ (z - 1)) =
        primeSquareCoef / (z - 1 / 2) := by
  have h := Phi2HInf.integral_cpow_family (ι := Unit) (fun _ => primeSquareCoef)
    (fun _ => (1 / 2 : ℂ)) (r := 1 / 2) (by exact summable_of_finite_support (Set.toFinite _))
    (fun _ => by norm_num) hz
  simpa using h

lemma Rhat_eq_integral_aux (hZ1 : Z1) (hZ2 : Z2) {z : ℂ} (hz : 1 < z.re) :
    IntegrableOn (fun x : ℝ => R x * (x : ℂ) ^ (z - 1)) (Ioc (0 : ℝ) 1) ∧
      Rhat z = ∫ x in Ioc (0 : ℝ) 1, R x * (x : ℂ) ^ (z - 1) := by
  obtain ⟨hML, hL⟩ := L_mellin hz
  have hi : IntegrableOn (fun x : ℝ => L x * (x : ℂ) ^ (z - 1)) (Ioi 0) := by
    simpa only [MellinConvergent, smul_eq_mul, mul_comm] using hML
  have hIoc : IntegrableOn (fun x : ℝ => L x * (x : ℂ) ^ (z - 1)) (Ioc 0 1) :=
    hi.mono_set Ioc_subset_Ioi_self
  have hIoi := hi.mono_set (Ioi_subset_Ioi (show (0 : ℝ) ≤ 1 by norm_num))
  have hsplit : (1 - z) * Gamma z * Qcont z =
      (∫ x in Ioc (0 : ℝ) 1, L x * (x : ℂ) ^ (z - 1)) + EL z := by
    rw [← hL, mellin]
    simp only [smul_eq_mul]
    rw [show (fun x : ℝ => (x : ℂ) ^ (z - 1) * L x) =
      (fun x : ℝ => L x * (x : ℂ) ^ (z - 1)) by funext x; ring]
    rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num),
      setIntegral_union (by simp [Set.disjoint_left]) measurableSet_Ioi hIoc hIoi]
    rfl
  obtain ⟨hU, hUint⟩ := integral_U hZ1 hZ2 hz
  obtain ⟨hP, hPint⟩ := integral_primeSquare (z := z) (by linarith)
  have hR : (fun x : ℝ => R x * (x : ℂ) ^ (z - 1)) =
      fun x => (L x * (x : ℂ) ^ (z - 1) - U x * (x : ℂ) ^ (z - 1)) -
        primeSquareCoef * (x : ℂ) ^ (-(1 / 2 : ℂ)) * (x : ℂ) ^ (z - 1) := by
    funext x
    unfold R
    ring
  refine ⟨by rw [hR]; exact (hIoc.sub hU).sub hP, ?_⟩
  rw [hR]
  rw [integral_sub (f := fun x => L x * (x : ℂ) ^ (z - 1) - U x * (x : ℂ) ^ (z - 1)) (hIoc.sub hU) hP,
    integral_sub hIoc hU, hUint, hPint, Rhat, hsplit]
  ring

end GoldbachBoundaries.T0HInf
