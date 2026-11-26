import GoldbachBoundaries.T0HInf.ZeroCoefficients

/-! Weighted instances of the already proved Mellin–Fubini theorem. -/
noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
namespace GoldbachBoundaries.T0HInf
open GoldbachBoundaries Paper2
open _root_.GoldbachBoundaries.Phi2Proof (C_countable_zeros)
open _root_.GoldbachBoundaries.Phi2HInf (integral_cpow_family summable_norm_cpow_family)

lemma integral_U (hZ1 : Z1) (hZ2 : Z2)
    {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => U x * (x : ℂ) ^ (s - 1)) (Ioc 0 1) ∧
      (∫ x in Ioc (0 : ℝ) 1, U x * (x : ℂ) ^ (s - 1)) = singleC s := by
  letI := C_countable_zeros
  exact integral_cpow_family (fun ρ : NontrivialZeros => zeroCoef ρ) (fun ρ => ρ)
    (summable_norm_zeroCoef hZ1 hZ2) (fun ρ => ρ.2.2.2.le) hs

lemma integral_U_sq (hZ1 : Z1) (hZ2 : Z2)
    {s : ℂ} (hs : 2 < s.re) :
    IntegrableOn (fun x : ℝ => U x ^ 2 * (x : ℂ) ^ (s - 1)) (Ioc 0 1) ∧
      (∫ x in Ioc (0 : ℝ) 1, U x ^ 2 * (x : ℂ) ^ (s - 1)) = C s := by
  letI := C_countable_zeros
  have ha := summable_norm_zeroCoef hZ1 hZ2
  let a (p : NontrivialZeros × NontrivialZeros) := zeroCoef p.1 * zeroCoef p.2
  let p (q : NontrivialZeros × NontrivialZeros) : ℂ := q.1 + q.2
  have hp (q : NontrivialZeros × NontrivialZeros) : (p q).re ≤ 2 := by
    dsimp [p]
    linarith [q.1.2.2.2, q.2.2.2.2]
  have h := integral_cpow_family a p
    (Summable.mul_norm (f := fun ρ : NontrivialZeros => zeroCoef ρ) (g := fun ρ : NontrivialZeros => zeroCoef ρ) ha ha) hp hs
  have heq (x : ℝ) (hx : x ∈ Ioc (0 : ℝ) 1) : U x ^ 2 = ∑' q, a q * (x : ℂ) ^ (-p q) := by
    have hz := summable_norm_cpow_family (fun ρ : NontrivialZeros => zeroCoef ρ) (fun ρ => (ρ : ℂ))
      ha (fun ρ => ρ.2.2.2.le) hx
    rw [pow_two, U, tsum_mul_tsum_of_summable_norm hz hz]
    apply tsum_congr
    intro q
    dsimp [a, p]
    rw [neg_add, cpow_add _ _ (ofReal_ne_zero.mpr hx.1.ne')]
    ring
  refine ⟨h.1.congr_fun (fun x hx => by rw [heq x hx]) measurableSet_Ioc, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioc (fun x hx => by rw [heq x hx]), h.2]
  apply tsum_congr
  intro q
  simp only [a, p, sub_add_eq_sub_sub]

end GoldbachBoundaries.T0HInf
