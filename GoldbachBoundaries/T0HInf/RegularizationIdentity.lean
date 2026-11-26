import GoldbachBoundaries.T0HInf.RemainderTransform

/-! Exact Mellin regularization, including the finite exceptional-zero cross terms. -/
noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
namespace GoldbachBoundaries.T0HInf
open GoldbachBoundaries Paper2

lemma integral_UP (hZ1 : Z1) (hZ2 : Z2) {s : ℂ} (hs : 2 < s.re) :
    IntegrableOn (fun x : ℝ => 2 * primeSquareCoef * U x * (x : ℂ) ^ (-(1 / 2 : ℂ)) *
      (x : ℂ) ^ (s - 1)) (Ioc 0 1) ∧
    (∫ x in Ioc (0 : ℝ) 1, 2 * primeSquareCoef * U x * (x : ℂ) ^ (-(1 / 2 : ℂ)) *
      (x : ℂ) ^ (s - 1)) = 2 * primeSquareCoef * singleC (s - 1 / 2) := by
  have hz : 1 < (s - 1 / 2).re := by simp; linarith
  have hu := integral_U hZ1 hZ2 hz
  have heq (x : ℝ) (hx : x ∈ Ioc (0 : ℝ) 1) :
      2 * primeSquareCoef * U x * (x : ℂ) ^ (-(1 / 2 : ℂ)) * (x : ℂ) ^ (s - 1) =
        (2 * primeSquareCoef) * (U x * (x : ℂ) ^ ((s - 1 / 2) - 1)) := by
    rw [show (s - 1 / 2) - 1 = -(1 / 2 : ℂ) + (s - 1) by ring,
      cpow_add _ _ (ofReal_ne_zero.mpr hx.1.ne')]
    ring
  have hi : IntegrableOn (fun x : ℝ => (2 * primeSquareCoef) * (U x * (x : ℂ) ^ ((s - 1 / 2) - 1))) (Ioc 0 1) := hu.1.const_mul _
  refine ⟨hi.congr_fun (fun x hx => (heq x hx).symm) measurableSet_Ioc, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioc heq, integral_const_mul, hu.2]

lemma integral_ER (hZ1 : Z1) (hZ2 : Z2) (E : Finset NontrivialZeros)
    {s : ℂ} (hs : 2 < s.re) :
    IntegrableOn (fun x : ℝ => 2 * exceptionalU E x * R x * (x : ℂ) ^ (s - 1)) (Ioc 0 1) ∧
    (∫ x in Ioc (0 : ℝ) 1, 2 * exceptionalU E x * R x * (x : ℂ) ^ (s - 1)) =
      2 * (∑ ρ ∈ E, zeroCoef ρ * Rhat (s - ρ)) := by
  have hr (ρ : NontrivialZeros) := Rhat_eq_integral hZ1 hZ2 (z := s - ρ) (by
    rw [sub_re]; linarith [ρ.2.2.2])
  have heq (x : ℝ) (hx : x ∈ Ioc (0 : ℝ) 1) :
      2 * exceptionalU E x * R x * (x : ℂ) ^ (s - 1) =
        2 * ∑ ρ ∈ E, zeroCoef ρ * (R x * (x : ℂ) ^ ((s - ρ) - 1)) := by
    simp_rw [show ∀ ρ : NontrivialZeros, (s - ρ) - 1 = -(ρ : ℂ) + (s - 1) by intro ρ; ring,
      cpow_add _ _ (ofReal_ne_zero.mpr hx.1.ne')]
    simp only [exceptionalU, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro ρ hρ
    ring
  have hi : IntegrableOn (fun x : ℝ => 2 * ∑ ρ ∈ E, zeroCoef ρ * (R x * (x : ℂ) ^ ((s - ρ) - 1))) (Ioc 0 1) := (integrable_finsetSum E (fun ρ _ => (hr ρ).1.const_mul (zeroCoef ρ))).const_mul (2 : ℂ)
  refine ⟨hi.congr_fun (fun x hx => (heq x hx).symm) measurableSet_Ioc, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioc heq, integral_const_mul,
    integral_finsetSum E (fun ρ _ => (hr ρ).1.const_mul _)]
  congr 1
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [integral_const_mul, ← (hr ρ).2]

lemma integral_PP {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => primeSquareCoef ^ 2 * (x : ℂ) ^ (-(1 : ℂ)) *
      (x : ℂ) ^ (s - 1)) (Ioc 0 1) ∧
    (∫ x in Ioc (0 : ℝ) 1, primeSquareCoef ^ 2 * (x : ℂ) ^ (-(1 : ℂ)) *
      (x : ℂ) ^ (s - 1)) = primeSquareCoef ^ 2 / (s - 1) := by
  have h := Phi2HInf.integral_cpow_family (ι := Unit) (fun _ => primeSquareCoef ^ 2)
    (fun _ => (1 : ℂ)) (r := 1) (by exact summable_of_hasFiniteSupport (Set.toFinite _))
    (fun _ => by norm_num) hs
  simpa using h

lemma square_expansion (E : Finset NontrivialZeros) {x : ℝ} (hx : 0 < x) :
    L x ^ 2 = U x ^ 2 + primeSquareCoef ^ 2 * (x : ℂ) ^ (-(1 : ℂ)) +
      2 * primeSquareCoef * U x * (x : ℂ) ^ (-(1 / 2 : ℂ)) +
      2 * exceptionalU E x * R x + regularError E x := by
  have hp : (x : ℂ) ^ (-(1 : ℂ)) = ((x : ℂ) ^ (-(1 / 2 : ℂ))) ^ 2 := by
    rw [pow_two, ← cpow_add _ _ (ofReal_ne_zero.mpr hx.ne')]
    congr 1
    ring
  rw [hp]
  dsimp [regularError, residualU, R]
  ring

lemma t0_reg_identity_aux (hZ1 : Z1) (hZ2 : Z2) (E : Finset NontrivialZeros) :
    EqOn (T0c E) T0 (halfPlane 2) := by
  intro s hs
  obtain ⟨hi, hv⟩ := t0_mellin_sq hs
  have hio : IntegrableOn (fun x : ℝ => L x ^ 2 * (x : ℂ) ^ (s - 1)) (Ioi 0) := by
    simpa only [MellinConvergent, smul_eq_mul, mul_comm] using hi
  have hi0 : IntegrableOn (fun x : ℝ => L x ^ 2 * (x : ℂ) ^ (s - 1)) (Ioc 0 1) :=
    hio.mono_set Ioc_subset_Ioi_self
  have hi1 := hio.mono_set (Ioi_subset_Ioi (show (0 : ℝ) ≤ 1 by norm_num))
  have hsplit : Gamma s * T0 s =
      (∫ x in Ioc (0 : ℝ) 1, L x ^ 2 * (x : ℂ) ^ (s - 1)) + E2 s := by
    rw [← hv, mellin]
    simp only [smul_eq_mul]
    rw [show (fun x : ℝ => (x : ℂ) ^ (s - 1) * L x ^ 2) =
      (fun x : ℝ => L x ^ 2 * (x : ℂ) ^ (s - 1)) by funext x; ring,
      ← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num),
      setIntegral_union (by simp [Set.disjoint_left]) measurableSet_Ioi hi0 hi1]
    rfl
  obtain ⟨h0, hv0⟩ := integral_U_sq hZ1 hZ2 hs
  obtain ⟨h1, hv1⟩ := integral_PP (s := s) (by have : 2 < s.re := hs; linarith)
  obtain ⟨h2, hv2⟩ := integral_UP hZ1 hZ2 hs
  obtain ⟨h3, hv3⟩ := integral_ER hZ1 hZ2 E hs
  unfold IntegrableOn at h0 h1 h2 h3
  let f (x : ℝ) : ℂ := U x ^ 2 * (x : ℂ) ^ (s - 1) +
    primeSquareCoef ^ 2 * (x : ℂ) ^ (-(1 : ℂ)) * (x : ℂ) ^ (s - 1) +
    2 * primeSquareCoef * U x * (x : ℂ) ^ (-(1 / 2 : ℂ)) * (x : ℂ) ^ (s - 1) +
    2 * exceptionalU E x * R x * (x : ℂ) ^ (s - 1)
  have hf : IntegrableOn f (Ioc 0 1) := ((h0.add h1).add h2).add h3
  have herr (x : ℝ) (hx : x ∈ Ioc (0 : ℝ) 1) :
      regularError E x * (x : ℂ) ^ (s - 1) = L x ^ 2 * (x : ℂ) ^ (s - 1) - f x := by
    rw [square_expansion E hx.1]
    dsimp [f]
    ring
  have he : H E s = (∫ x in Ioc (0 : ℝ) 1, L x ^ 2 * (x : ℂ) ^ (s - 1)) -
      (C s + primeSquareCoef ^ 2 / (s - 1) + 2 * primeSquareCoef * singleC (s - 1 / 2) +
        2 * (∑ ρ ∈ E, zeroCoef ρ * Rhat (s - ρ))) := by
    rw [H, setIntegral_congr_fun measurableSet_Ioc herr, integral_sub hi0 hf]
    dsimp [f]
    have e1 := integral_add h0 h1
    have e2 := integral_add (h0.add h1) h2
    have e3 := integral_add ((h0.add h1).add h2) h3
    simp only [Pi.add_apply] at e1 e2 e3
    rw [e3, e2, e1, hv0, hv1, hv2, hv3]
  have hnum : C s + W E s = Gamma s * T0 s := by rw [W, he, hsplit]; ring
  rw [T0c, hnum, mul_div_cancel_left₀ _ (Gamma_ne_zero_of_re_pos (by have : 2 < s.re := hs; linarith))]

end GoldbachBoundaries.T0HInf
