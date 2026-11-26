import GoldbachBoundaries.T0HInf.ExplicitFormula

/-! Cutoff bounds for the part of the error whose Mellin transform crosses Re s = 1. -/
noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
namespace GoldbachBoundaries.T0HInf
open GoldbachBoundaries Paper2
open _root_.GoldbachBoundaries.Phi2HInf (StirlingStrip summable_norm_cpow_family)

lemma norm_residualU_le (hZ1 : Z1) (hZ2 : Z2)
    {E : Finset NontrivialZeros} (hE : IsCutoff E) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ Ioc (0 : ℝ) 1, ‖residualU E x‖ ≤ K * x ^ (-cutoffAbscissa) := by
  classical
  have ha := summable_norm_zeroCoef hZ1 hZ2
  let S : ℝ := ∑' ρ : {ρ : NontrivialZeros // ρ ∉ E}, ‖zeroCoef ρ.1‖
  refine ⟨S, tsum_nonneg (fun _ => norm_nonneg _), ?_⟩
  intro x hx
  have hrem := summable_norm_cpow_family
    (fun ρ : {ρ : NontrivialZeros // ρ ∉ E} => zeroCoef ρ.1) (fun ρ => (ρ.1 : ℂ))
    (r := cutoffAbscissa) (ha.subtype (fun ρ : NontrivialZeros => ρ ∉ E))
    (fun ρ => le_of_not_gt (fun h => ρ.2 ((hE ρ.1).2 h))) hx
  have hsum := (summable_norm_cpow_family (fun ρ : NontrivialZeros => zeroCoef ρ)
    (fun ρ => (ρ : ℂ)) (r := 1) ha (fun ρ => ρ.2.2.2.le) hx).of_norm.sum_add_tsum_subtype_compl E
  have heq : residualU E x = ∑' ρ : {ρ : NontrivialZeros // ρ ∉ E},
      zeroCoef ρ.1 * (x : ℂ) ^ (-(ρ.1 : ℂ)) := by
    unfold residualU U exceptionalU
    rw [← hsum]
    ring
  rw [heq]
  calc
    _ ≤ ∑' ρ : {ρ : NontrivialZeros // ρ ∉ E},
        ‖zeroCoef ρ.1 * (x : ℂ) ^ (-(ρ.1 : ℂ))‖ := norm_tsum_le_tsum_norm hrem
    _ ≤ ∑' ρ : {ρ : NontrivialZeros // ρ ∉ E}, ‖zeroCoef ρ.1‖ * x ^ (-cutoffAbscissa) := by
      apply hrem.tsum_le_tsum _ ((ha.subtype (fun ρ : NontrivialZeros => ρ ∉ E)).mul_right _)
      intro ρ
      rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx.1, neg_re]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hx.1 hx.2
        (neg_le_neg (le_of_not_gt (fun h => ρ.2 ((hE ρ.1).2 h))))) (norm_nonneg _)
    _ = _ := tsum_mul_right

lemma regularError_meas (E : Finset NontrivialZeros) :
    AEStronglyMeasurable (regularError E) (volume.restrict (Ioc (0 : ℝ) 1)) := by
  have hL : AEStronglyMeasurable L (volume.restrict (Ioc (0 : ℝ) 1)) := (L_basic.1.mono (show Ioc (0 : ℝ) 1 ⊆ Ioi 0 from Ioc_subset_Ioi_self)).aestronglyMeasurable measurableSet_Ioc
  have hU : AEStronglyMeasurable U (volume.restrict (Ioc (0 : ℝ) 1)) := by
    letI := Phi2Proof.C_countable_zeros
    unfold U
    exact AEStronglyMeasurable.tsum (fun ρ => (Phi2Proof.C_cpow_meas (-(ρ : ℂ))).const_mul _)
  have hE : AEStronglyMeasurable (exceptionalU E) (volume.restrict (Ioc (0 : ℝ) 1)) :=
    E.aestronglyMeasurable_fun_sum (fun ρ _ => (Phi2Proof.C_cpow_meas (-(ρ : ℂ))).const_mul _)
  have hp : AEStronglyMeasurable (fun x : ℝ => primeSquareCoef * (x : ℂ) ^ (-(1 / 2 : ℂ))) (volume.restrict (Ioc (0 : ℝ) 1)) := (Phi2Proof.C_cpow_meas (-(1 / 2 : ℂ))).const_mul primeSquareCoef
  have hR : AEStronglyMeasurable R (volume.restrict (Ioc (0 : ℝ) 1)) := (hL.sub hU).sub hp
  convert! (((hU.sub hE).const_mul 2).mul hR |>.add ((hp.const_mul 2).mul hR)).add (hR.pow 2) using 1
  ext x
  dsimp [regularError, residualU]
  ring

lemma norm_regularError_le (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3)
    (hStir : StirlingStrip) {E : Finset NontrivialZeros} (hE : IsCutoff E) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ Ioc (0 : ℝ) 1,
      ‖regularError E x‖ ≤ K * x ^ (-(remainderAbscissa + cutoffAbscissa)) := by
  obtain ⟨Ku, hKu, hu⟩ := norm_residualU_le hZ1 hZ2 hE
  obtain ⟨Kr, hKr, hr⟩ := remainder_bound hH hZ1 hZ2 hZ3 hStir
  refine ⟨2 * Ku * Kr + 2 * ‖primeSquareCoef‖ * Kr + Kr ^ 2, by positivity, ?_⟩
  intro x hx
  have hx0 : 0 ≤ x := hx.1.le
  have ha := (cutoff_bounds hH).2.2.1
  have hb := (cutoff_bounds hH).2.2.2.1
  have hba : remainderAbscissa ≤ cutoffAbscissa := by linarith
  have hp1 : x ^ (-cutoffAbscissa) * x ^ (-remainderAbscissa) =
      x ^ (-(remainderAbscissa + cutoffAbscissa)) := by
    rw [← Real.rpow_add hx.1]
    congr 1
    ring
  have hp2 : x ^ (-(1 / 2 : ℝ)) * x ^ (-remainderAbscissa) ≤
      x ^ (-(remainderAbscissa + cutoffAbscissa)) := by
    rw [← Real.rpow_add hx.1]
    exact Real.rpow_le_rpow_of_exponent_ge hx.1 hx.2 (by linarith)
  have hp3 : (x ^ (-remainderAbscissa)) ^ 2 ≤
      x ^ (-(remainderAbscissa + cutoffAbscissa)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.1.le]
    exact Real.rpow_le_rpow_of_exponent_ge hx.1 hx.2 (by norm_num; linarith)
  have h1 : ‖2 * residualU E x * R x‖ ≤ 2 * Ku * Kr * x ^ (-(remainderAbscissa + cutoffAbscissa)) := by
    rw [norm_mul, norm_mul, Complex.norm_ofNat]
    calc
      _ ≤ 2 * (Ku * x ^ (-cutoffAbscissa)) * (Kr * x ^ (-remainderAbscissa)) := by
        gcongr
        · exact hu x hx
        · exact hr x hx
      _ = _ := by rw [show 2 * (Ku * x ^ (-cutoffAbscissa)) * (Kr * x ^ (-remainderAbscissa)) =
          2 * Ku * Kr * (x ^ (-cutoffAbscissa) * x ^ (-remainderAbscissa)) by ring, hp1]
  have h2 : ‖2 * primeSquareCoef * (x : ℂ) ^ (-(1 / 2 : ℂ)) * R x‖ ≤
      2 * ‖primeSquareCoef‖ * Kr * x ^ (-(remainderAbscissa + cutoffAbscissa)) := by
    simp only [norm_mul, Complex.norm_ofNat, norm_cpow_eq_rpow_re_of_pos hx.1]
    norm_num only [neg_re, div_ofNat_re, one_re]
    calc
      _ ≤ 2 * ‖primeSquareCoef‖ * x ^ (-(1 / 2 : ℝ)) * (Kr * x ^ (-remainderAbscissa)) := by
        gcongr
        exact hr x hx
      _ = 2 * ‖primeSquareCoef‖ * Kr * (x ^ (-(1 / 2 : ℝ)) * x ^ (-remainderAbscissa)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hp2 (by positivity)
  have h3 : ‖R x ^ 2‖ ≤ Kr ^ 2 * x ^ (-(remainderAbscissa + cutoffAbscissa)) := by
    rw [norm_pow]
    calc
      _ ≤ (Kr * x ^ (-remainderAbscissa)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hr x hx) 2
      _ = Kr ^ 2 * (x ^ (-remainderAbscissa)) ^ 2 := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hp3 (sq_nonneg _)
  exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add h1 h2)) h3) |>.trans (by ring_nf; rfl)

lemma differentiableOn_H (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3)
    (hStir : StirlingStrip) {E : Finset NontrivialZeros} (hE : IsCutoff E) :
    DifferentiableOn ℂ (H E) (halfPlane (remainderAbscissa + cutoffAbscissa)) := by
  obtain ⟨K, -, hK⟩ := norm_regularError_le hH hZ1 hZ2 hZ3 hStir hE
  exact TIdentity.differentiableOn_integral_Ioc_cpow (regularError_meas E) hK

end GoldbachBoundaries.T0HInf
