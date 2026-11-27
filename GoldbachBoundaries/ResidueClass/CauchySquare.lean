import GoldbachBoundaries.ResidueClass.GammaWeights
import GoldbachBoundaries.Phi2HInf.Fill.zero_mellin
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-! # The Cauchy series from the Mellin transform of the squared zero sum -/

noncomputable section

open Complex Filter Set MeasureTheory Metric

namespace GoldbachBoundaries.ResidueClass

variable {q : ℕ} [NeZero q]

private instance countable_ordinates : Countable (Ordinates q) := by
  have h (n : ℕ) : (Ordinates q ∩ Icc (-(n : ℝ)) (n : ℝ)).Countable :=
    (finite_Ordinates_inter _ _).countable
  refine ((Set.countable_iUnion h).mono ?_).to_subtype
  intro t ht
  obtain ⟨n, hn⟩ := exists_nat_ge |t|
  exact Set.mem_iUnion.mpr ⟨n, ht, abs_le.mp hn⟩

/-- Ordered pairs of participating ordinates. -/
abbrev OrdinatePair (q : ℕ) [NeZero q] := Ordinates q × Ordinates q

def pairWeight (q : ℕ) [NeZero q] (p : OrdinatePair q) : ℂ :=
  gammaWeight q p.1 * gammaWeight q p.2

def pairPoint (q : ℕ) [NeZero q] (p : OrdinatePair q) : ℂ :=
  criticalPoint p.1 + criticalPoint p.2

@[simp] theorem pairPoint_re (p : OrdinatePair q) : (pairPoint q p).re = 1 := by
  norm_num [pairPoint, criticalPoint_re]

@[simp] theorem pairPoint_im (p : OrdinatePair q) : (pairPoint q p).im = (p.1 : ℝ) + p.2 := by
  simp [pairPoint, criticalPoint_im]

theorem summable_norm_pairWeight_unconditional (q : ℕ) [NeZero q] :
    Summable (fun p : OrdinatePair q ↦ ‖pairWeight q p‖) :=
  Summable.mul_norm (f := fun t : Ordinates q ↦ gammaWeight q t)
    (g := fun t : Ordinates q ↦ gammaWeight q t)
    (summable_norm_gammaWeight_unconditional q) (summable_norm_gammaWeight_unconditional q)

/-- The double Cauchy series on the half-plane to the right of all pair locations. -/
def cauchySquare (q : ℕ) [NeZero q] (s : ℂ) : ℂ :=
  ∑' p : OrdinatePair q, pairWeight q p / (s - pairPoint q p)

theorem differentiableOn_cauchySquare_unconditional (q : ℕ) [NeZero q] :
    DifferentiableOn ℂ (cauchySquare q) HH := by
  intro s hs
  have hs' : 1 < s.re := hs
  let d : ℝ := (s.re - 1) / 2
  have hd : 0 < d := by dsimp [d]; linarith
  have hb (p : OrdinatePair q) (z : ℂ) (hz : z ∈ halfPlane (1 + d)) :
      d ≤ ‖z - pairPoint q p‖ := by
    have h := re_le_norm (z - pairPoint q p)
    rw [sub_re, pairPoint_re] at h
    change 1 + d < z.re at hz
    linarith
  have hdif : DifferentiableOn ℂ (cauchySquare q) (halfPlane (1 + d)) := by
    apply Complex.differentiableOn_tsum_of_summable_norm
      ((summable_norm_pairWeight_unconditional q).div_const d)
    · intro p z hz
      have hne : z - pairPoint q p ≠ 0 := norm_pos_iff.mp (hd.trans_le (hb p z hz))
      exact (differentiableWithinAt_const _).div (differentiableWithinAt_id.sub_const _) hne
    · exact isOpen_halfPlane _
    · intro p z hz
      rw [norm_div]
      exact div_le_div_of_nonneg_left (norm_nonneg _) hd (hb p z hz)
  exact (hdif.differentiableAt ((isOpen_halfPlane _).mem_nhds
    (show s ∈ halfPlane (1 + d) by change 1 + d < s.re; dsimp [d]; linarith))).differentiableWithinAt

/-- Termwise integration of the squared zero sum on the unit interval. -/
theorem integral_zeroTerm_sq_unconditional {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ ↦ zeroTerm q x ^ 2 * (x : ℂ) ^ (s - 1)) (Ioc 0 1) ∧
      (∫ x in Ioc (0 : ℝ) 1, zeroTerm q x ^ 2 * (x : ℂ) ^ (s - 1)) = cauchySquare q s := by
  have h := Phi2HInf.integral_cpow_family (pairWeight q) (pairPoint q)
    (summable_norm_pairWeight_unconditional q) (fun p ↦ by simp) hs
  have heq (x : ℝ) (hx : x ∈ Ioc (0 : ℝ) 1) :
      zeroTerm q x ^ 2 = ∑' p : OrdinatePair q, pairWeight q p * (x : ℂ) ^ (-pairPoint q p) := by
    have hsum := summable_norm_zeroTerm_unconditional (q := q) hx.1
    rw [pow_two, zeroTerm, tsum_mul_tsum_of_summable_norm hsum hsum]
    apply tsum_congr
    intro p
    simp only [pairWeight, pairPoint, neg_add]
    rw [cpow_add _ _ (ofReal_ne_zero.mpr hx.1.ne')]
    ring
  refine ⟨h.1.congr_fun (fun x hx ↦ by rw [heq x hx]) measurableSet_Ioc, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioc (fun x hx ↦ by rw [heq x hx]), h.2]
  rfl

theorem aestronglyMeasurable_zeroTerm :
    AEStronglyMeasurable (zeroTerm q) (volume.restrict (Ioc 0 1)) :=
  AEStronglyMeasurable.tsum (fun t : Ordinates q ↦
    (Phi2Proof.C_cpow_meas (-criticalPoint t)).const_mul (gammaWeight q t))

theorem summable_norm_pairWeight (hGRH : GRH q) :
    Summable (fun p : OrdinatePair q ↦ ‖pairWeight q p‖) :=
  summable_norm_pairWeight_unconditional q

theorem differentiableOn_cauchySquare (hGRH : GRH q) :
    DifferentiableOn ℂ (cauchySquare q) HH :=
  differentiableOn_cauchySquare_unconditional q

theorem integral_zeroTerm_sq (hGRH : GRH q) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ ↦ zeroTerm q x ^ 2 * (x : ℂ) ^ (s - 1)) (Ioc 0 1) ∧
      (∫ x in Ioc (0 : ℝ) 1, zeroTerm q x ^ 2 * (x : ℂ) ^ (s - 1)) = cauchySquare q s :=
  integral_zeroTerm_sq_unconditional hs

end GoldbachBoundaries.ResidueClass
