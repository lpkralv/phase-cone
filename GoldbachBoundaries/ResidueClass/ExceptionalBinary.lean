import GoldbachBoundaries.ResidueClass.BinaryBoundary
import GoldbachBoundaries.ResidueClass.ExceptionalMellin
import GoldbachBoundaries.ResidueClass.PrimitiveLocalProof

/-! # The class-one binary boundary with finitely many exceptional zeros -/

noncomputable section

open Complex Filter Set MeasureTheory Topology

namespace GoldbachBoundaries.ResidueClass

variable {q : ℕ} [NeZero q]

private def exceptionalBinaryRemainder (q : ℕ) [NeZero q] (E : Finset ℂ) (x : ℝ) : ℂ :=
  smoothedResidual q x ^ 2 - (zeroTerm q x + exceptionalTerm q E x)^2

private theorem exceptionalBinaryRemainder_meas (E : Finset ℂ) :
    AEStronglyMeasurable (exceptionalBinaryRemainder q E) (volume.restrict (Ioc 0 1)) :=
  (((continuousOn_smoothedResidual (q := q)).mono Ioc_subset_Ioi_self).pow 2).aestronglyMeasurable
    measurableSet_Ioc |>.sub ((aestronglyMeasurable_zeroTerm.add
      (aestronglyMeasurable_exceptionalTerm E)).pow 2)

private def exceptionalBinaryCorrection (q : ℕ) [NeZero q] (E : Finset ℂ) (s : ℂ) : ℂ :=
  W q s + exceptionalCauchy q E s

private def exceptionalBinaryHolomorphic (q : ℕ) [NeZero q] (E : Finset ℂ) : ℂ → ℂ :=
  binaryHolomorphicPart q (exceptionalBinaryRemainder q E)

private def exceptionalBinaryContinuation (q : ℕ) [NeZero q] (E : Finset ℂ) (s : ℂ) : ℂ :=
  (Gamma s)⁻¹ * (exceptionalBinaryCorrection q E s + cauchySquare q s + exceptionalBinaryHolomorphic q E s)

theorem phi2_natural_boundary_finite_exceptions_of_local (_hq : 2 ≤ q)
    (hE : (OffLineZeros q).Finite) (hZ3 : Paper2.Z3) (hLocal : LogDerivPrimitiveLocal q)
    (hGap : Paper2.ZLittlewood) (hStir : Phi2HInf.StirlingStrip) :
    (∃ F : ℂ → ℂ, MeromorphicOn F HH ∧ EqOn F (Phi2 q) (halfPlane 2)) ∧
    (∀ F : ℂ → ℂ, MeromorphicOn F HH → F =ᶠ[codiscreteWithin (halfPlane 2)] Phi2 q →
      IsNaturalBoundary F HH lineOne) := by
  classical
  obtain ⟨T, _, hline⟩ := exists_high_critical hE
  obtain ⟨B, δ, hB₀, _, hδ, hδ', hBδ, hstrip⟩ := exists_exception_strip hE
  let E := hE.toFinset
  have he (ρ : ℂ) : ρ ∈ E ↔ ρ ∈ OffLineZeros q := hE.mem_toFinset
  let Z : ℝ := ∑' t : Ordinates q, ‖gammaWeight q t‖
  let X : ℝ := ∑ ρ ∈ E, ‖exceptionalWeight q ρ‖
  have hZ : 0 ≤ Z := tsum_nonneg (fun _ ↦ norm_nonneg _)
  have hX : 0 ≤ X := Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _)
  have hb (x : ℝ) (hx : x ∈ Ioc (0 : ℝ) 1) :
      ‖zeroTerm q x + exceptionalTerm q E x‖ ≤ (Z + X) * x ^ (-B) := by
    rw [add_mul]
    apply (norm_add_le _ _).trans
    exact add_le_add ((norm_zeroTerm_le_unconditional hx.1).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hx.1 hx.2 (by linarith)) hZ))
      (norm_exceptionalTerm_le (fun ρ hρ ↦ (hstrip ρ ((he ρ).mp hρ)).2) hx)
  have hF (x : ℝ) (hx : 0 < x) :
      smoothedResidual q x = -(zeroTerm q x + exceptionalTerm q E x) + lineRemainder q δ x := by
    rw [smoothedResidual, smoothed_explicit_formula_with_exceptions hline hZ3 hLocal hδ hδ' hx
      he (fun ρ hρ ↦ (hstrip ρ ((he ρ).mp hρ)).1)]
    ring
  obtain ⟨C, hC⟩ := exists_norm_residual_square_sub_bound (by linarith : δ ≤ B)
    _ (add_nonneg hZ hX) hb hF
  have hDiff : DifferentiableOn ℂ (exceptionalBinaryHolomorphic q E) (halfPlane (B + δ)) :=
    differentiableOn_binaryHolomorphicPart (exceptionalBinaryRemainder_meas E) hC
  have hW : Meromorphic (exceptionalBinaryCorrection q E) :=
    fun s ↦ (meromorphic_W q s).add (meromorphic_exceptionalCauchy E s)
  have hM : MeromorphicOn (exceptionalBinaryContinuation q E) HH := by
    intro s hs
    have hs' : 1 < s.re := hs
    have h₁ := (differentiableOn_cauchySquare_unconditional q).analyticAt ((isOpen_halfPlane _).mem_nhds hs)
    have h₂ := hDiff.analyticAt ((isOpen_halfPlane _).mem_nhds (hBδ.trans hs'))
    exact (PhiRProof.analyticAt_inv_Gamma s).meromorphicAt.mul
      (((hW s).add h₁.meromorphicAt).add h₂.meromorphicAt)
  have hInit : EqOn (exceptionalBinaryContinuation q E) (Phi2 q) (halfPlane 2) := by
    intro s hs
    have hs' : 2 < s.re := hs
    obtain ⟨hI, hIv⟩ := integral_zeroTerm_add_exceptional_sq (q := q)
      (fun ρ hρ ↦ OffLineZeros.re_lt_one ((he ρ).mp hρ)) hs'
    have hR := Phi2Proof.C_integrableOn_mellin (exceptionalBinaryRemainder_meas E) hC
      (s := s) (by linarith)
    have h := Gamma_mul_Phi2_eq_of_zero_square hs' hI hIv hR
    unfold exceptionalBinaryContinuation exceptionalBinaryCorrection exceptionalBinaryHolomorphic exceptionalBinaryRemainder
    rw [add_right_comm (W q s) (exceptionalCauchy q E s) (cauchySquare q s),
      add_assoc (W q s), ← h, ← mul_assoc,
      inv_mul_cancel₀ (Gamma_ne_zero_of_re_pos (by linarith)), one_mul]
  have hRegular := isNaturalBoundary_cauchySquare_add hBδ hDiff (fun y ε hε ↦ by
    obtain ⟨τ, hn, ht, _, hr⟩ := exists_nearby_pairResidue_ne_zero_of_high_critical
      (q := q) (fun ρ hρ ↦ hline 1 ρ ((primitiveZeros_one (q := q)).symm ▸ hρ))
      hGap hStir y hε (finite_meromorphic_poles_line_Icc hW (y - ε) (y + ε))
    exact ⟨τ, hn, ht, hr⟩)
  exact ⟨⟨_, hM, hInit⟩, isNaturalBoundary_binary_of_decomposition hW hRegular hM hInit⟩

/-- The binary class-one boundary with a finite set of off-line primitive
zeros, including real zeros, using the high-window local expansion. -/
theorem phi2_natural_boundary_finite_exceptions (hq : 2 ≤ q)
    (hE : (OffLineZeros q).Finite) (hZ3 : Paper2.Z3) (hGap : Paper2.ZLittlewood)
    (hStir : Phi2HInf.StirlingStrip) :
    (∃ F : ℂ → ℂ, MeromorphicOn F HH ∧ EqOn F (Phi2 q) (halfPlane 2)) ∧
    (∀ F : ℂ → ℂ, MeromorphicOn F HH → F =ᶠ[codiscreteWithin (halfPlane 2)] Phi2 q →
      IsNaturalBoundary F HH lineOne) :=
  phi2_natural_boundary_finite_exceptions_of_local hq hE hZ3
    (logDerivPrimitiveLocal_of_finite_exceptions hE) hGap hStir

end GoldbachBoundaries.ResidueClass
