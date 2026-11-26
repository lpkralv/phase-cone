import GoldbachBoundaries.ResidueClass.BinaryContinuation
import GoldbachBoundaries.ResidueClass.BoundaryDensity
import GoldbachBoundaries.ResidueClass.PoleWindows
import GoldbachBoundaries.PhiR.Proof.M3Boundary

/-! # The natural boundary of the binary continuation -/

noncomputable section

open Complex Filter Set Topology

namespace GoldbachBoundaries.ResidueClass

variable {q : ℕ} [NeZero q]

theorem tendsto_radial_regularPart (hGRH : GRH q) (hZ3 : Paper2.Z3)
    (hLocal : LogDerivPrimitiveLocal q) (τ : ℝ) :
    Tendsto (fun η : ℝ ↦ (η : ℂ) *
      (cauchySquare q (1 + τ * I + η) + holomorphicCorrection q (1 + τ * I + η)))
      (𝓝[>] 0) (𝓝 (pairResidue q τ)) := by
  let z : ℂ := 1 + (τ : ℂ) * I
  have hη : Tendsto (fun η : ℝ ↦ (η : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (continuous_ofReal.tendsto 0).mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have hdir : Tendsto (fun η : ℝ ↦ z + (η : ℂ)) (𝓝[>] 0) (𝓝 z) := by
    simpa using (tendsto_const_nhds (x := z)).add hη
  have hDiff := differentiableOn_holomorphicCorrection hGRH hZ3 hLocal
    (δ := 1 / 4) (by norm_num) (by norm_num)
  have hz : z ∈ halfPlane (1 / 2 + 1 / 4) := by
    change (1 / 2 + 1 / 4 : ℝ) < z.re
    norm_num [z]
  have hcont := (hDiff.analyticAt ((isOpen_halfPlane _).mem_nhds hz)).continuousAt
  have h := (tendsto_radial_cauchySquare hGRH τ).add (hη.mul (hcont.tendsto.comp hdir))
  simpa only [Function.comp_apply, zero_mul, add_zero, mul_add, z] using h

/-- After subtracting the meromorphic correction, the radial limit of the
binary continuation is the summed pair residue divided by Gamma. -/
theorem tendsto_radial_phi2Continuation (hGRH : GRH q) (hZ3 : Paper2.Z3)
    (hLocal : LogDerivPrimitiveLocal q) (τ : ℝ) :
    Tendsto (fun η : ℝ ↦ (η : ℂ) *
      (phi2Continuation q (1 + τ * I + η) - W q (1 + τ * I + η) / Gamma (1 + τ * I + η)))
      (𝓝[>] 0) (𝓝 (pairResidue q τ / Gamma (1 + τ * I))) := by
  let z : ℂ := 1 + (τ : ℂ) * I
  have hη : Tendsto (fun η : ℝ ↦ (η : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (continuous_ofReal.tendsto 0).mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have hdir : Tendsto (fun η : ℝ ↦ z + (η : ℂ)) (𝓝[>] 0) (𝓝 z) := by
    simpa using (tendsto_const_nhds (x := z)).add hη
  have h := ((PhiRProof.analyticAt_inv_Gamma z).continuousAt.tendsto.comp hdir).mul
    (tendsto_radial_regularPart hGRH hZ3 hLocal τ)
  convert h using 1
  · funext η
    simp only [Function.comp_apply, z, phi2Continuation, div_eq_mul_inv]
    ring
  · rw [div_eq_mul_inv, mul_comm]

theorem isNaturalBoundary_regularPart (hGRH : GRH q) (hZ3 : Paper2.Z3)
    (hLocal : LogDerivPrimitiveLocal q) (hGap : Paper2.ZLittlewood) (hStir : Phi2HInf.StirlingStrip) :
    IsNaturalBoundary (fun s ↦ cauchySquare q s + holomorphicCorrection q s) HH lineOne := by
  intro z hz
  have hz' : z.re = 1 := hz
  have he : z = 1 + (z.im : ℂ) * I := by apply Complex.ext <;> simp [hz']
  nth_rw 1 [he]
  apply Paper2.M5.noMeromorphicExtensionAt_of_line_blowup
  · apply (differentiableOn_cauchySquare hGRH).add
    exact (differentiableOn_holomorphicCorrection hGRH hZ3 hLocal
      (δ := 1 / 4) (by norm_num) (by norm_num)).mono fun s hs ↦ by
      change 1 < s.re at hs
      change (1 / 2 + 1 / 4 : ℝ) < s.re
      linarith
  · intro ε hε
    obtain ⟨τ, hn, ht, _, hr⟩ := exists_nearby_pairResidue_ne_zero hGRH hGap hStir z.im hε
      (finite_W_poles_line_Icc (q := q) (z.im - ε) (z.im + ε))
    exact ⟨τ, hn, ht, pairResidue q τ, hr, tendsto_radial_regularPart hGRH hZ3 hLocal τ⟩

/-- Any binary continuation agreeing on the initial half-plane has a natural boundary. -/
theorem isNaturalBoundary_phi2_of_agrees (hGRH : GRH q) (hZ3 : Paper2.Z3)
    (hLocal : LogDerivPrimitiveLocal q) (hGap : Paper2.ZLittlewood) (hStir : Phi2HInf.StirlingStrip)
    (F : ℂ → ℂ) (hF : MeromorphicOn F HH)
    (hAgree : F =ᶠ[codiscreteWithin (halfPlane 2)] Phi2 q) :
    IsNaturalBoundary F HH lineOne := by
  have hE := Phi2Proof.eventuallyEq_codiscreteWithin_of_nhdsNE fun z hz ↦
    Phi2Proof.eventuallyEq_nhdsNE_of_agree_halfPlane_two' hF
      (meromorphicOn_phi2Continuation hGRH hZ3 hLocal) (eqOn_phi2Continuation hGRH hZ3 hLocal)
      hAgree hz
  have hEq : F =ᶠ[codiscreteWithin HH] fun s ↦ (Gamma s)⁻¹ * W q s +
      (Gamma s)⁻¹ * (cauchySquare q s + holomorphicCorrection q s) := by
    filter_upwards [hE] with s hs
    rw [hs, phi2Continuation]
    ring
  intro z hz
  have hz' : z.re = 1 := hz
  have hz₀ : z ∈ halfPlane 0 := by change 0 < z.re; linarith
  apply (PhiRProof.noMeromorphicExtensionAt_iff_of_eq_add_mul
    (isOpen_halfPlane 0) hz₀
    (fun s _ ↦ (PhiRProof.analyticAt_inv_Gamma s).meromorphicAt.mul (meromorphic_W q s))
    (fun s _ ↦ PhiRProof.analyticAt_inv_Gamma s)
    (fun s hs ↦ inv_ne_zero (Gamma_ne_zero_of_re_pos hs)) hEq).mpr
  exact isNaturalBoundary_regularPart hGRH hZ3 hLocal hGap hStir z hz

end GoldbachBoundaries.ResidueClass
