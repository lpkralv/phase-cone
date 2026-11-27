import GoldbachBoundaries.ResidueClass.TwoDeletionRemainder
import GoldbachBoundaries.PhiR.Statement
import GoldbachBoundaries.Paper2.M3.Zeros

/-! # The modulus-two boundary from the unrestricted Goldbach series -/

noncomputable section

open Complex Filter Set

namespace GoldbachBoundaries.ResidueClass

open Paper2 (Z2 Z3 ZLittlewood)

private theorem character_two_eq_one (χ : DirichletCharacter ℂ 2) : χ = 1 := by
  classical
  have h : Fintype.card (ZMod 2)ˣ ≤ 1 := by
    rw [ZMod.card_units_eq_totient, Nat.totient_two]
  apply MulChar.ext
  intro u
  rw [Fintype.card_le_one_iff.mp h u 1]
  simp

/-- GRH at modulus two is RH because its only character is principal. -/
theorem grh_two_iff_riemannHypothesis : GRH 2 ↔ RiemannHypothesis := by
  rw [Paper2.M3.riemannHypothesis_iff]
  have h : primitiveZeros (1 : DirichletCharacter ℂ 2) = NontrivialZeros := by
    rw [primitiveZeros, primitiveL_one, NontrivialZeros]
  constructor
  · intro hGRH ρ hρ
    exact hGRH 1 ρ (h.symm ▸ hρ)
  · intro hRH χ ρ hρ
    rw [character_two_eq_one χ, h] at hρ
    exact hRH ρ hρ

/-- The explicit Euler-factor contribution is meromorphic on the whole plane. -/
theorem meromorphic_twoEulerCorrection (r : ℕ) : Meromorphic (twoEulerCorrection r) := by
  intro s
  let z : ℂ → ℂ := fun w ↦ w - r + 1
  have hz : AnalyticAt ℂ z s := by dsimp [z]; fun_prop
  have hpow : AnalyticAt ℂ (fun w ↦ (2 : ℂ) ^ (-z w)) s := by
    apply Differentiable.analyticAt
    intro w
    exact ((show DifferentiableAt ℂ z w by dsimp [z]; fun_prop).neg.const_cpow
      (Or.inl (by norm_num)))
  have hGamma : MeromorphicAt (fun w ↦ Gamma (z w)) s :=
    MeromorphicAt.comp_analyticAt (PhiRProof.meromorphicAt_Gamma _) hz
  unfold twoEulerCorrection
  exact ((MeromorphicAt.const _ s).mul hGamma |>.mul hpow.meromorphicAt).div
    ((PhiRProof.meromorphicAt_Gamma s).mul (analyticAt_const.sub hpow).meromorphicAt)

private def twoDifference (r : ℕ) (s : ℂ) : ℂ :=
  twoEulerCorrection r s + twoHolomorphicRemainder r s

private theorem meromorphicOn_twoDifference (hRH : RiemannHypothesis) {r : ℕ} (hr : 2 ≤ r) :
    MeromorphicOn (twoDifference r) (halfPlane ((r : ℝ) - 3 / 2)) :=
  fun s hs ↦ (meromorphic_twoEulerCorrection r s).add
    ((analyticOnNhd_twoHolomorphicRemainder hRH hr) s hs).meromorphicAt

private theorem twoDifference_eq (hRH : RiemannHypothesis) {r : ℕ} (hr : 2 ≤ r)
    {s : ℂ} (hs : s ∈ halfPlane r) :
    twoDifference r s = GoldbachBoundaries.PhiR r s - PhiR 2 r s := by
  have h := eqOn_twoHolomorphicRemainder hRH hr hs
  change twoHolomorphicRemainder r s =
    GoldbachBoundaries.PhiR r s - PhiR 2 r s - twoEulerCorrection r s at h
  rw [twoDifference, h]
  ring

/-- The odd-summand continuation obtained by deleting the Euler-factor
contribution and the holomorphic Mellin remainder from the unrestricted continuation. -/
def phiRTwoContinuation (r : ℕ) (s : ℂ) : ℂ :=
  PhiRProof.PhiRc r s - twoDifference r s

/-- The difference of the two continued series, after subtracting the explicit
Euler-factor contribution, extends holomorphically to Re s > r − 3/2. -/
theorem phiRc_sub_phiRTwoContinuation_extends (hRH : RiemannHypothesis) {r : ℕ} (hr : 2 ≤ r) :
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H (halfPlane ((r : ℝ) - 3 / 2)) ∧
      EqOn H (fun s ↦ PhiRProof.PhiRc r s - phiRTwoContinuation r s - twoEulerCorrection r s)
        (halfPlane ((r : ℝ) - 1)) := by
  refine ⟨twoHolomorphicRemainder r, analyticOnNhd_twoHolomorphicRemainder hRH hr, fun s _ ↦ ?_⟩
  change twoHolomorphicRemainder r s =
    PhiRProof.PhiRc r s - (PhiRProof.PhiRc r s - twoDifference r s) - twoEulerCorrection r s
  unfold twoDifference
  ring

/-- The odd-summand series continues to Re s > r − 1, and the line
Re s = r − 1 is a natural boundary for every meromorphic continuation.
The proof transfers the unrestricted boundary by the deletion at two. -/
theorem phiR_two_natural_boundary_of_unrestricted (hRH : RiemannHypothesis)
    (hZ2 : Z2) (hZ3 : Z3) (hL : ZLittlewood) {r : ℕ} (hr : 2 ≤ r) :
    (MeromorphicOn (phiRTwoContinuation r) (halfPlane ((r : ℝ) - 1)) ∧
      EqOn (phiRTwoContinuation r) (PhiR 2 r) (halfPlane r)) ∧
    (∀ F : ℂ → ℂ, MeromorphicOn F (halfPlane ((r : ℝ) - 1)) →
      F =ᶠ[codiscreteWithin (halfPlane r)] PhiR 2 r →
      IsNaturalBoundary F (halfPlane ((r : ℝ) - 1)) (lineAt ((r : ℝ) - 1))) := by
  let U := halfPlane ((r : ℝ) - 1)
  let V := halfPlane ((r : ℝ) - 3 / 2)
  have hUV : U ⊆ V := fun s (hs : (r : ℝ) - 1 < s.re) ↦
    show (r : ℝ) - 3 / 2 < s.re by linarith
  have hD : MeromorphicOn (twoDifference r) V := meromorphicOn_twoDifference hRH hr
  refine ⟨⟨(PhiRProof.meromorphicOn_PhiRc hRH hr).sub (hD.mono_set hUV), ?_⟩, ?_⟩
  · intro s hs
    rw [phiRTwoContinuation, (PhiRProof.phiR_continuation hRH hr).2.1 hs, twoDifference_eq hRH hr hs]
    abel
  · intro F hF hEq
    have hsum : (fun s ↦ F s + twoDifference r s) =ᶠ[codiscreteWithin (halfPlane r)]
        GoldbachBoundaries.PhiR r := by
      filter_upwards [hEq, self_mem_codiscreteWithin (halfPlane r)] with s h₁ h₂
      rw [h₁, twoDifference_eq hRH hr h₂]
      abel
    have hBoundary := (GoldbachBoundaries.phiR_natural_boundary hRH hZ2 hZ3 hL hr).2
      _ (hF.add (hD.mono_set hUV)) hsum
    intro s₀ hs₀
    have hsV : s₀ ∈ V := by
      change s₀.re = (r : ℝ) - 1 at hs₀
      change (r : ℝ) - 3 / 2 < s₀.re
      linarith
    exact (PhiRProof.noMeromorphicExtensionAt_iff_of_eq_add_mul
      (F := F + twoDifference r) (f := fun _ ↦ (1 : ℂ)) (H := F)
      (isOpen_halfPlane _) hsV hD (fun _ _ ↦ analyticAt_const) (fun _ _ ↦ one_ne_zero)
      (Eventually.of_forall fun s ↦ by simp [Pi.add_apply, add_comm])).mp (hBoundary s₀ hs₀)

end GoldbachBoundaries.ResidueClass
