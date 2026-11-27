import GoldbachBoundaries.ResidueClass.PrimitiveLocalProof
import GoldbachBoundaries.ResidueClass.RealPoint
import GoldbachBoundaries.ResidueClass.Statement
import Batteries.Tactic.OpenPrivate

/-! # Residue-class theorems with the local Dirichlet expansion supplied by GRH -/

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology

namespace GoldbachBoundaries.ResidueClass

variable {q : ℕ} [NeZero q]

open private exists_norm_D_le_of_separated from GoldbachBoundaries.ResidueClass.ContourBounds
open private norm_smoothedResidual_le higherTail_bound differentiableOn_higherRemainder
  meromorphicOn_higherCorrection higherCorrection higherRemainder binaryFactor linearFactor
  constantFactor from GoldbachBoundaries.ResidueClass.HigherReduction
open private higherSmallMellin analyticAt_higherSmallMellin tendsto_sub_main_at_real
  from GoldbachBoundaries.ResidueClass.RealPoint

theorem exists_logDeriv_primitive_local_bound_of_proved (hGRH : GRH q) (hZ3 : Paper2.Z3) :
    ∃ A T₀ : ℝ, 0 ≤ A ∧ 2 ≤ T₀ ∧
      ∀ (χ : DirichletCharacter ℂ q) (z : ℂ), 0 < z.re → z.re ≤ 2 → T₀ ≤ |z.im| →
        primitiveL χ z ≠ 0 →
        ‖logDeriv (primitiveL χ) z -
          ∑ᶠ ρ ∈ {ρ ∈ primitiveZeros χ | |ρ.im - z.im| ≤ 1},
            (primitiveMult χ ρ : ℂ) / (z - ρ)‖ ≤ A * Real.log (2 + |z.im|) :=
  exists_logDeriv_primitive_local_bound hZ3 (logDerivPrimitiveLocal_of_GRH hGRH)

theorem exists_norm_logDeriv_primitive_le_of_separated_of_proved (hGRH : GRH q) (hZ3 : Paper2.Z3) :
    ∃ A B T₀ : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 2 ≤ T₀ ∧
      ∀ (χ : DirichletCharacter ℂ q) (z : ℂ) (d : ℝ), 0 < d → 0 < z.re → z.re ≤ 2 →
        T₀ ≤ |z.im| → primitiveL χ z ≠ 0 →
        (∀ ρ ∈ primitiveZeros χ, |ρ.im - z.im| ≤ 1 → d ≤ ‖z - ρ‖) →
        ‖logDeriv (primitiveL χ) z‖ ≤ A * Real.log (2 + |z.im|) + B * Real.log (|z.im| + 4) / d :=
  exists_norm_logDeriv_primitive_le_of_separated hGRH hZ3 (logDerivPrimitiveLocal_of_GRH hGRH)

private theorem exists_norm_D_le_of_separated_of_proved {δ : ℝ} (hδ : 0 < δ)
    (hGRH : GRH q) (hZ3 : Paper2.Z3) :
    ∃ A B E T₀ : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 ≤ E ∧ 2 ≤ T₀ ∧
      ∀ (z : ℂ) (d : ℝ), 0 < d → δ ≤ z.re → z.re ≤ 2 → T₀ ≤ |z.im| →
        (∀ t ∈ Ordinates q, d ≤ ‖z - criticalPoint t‖) →
        ‖D q z‖ ≤ A * Real.log (2 + |z.im|) + B * Real.log (|z.im| + 4) / d + E :=
  exists_norm_D_le_of_separated hδ hGRH hZ3 (logDerivPrimitiveLocal_of_GRH hGRH)

theorem exists_norm_D_left_bound_of_proved (hGRH : GRH q) (hZ3 : Paper2.Z3)
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 2) :
    ∃ K : ℝ, ∀ y : ℝ, ‖D q (δ + y * I)‖ ≤ K * (1 + |y|) :=
  exists_norm_D_left_bound hGRH hZ3 (logDerivPrimitiveLocal_of_GRH hGRH) hδ hδ'

theorem integrable_Gamma_mul_D_left_of_proved (hGRH : GRH q) (hZ3 : Paper2.Z3)
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 2) :
    Integrable fun y : ℝ ↦ Gamma (δ + y * I) * D q (δ + y * I) :=
  integrable_Gamma_mul_D_left hGRH hZ3 (logDerivPrimitiveLocal_of_GRH hGRH) hδ hδ'

theorem exists_D_horizontal_bounds_of_proved (hGRH : GRH q) (hZ3 : Paper2.Z3)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ K Y₀ : ℝ, 0 ≤ K ∧ 2 ≤ Y₀ ∧ ∀ Y : ℝ, Y₀ ≤ Y → ∃ H ∈ Icc Y (Y + 1),
      (∀ t ∈ Ordinates q, |t| ≠ H) ∧
      ∀ z : ℂ, δ ≤ z.re → z.re ≤ 2 → |z.im| = H → ‖D q z‖ ≤ K * (1 + H) ^ 2 :=
  exists_D_horizontal_bounds hGRH hZ3 (logDerivPrimitiveLocal_of_GRH hGRH) hδ

theorem smoothed_explicit_formula_of_proved (hGRH : GRH q) (hZ3 : Paper2.Z3)
    {δ x : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 2) (hx : 0 < x) :
    (smoothed q x : ℂ) =
      principalWeight q / (x : ℂ) - zeroTerm q x + lineRemainder q δ x :=
  smoothed_explicit_formula hGRH hZ3 (logDerivPrimitiveLocal_of_GRH hGRH) hδ hδ' hx

theorem exists_norm_smallRemainder_bound_of_proved (hGRH : GRH q) (hZ3 : Paper2.Z3)
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 2) :
    ∃ C : ℝ, ∀ x ∈ Ioc (0 : ℝ) 1, ‖smallRemainder q x‖ ≤ C * x ^ (-(1 / 2 + δ)) :=
  exists_norm_smallRemainder_bound hGRH hZ3 (logDerivPrimitiveLocal_of_GRH hGRH) hδ hδ'

theorem differentiableOn_holomorphicCorrection_of_proved (hGRH : GRH q) (hZ3 : Paper2.Z3)
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 2) :
    DifferentiableOn ℂ (holomorphicCorrection q) (halfPlane (1 / 2 + δ)) :=
  differentiableOn_holomorphicCorrection hGRH hZ3 (logDerivPrimitiveLocal_of_GRH hGRH) hδ hδ'

theorem Gamma_mul_Phi2_eq_of_proved (hGRH : GRH q) (hZ3 : Paper2.Z3)
    {s : ℂ} (hs : 2 < s.re) :
    Gamma s * Phi2 q s = W q s + cauchySquare q s + holomorphicCorrection q s :=
  Gamma_mul_Phi2_eq hGRH hZ3 (logDerivPrimitiveLocal_of_GRH hGRH) hs

theorem meromorphicOn_phi2Continuation_of_proved (hGRH : GRH q) (hZ3 : Paper2.Z3) :
    MeromorphicOn (phi2Continuation q) HH :=
  meromorphicOn_phi2Continuation hGRH hZ3 (logDerivPrimitiveLocal_of_GRH hGRH)

theorem eqOn_phi2Continuation_of_proved (hGRH : GRH q) (hZ3 : Paper2.Z3) :
    EqOn (phi2Continuation q) (Phi2 q) (halfPlane 2) :=
  eqOn_phi2Continuation hGRH hZ3 (logDerivPrimitiveLocal_of_GRH hGRH)

theorem tendsto_radial_regularPart_of_proved (hGRH : GRH q) (hZ3 : Paper2.Z3)
    (τ : ℝ) :
    Tendsto (fun η : ℝ ↦ (η : ℂ) *
      (cauchySquare q (1 + τ * I + η) + holomorphicCorrection q (1 + τ * I + η)))
      (𝓝[>] 0) (𝓝 (pairResidue q τ)) :=
  tendsto_radial_regularPart hGRH hZ3 (logDerivPrimitiveLocal_of_GRH hGRH) τ

theorem tendsto_radial_phi2Continuation_of_proved (hGRH : GRH q) (hZ3 : Paper2.Z3)
    (τ : ℝ) :
    Tendsto (fun η : ℝ ↦ (η : ℂ) *
      (phi2Continuation q (1 + τ * I + η) - W q (1 + τ * I + η) / Gamma (1 + τ * I + η)))
      (𝓝[>] 0) (𝓝 (pairResidue q τ / Gamma (1 + τ * I))) :=
  tendsto_radial_phi2Continuation hGRH hZ3 (logDerivPrimitiveLocal_of_GRH hGRH) τ

theorem isNaturalBoundary_regularPart_of_proved (hGRH : GRH q) (hZ3 : Paper2.Z3)
    (hGap : Paper2.ZLittlewood) (hStir : Phi2HInf.StirlingStrip) :
    IsNaturalBoundary (fun s ↦ cauchySquare q s + holomorphicCorrection q s) HH lineOne :=
  isNaturalBoundary_regularPart hGRH hZ3 (logDerivPrimitiveLocal_of_GRH hGRH) hGap hStir

theorem isNaturalBoundary_phi2_of_agrees_of_proved (hGRH : GRH q) (hZ3 : Paper2.Z3)
    (hGap : Paper2.ZLittlewood) (hStir : Phi2HInf.StirlingStrip)
    (F : ℂ → ℂ) (hF : MeromorphicOn F HH)
    (hAgree : F =ᶠ[codiscreteWithin (halfPlane 2)] Phi2 q) :
    IsNaturalBoundary F HH lineOne :=
  isNaturalBoundary_phi2_of_agrees hGRH hZ3 (logDerivPrimitiveLocal_of_GRH hGRH)
    hGap hStir F hF hAgree

private theorem norm_smoothedResidual_le_of_proved (hGRH : GRH q) (hZ3 : Paper2.Z3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Ioc (0 : ℝ) 1, ‖smoothedResidual q x‖ ≤ C * x ^ (-(1 / 2 : ℝ)) :=
  norm_smoothedResidual_le hGRH hZ3 (logDerivPrimitiveLocal_of_GRH hGRH)

private theorem higherTail_bound_of_proved (hGRH : GRH q) (hZ3 : Paper2.Z3)
    (r : ℕ) :
    ∃ C : ℝ, ∀ x ∈ Ioc (0 : ℝ) 1, ‖higherTail q r x‖ ≤ C * x ^ (-((r : ℝ) - 3 / 2)) :=
  higherTail_bound hGRH hZ3 (logDerivPrimitiveLocal_of_GRH hGRH) r

private theorem differentiableOn_higherRemainder_of_proved (hGRH : GRH q) (hZ3 : Paper2.Z3)
    {r : ℕ} (hr : 2 ≤ r) :
    DifferentiableOn ℂ (higherRemainder q r) (halfPlane ((r : ℝ) - 3 / 2)) :=
  differentiableOn_higherRemainder hGRH hZ3 (logDerivPrimitiveLocal_of_GRH hGRH) hr

theorem Gamma_mul_PhiR_eq_of_proved (hGRH : GRH q) (hZ3 : Paper2.Z3)
    {r : ℕ} (hr : 2 ≤ r) {s : ℂ} (hs : (r : ℝ) < s.re) :
    Gamma s * PhiR q r s =
      binaryFactor q r * (Gamma (s - r + 2) * Phi2 q (s - r + 2)) +
      linearFactor q r * (Gamma (s - r + 1) * D q (s - r + 1)) +
      constantFactor q r / (s - r) + higherRemainder q r s :=
  Gamma_mul_PhiR_eq hGRH hZ3 (logDerivPrimitiveLocal_of_GRH hGRH) hr hs

private theorem meromorphicOn_higherCorrection_of_proved (hGRH : GRH q) (hZ3 : Paper2.Z3)
    {r : ℕ} (hr : 2 ≤ r) :
    MeromorphicOn (higherCorrection q r) (halfPlane ((r : ℝ) - 3 / 2)) :=
  meromorphicOn_higherCorrection hGRH hZ3 (logDerivPrimitiveLocal_of_GRH hGRH) hr

theorem meromorphicOn_phiRContinuation_of_proved (hGRH : GRH q) (hZ3 : Paper2.Z3)
    {r : ℕ} (hr : 2 ≤ r) :
    MeromorphicOn (phiRContinuation q r) (halfPlane ((r : ℝ) - 1)) :=
  meromorphicOn_phiRContinuation hGRH hZ3 (logDerivPrimitiveLocal_of_GRH hGRH) hr

theorem eqOn_phiRContinuation_of_proved (hGRH : GRH q) (hZ3 : Paper2.Z3)
    {r : ℕ} (hr : 2 ≤ r) :
    EqOn (phiRContinuation q r) (PhiR q r) (halfPlane r) :=
  eqOn_phiRContinuation hGRH hZ3 (logDerivPrimitiveLocal_of_GRH hGRH) hr

theorem isNaturalBoundary_phiR_of_agrees_of_proved (hGRH : GRH q) (hZ3 : Paper2.Z3)
    (hGap : Paper2.ZLittlewood) (hStir : Phi2HInf.StirlingStrip)
    {r : ℕ} (hr : 2 ≤ r) (F : ℂ → ℂ)
    (hF : MeromorphicOn F (halfPlane ((r : ℝ) - 1)))
    (hAgree : F =ᶠ[codiscreteWithin (halfPlane r)] PhiR q r) :
    IsNaturalBoundary F (halfPlane ((r : ℝ) - 1)) (lineAt ((r : ℝ) - 1)) :=
  isNaturalBoundary_phiR_of_agrees hGRH hZ3 (logDerivPrimitiveLocal_of_GRH hGRH)
    hGap hStir hr F hF hAgree

private theorem analyticAt_higherSmallMellin_of_proved (hGRH : GRH q) (hZ3 : Paper2.Z3)
    {r : ℕ} (hr : 2 ≤ r) {s : ℂ} (hs : (r : ℝ) - 3 / 2 < s.re) :
    AnalyticAt ℂ (higherSmallMellin q r) s :=
  analyticAt_higherSmallMellin hGRH hZ3 (logDerivPrimitiveLocal_of_GRH hGRH) hr hs

private theorem tendsto_sub_main_at_real_of_proved (hGRH : GRH q) (hZ3 : Paper2.Z3)
    {r : ℕ} (hr : 2 ≤ r) :
    Tendsto (fun η : ℝ ↦ (η : ℂ) *
      (phiRContinuation q r ((r : ℂ) - 1 + η) - phiRMain q r ((r : ℂ) - 1 + η)))
      (𝓝[>] 0)
      (𝓝 ((r.choose 2 : ℂ) * principalWeight q ^ (r - 2) / Gamma ((r : ℂ) - 1) * pairResidue q 0)) :=
  tendsto_sub_main_at_real hGRH hZ3 (logDerivPrimitiveLocal_of_GRH hGRH) hr

theorem phiR_sub_main_real_limit_of_proved (hq : 2 ≤ q) (hGRH : GRH q) (hZ3 : Paper2.Z3)
    {r : ℕ} (hr : 2 ≤ r) :
    Tendsto (fun η : ℝ ↦ (η : ℂ) *
      (phiRContinuation q r ((r : ℂ) - 1 + η) - phiRMain q r ((r : ℂ) - 1 + η))) (𝓝[>] 0)
      (𝓝 (((r.choose 2 : ℝ) / ((q.totient : ℝ) ^ r * ((r - 2).factorial : ℝ)) *
        ∑' t : Ordinates q, (ordinateWeight q t : ℝ) ^ 2 * ‖Gamma (criticalPoint t)‖ ^ 2 : ℝ) : ℂ)) ∧
    0 < (r.choose 2 : ℝ) / ((q.totient : ℝ) ^ r * ((r - 2).factorial : ℝ)) *
      ∑' t : Ordinates q, (ordinateWeight q t : ℝ) ^ 2 * ‖Gamma (criticalPoint t)‖ ^ 2 :=
  phiR_sub_main_real_limit hq hGRH hZ3 (logDerivPrimitiveLocal_of_GRH hGRH) hr

theorem phi2_natural_boundary_of_proved (hq : 2 ≤ q) (hGRH : GRH q) (hZ3 : Paper2.Z3)
    (hGap : Paper2.ZLittlewood) (hStir : Phi2HInf.StirlingStrip) :
    (∃ F : ℂ → ℂ, MeromorphicOn F HH ∧ EqOn F (Phi2 q) (halfPlane 2)) ∧
    (∀ F : ℂ → ℂ, MeromorphicOn F HH → F =ᶠ[codiscreteWithin (halfPlane 2)] Phi2 q →
      IsNaturalBoundary F HH lineOne) :=
  phi2_natural_boundary hq hGRH hZ3 (logDerivPrimitiveLocal_of_GRH hGRH) hGap hStir

theorem phiR_natural_boundary_of_proved (hq : 2 ≤ q) (hGRH : GRH q) (hZ3 : Paper2.Z3)
    (hGap : Paper2.ZLittlewood) (hStir : Phi2HInf.StirlingStrip) {r : ℕ} (hr : 2 ≤ r) :
    (∃ F : ℂ → ℂ, MeromorphicOn F (halfPlane ((r : ℝ) - 1)) ∧
      EqOn F (PhiR q r) (halfPlane r)) ∧
    (∀ F : ℂ → ℂ, MeromorphicOn F (halfPlane ((r : ℝ) - 1)) →
      F =ᶠ[codiscreteWithin (halfPlane r)] PhiR q r →
      IsNaturalBoundary F (halfPlane ((r : ℝ) - 1)) (lineAt ((r : ℝ) - 1))) :=
  phiR_natural_boundary hq hGRH hZ3 (logDerivPrimitiveLocal_of_GRH hGRH) hGap hStir hr

end GoldbachBoundaries.ResidueClass
