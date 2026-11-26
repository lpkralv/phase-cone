import GoldbachBoundaries.ResidueClass.EulerFactors
import GoldbachBoundaries.LogDerivZeta
import Mathlib.Analysis.Meromorphic.LogDeriv

/-! # Strip zeros, their multiplicities, and the poles of the character average -/

noncomputable section

open Complex Filter Set
open scoped Topology

namespace GoldbachBoundaries.ResidueClass

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

omit [NeZero q] in
theorem primitiveCharacter_ne_one (hχ : χ ≠ 1) : χ.primitiveCharacter ≠ 1 := by
  intro h
  apply hχ
  exact χ.changeLevel_primitiveCharacter.symm.trans
    ((congrArg (DirichletCharacter.changeLevel χ.conductor_dvd_level) h).trans
      (DirichletCharacter.changeLevel_one _))

theorem analyticOnNhd_lFunction :
    AnalyticOnNhd ℂ χ.LFunction ({1}ᶜ : Set ℂ) := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_compl_singleton
  exact fun z hz ↦ (χ.differentiableAt_LFunction z (.inl hz)).differentiableWithinAt

theorem analyticOnNhd_primitiveL :
    AnalyticOnNhd ℂ (primitiveL χ) ({1}ᶜ : Set ℂ) := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  exact analyticOnNhd_lFunction χ.primitiveCharacter

theorem primitiveL_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) :
    primitiveL χ s ≠ 0 := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  rcases eq_or_ne χ 1 with rfl | hχ
  · rw [primitiveL_one]
    exact riemannZeta_ne_zero_of_one_le_re hs
  · exact χ.primitiveCharacter.LFunction_ne_zero_of_one_le_re
      (.inl (primitiveCharacter_ne_one χ hχ)) hs

theorem analyticOrderAt_primitiveL_ne_top {s : ℂ} (hs : s ≠ 1) :
    analyticOrderAt (primitiveL χ) s ≠ ⊤ := by
  have h2 : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by simp
  have hconn : IsPreconnected ({(1 : ℂ)}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected
  have ha := analyticOnNhd_primitiveL χ
  apply ha.analyticOrderAt_ne_top_of_isPreconnected hconn h2 hs
  rw [(ha _ h2).analyticOrderAt_eq_zero.mpr (primitiveL_ne_zero_of_one_le_re χ (by norm_num))]
  simp

theorem primitiveMult_pos_iff {s : ℂ} (hs : s ≠ 1) :
    0 < primitiveMult χ s ↔ primitiveL χ s = 0 := by
  unfold primitiveMult
  rw [← Nat.cast_pos (α := ℕ∞), Nat.cast_analyticOrderNatAt (analyticOrderAt_primitiveL_ne_top χ hs),
    pos_iff_ne_zero, (analyticOnNhd_primitiveL χ s hs).analyticOrderAt_ne_zero]

theorem primitiveZeros_one : primitiveZeros (1 : DirichletCharacter ℂ q) = NontrivialZeros := by
  simp [primitiveZeros, primitiveL_one, NontrivialZeros]

theorem primitiveMult_one {s : ℂ} (hs : s ≠ 1) :
    primitiveMult (1 : DirichletCharacter ℂ q) s = zetaMult s := by
  unfold primitiveMult analyticOrderNatAt
  rw [primitiveL_one, analyticOrderAt_riemannZeta_eq_zetaMult hs]
  simp

/-- The strip formulation of fixed-modulus GRH is equivalent to imposing the
critical-line condition on the L-functions at level `q`. -/
theorem grh_iff_level :
    GRH q ↔ ∀ χ : DirichletCharacter ℂ q, ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 →
      χ.LFunction ρ = 0 → ρ.re = 1 / 2 := by
  have hz (ρ : ℂ) (hρ : ρ.re < 1) : ρ ≠ 1 := by
    intro h
    simp [h] at hρ
  constructor
  · intro h χ ρ h₀ h₁ hzero
    exact h χ ρ ⟨(lFunction_zero_iff_primitive_zero χ h₀ (hz ρ h₁)).mp hzero, h₀, h₁⟩
  · intro h χ ρ hρ
    exact h χ ρ hρ.2.1 hρ.2.2
      ((lFunction_zero_iff_primitive_zero χ hρ.2.1 (hz ρ hρ.2.2)).mpr hρ.1)

theorem hasResidue_negLogDeriv_primitiveL {s : ℂ} (hs : s ≠ 1) :
    HasResidue (fun z ↦ -logDeriv (primitiveL χ) z) s (-(primitiveMult χ s : ℂ)) :=
  (hasResidue_logDeriv_of_analyticOrderAt (analyticOnNhd_primitiveL χ s hs)
    (Nat.cast_analyticOrderNatAt (analyticOrderAt_primitiveL_ne_top χ hs)).symm).neg

private theorem lFunction_one_eventuallyEq :
    (1 : DirichletCharacter ℂ q).LFunction =ᶠ[𝓝[≠] (1 : ℂ)]
      (fun z ↦ eulerProduct (1 : DirichletCharacter ℂ q) z * riemannZeta z) := by
  filter_upwards [self_mem_nhdsWithin] with z hz
  rw [lFunction_eq_primitive_mul _ (.inl (show z ≠ 1 from hz)), primitiveL_one, mul_comm]

theorem meromorphic_lFunction : Meromorphic χ.LFunction := by
  intro z
  by_cases h : z ≠ 1 ∨ χ ≠ 1
  · rcases h with hz | hχ
    · exact (analyticOnNhd_lFunction χ z hz).meromorphicAt
    · exact ((DirichletCharacter.differentiable_LFunction hχ).analyticAt z).meromorphicAt
  · push Not at h
    obtain ⟨rfl, rfl⟩ := h
    exact ((analyticAt_eulerProduct (1 : DirichletCharacter ℂ q) 1).meromorphicAt.fun_mul
      (meromorphicAt_riemannZeta 1)).congr lFunction_one_eventuallyEq.symm

theorem meromorphic_D : Meromorphic (D q) := by
  intro s
  unfold D
  exact (MeromorphicAt.const _ s).fun_mul
    (MeromorphicAt.fun_sum fun χ _ ↦ ((meromorphic_lFunction χ).logDeriv s).fun_neg)

private theorem hasResidue_negLogDeriv_lFunction {s : ℂ} (hs : 0 < s.re) (hs₁ : s ≠ 1) :
    HasResidue (fun z ↦ -logDeriv χ.LFunction z) s (-(primitiveMult χ s : ℂ)) := by
  have ha := analyticOnNhd_lFunction χ s hs₁
  have hord : analyticOrderAt χ.LFunction s ≠ ⊤ := by
    have h2 : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by simp
    have hconn : IsPreconnected ({(1 : ℂ)}ᶜ : Set ℂ) :=
      (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected
    apply (analyticOnNhd_lFunction χ).analyticOrderAt_ne_top_of_isPreconnected hconn h2 hs₁
    rw [(analyticOnNhd_lFunction χ _ h2).analyticOrderAt_eq_zero.mpr
      (χ.LFunction_ne_zero_of_one_le_re (.inr (by norm_num)) (by norm_num))]
    simp
  have heq := Nat.cast_analyticOrderNatAt hord
  rw [analyticOrderNatAt_lFunction_eq_primitiveMult χ hs hs₁] at heq
  exact (hasResidue_logDeriv_of_analyticOrderAt ha heq.symm).neg

private theorem hasResidue_negLogDeriv_lFunction_one :
    HasResidue (fun z ↦ -logDeriv χ.LFunction z) 1 (if χ = 1 then 1 else 0) := by
  classical
  by_cases hχ : χ = 1
  · subst χ
    simp only [ite_true]
    have hord :
        meromorphicOrderAt (1 : DirichletCharacter ℂ q).LFunction 1 = (-1 : WithTop ℤ) := by
      rw [meromorphicOrderAt_congr lFunction_one_eventuallyEq, ← Pi.mul_def,
        meromorphicOrderAt_mul_of_ne_zero (analyticAt_eulerProduct _ _)
          (eulerProduct_ne_zero _ (by norm_num)), meromorphicOrderAt_riemannZeta_one]
      rfl
    simpa using (hasResidue_logDeriv_of_meromorphicOrderAt
      (meromorphic_lFunction (1 : DirichletCharacter ℂ q) 1)
      (n := -1) (by simpa using hord)).neg
  · rw [ite_eq_right hχ]
    have ha := (DirichletCharacter.differentiable_LFunction hχ).analyticAt (1 : ℂ)
    exact hasResidue_zero_of_analyticAt
      (ha.deriv.div ha (DirichletCharacter.LFunction_apply_one_ne_zero hχ)).neg

/-- Off one and the inducing zeros, the average is holomorphic in the positive half-plane. -/
theorem analyticAt_D {s : ℂ} (hs : 0 < s.re) (hs₁ : s ≠ 1)
    (hne : ∀ χ : DirichletCharacter ℂ q, primitiveL χ s ≠ 0) :
    AnalyticAt ℂ (D q) s := by
  unfold D
  apply AnalyticAt.mul analyticAt_const
  apply Finset.analyticAt_fun_sum
  intro χ _
  have ha := analyticOnNhd_lFunction χ s hs₁
  exact (ha.deriv.div ha (fun h ↦ hne χ ((lFunction_zero_iff_primitive_zero χ hs hs₁).mp h))).neg

/-- Each character is counted with its own multiplicity at the point. -/
def totalMult (q : ℕ) [NeZero q] (s : ℂ) : ℕ :=
  ∑ χ : DirichletCharacter ℂ q, primitiveMult χ s

private theorem hasResidue_D_of_character_residues {s : ℂ} {c : DirichletCharacter ℂ q → ℂ}
    (h : ∀ χ : DirichletCharacter ℂ q, HasResidue (fun z ↦ -logDeriv χ.LFunction z) s (c χ)) :
    HasResidue (D q) s ((q.totient : ℂ)⁻¹ * ∑ χ, c χ) := by
  have hsum : HasResidue (fun z ↦ ∑ χ : DirichletCharacter ℂ q, -logDeriv χ.LFunction z)
      s (∑ χ, c χ) := by
    simp only [HasResidue, Finset.mul_sum]
    exact tendsto_finsetSum _ (fun χ _ ↦ h χ)
  exact hsum.const_mul _

/-- The principal term contributes residue `1 / φ(q)` at one. -/
theorem hasResidue_D_one : HasResidue (D q) 1 (q.totient : ℂ)⁻¹ := by
  classical
  simpa using hasResidue_D_of_character_residues (fun χ ↦
    hasResidue_negLogDeriv_lFunction_one χ)

/-- At positive real part away from one, the residue of the character average
is minus the total zero multiplicity divided by the totient. -/
theorem hasResidue_D {s : ℂ} (hs : 0 < s.re) (hs₁ : s ≠ 1) :
    HasResidue (D q) s (-(q.totient : ℂ)⁻¹ * (totalMult q s : ℂ)) := by
  simpa [totalMult, Nat.cast_sum, Finset.sum_neg_distrib] using
    hasResidue_D_of_character_residues (fun χ ↦ hasResidue_negLogDeriv_lFunction χ hs hs₁)

theorem meromorphicOrderAt_D_one :
    meromorphicOrderAt (D q) 1 = ((-1 : ℤ) : WithTop ℤ) := by
  apply HasResidue.meromorphicOrderAt_eq_neg_one (meromorphic_D 1) hasResidue_D_one
  exact inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (NeZero.pos q)).ne')

theorem meromorphicOrderAt_D_of_pos_mult {s : ℂ} (hs : 0 < s.re) (hs₁ : s ≠ 1)
    (hm : 0 < totalMult q s) : meromorphicOrderAt (D q) s = ((-1 : ℤ) : WithTop ℤ) := by
  apply HasResidue.meromorphicOrderAt_eq_neg_one (meromorphic_D s) (hasResidue_D hs hs₁)
  exact mul_ne_zero (neg_ne_zero.mpr
    (inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (NeZero.pos q)).ne')))
    (Nat.cast_ne_zero.mpr hm.ne')

/-- The point of the critical line of ordinate `t`. -/
def criticalPoint (t : ℝ) : ℂ := 1 / 2 + (t : ℂ) * I

/-- Multiplicities summed over characters at the indicated critical-line ordinate. -/
def ordinateWeight (q : ℕ) [NeZero q] (t : ℝ) : ℕ :=
  totalMult q (criticalPoint t)

/-- The distinct ordinates that occur in at least one inducing L-function. -/
def Ordinates (q : ℕ) [NeZero q] : Set ℝ := {t | 0 < ordinateWeight q t}

theorem totalMult_pos_iff {s : ℂ} (hs : s ≠ 1) :
    0 < totalMult q s ↔ ∃ χ : DirichletCharacter ℂ q, primitiveL χ s = 0 := by
  classical
  simp only [totalMult, Finset.sum_pos_iff, Finset.mem_univ, true_and, primitiveMult_pos_iff _ hs]

theorem criticalPoint_re (t : ℝ) : (criticalPoint t).re = 1 / 2 := by
  simp [criticalPoint]

theorem criticalPoint_im (t : ℝ) : (criticalPoint t).im = t := by
  simp [criticalPoint]

theorem mem_Ordinates_iff {t : ℝ} :
    t ∈ Ordinates q ↔ ∃ χ : DirichletCharacter ℂ q, criticalPoint t ∈ primitiveZeros χ := by
  have hne : criticalPoint t ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    norm_num [criticalPoint_re] at this
  rw [Ordinates, mem_ofPred_eq, ordinateWeight, totalMult_pos_iff hne]
  norm_num [primitiveZeros, criticalPoint_re]

theorem mem_Ordinates_of_zetaZero {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros)
    (hre : ρ.re = 1 / 2) : ρ.im ∈ Ordinates q := by
  have heq : criticalPoint ρ.im = ρ :=
    Complex.ext (by rw [criticalPoint_re, hre]) (criticalPoint_im _)
  rw [mem_Ordinates_iff]
  exact ⟨1, by rwa [heq, primitiveZeros_one]⟩

end GoldbachBoundaries.ResidueClass
