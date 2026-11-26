import GoldbachBoundaries.Paper2.M5.Fill.F3Common

/-!
# Fill, group F3: `CH_eq_tsum_limTerm`

Under RH `R_ρ = -m(ρ)` at a zero (M4a's `Rcoef_div_of_RH`, `n = 1`), so for `ρ' = s₀ - ρ` a zero,
`limTerm ρ = m(ρ)m(ρ')Γ(ρ)Γ(ρ')/Γ(s₀) H(ρ, ρ')`, the summand of `C_H(τ₀)` at `(ρ, ρ')`. The map `(ρ, ρ') ↦ ρ` from the
index type of `CHterm` to the zeros is injective (`ρ' = s₀ - ρ`), and `limTerm` vanishes off its range
(`Function.Injective.tsum_eq`, `Function.Injective.summable_iff`).
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

theorem CH_eq_tsum_limTerm (hRH : RiemannHypothesis) (hZ1 : Z1) (H : MvPolynomial (Fin 2) ℂ) {τ₀ : ℝ}
    (hsum : Summable (fun ρ : NontrivialZeros => limTerm H τ₀ ρ)) :
    Summable (CHterm H τ₀) ∧ CH H τ₀ = ∑' ρ : NontrivialZeros, limTerm H τ₀ ρ := by
  have _ := hZ1
  set e : {p : ℂ × ℂ // p.1 ∈ NontrivialZeros ∧ p.2 ∈ NontrivialZeros ∧ p.1 + p.2 = 1 + τ₀ * I} →
      NontrivialZeros := fun p => ⟨p.1.1, p.2.1⟩ with he
  have hinj : Function.Injective e := by
    rintro ⟨⟨a, b⟩, ha⟩ ⟨⟨a', b'⟩, ha'⟩ h
    simp only [he, Subtype.mk.injEq] at h
    subst h
    have : b = b' := by linear_combination ha.2.2 - ha'.2.2
    subst this
    rfl
  have hvan : ∀ ρ : NontrivialZeros, ρ ∉ Set.range e → limTerm H τ₀ ρ = 0 := by
    intro ρ hρ
    unfold limTerm
    split_ifs with hz
    · exact absurd ⟨⟨((ρ : ℂ), 1 + τ₀ * I - ρ), ρ.2, hz, by ring⟩, rfl⟩ hρ
    · rfl
  have hcomp : ∀ p, limTerm H τ₀ (e p) = CHterm H τ₀ p := by
    rintro ⟨⟨a, b⟩, ha, hb, hab⟩
    have hb' : 1 + τ₀ * I - a = b := by rw [← hab]; ring
    simp only [he, limTerm, CHterm]
    have hbz : 1 + τ₀ * I - a ∈ NontrivialZeros := by rw [hb']; exact hb
    simp only [hbz, ite_true]
    rw [hb', F3_Rcoef_zero hRH ha, F3_Rcoef_zero hRH hb, KerS]
    rw [← hb'] at *
    ring_nf
  have hfun : (fun p => limTerm H τ₀ (e p)) = CHterm H τ₀ := funext hcomp
  refine ⟨?_, ?_⟩
  · rw [← hfun]
    exact (hinj.summable_iff hvan).mpr hsum
  · unfold CH
    rw [← hfun]
    exact hinj.tsum_eq (fun ρ hρ => by
      by_contra h
      exact hρ (hvan ρ h))

end GoldbachBoundaries.Paper2.M5
