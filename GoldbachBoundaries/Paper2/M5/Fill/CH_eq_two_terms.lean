import GoldbachBoundaries.Paper2.M5.FilterII

/-!
# Filler F4: `CH_eq_two_terms`

Under RH and (F), the index type of `C_H(τ₀)` is `{(ρ₁, ρ₂), (ρ₂, ρ₁)}`: for a pair `(ρ, ρ')` with `ρ + ρ' = 1 + iτ₀`,
`γ + γ' = τ₀ = γ₁ + γ₂ ≠ 0`, so (F) gives `{γ, γ'} = {γ₁, γ₂}`, and under RH a zero is `1/2 + iγ`. The two terms agree by
the symmetry of `H`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- Under RH two zeros with the same ordinate are equal. -/
lemma F4_eq_of_im_eq (hRH : RiemannHypothesis) {ρ ρ' : ℂ} (hρ : ρ ∈ NontrivialZeros)
    (hρ' : ρ' ∈ NontrivialZeros) (h : ρ.im = ρ'.im) : ρ = ρ' :=
  Complex.ext (by rw [sigmaFinite_re_eq_half hRH hρ, sigmaFinite_re_eq_half hRH hρ']) h

theorem CH_eq_two_terms (hRH : RiemannHypothesis) (hF : HypF) (H : MvPolynomial (Fin 2) ℂ)
    (hHs : ∀ z w, evalH H z w = evalH H w z) {τ₀ : ℝ} (hτ₀ : τ₀ ≠ 0) {ρ₁ ρ₂ : ℂ}
    (h₁ : ρ₁ ∈ NontrivialZeros) (h₂ : ρ₂ ∈ NontrivialZeros) (hsum : ρ₁ + ρ₂ = 1 + τ₀ * I) (hne : ρ₁ ≠ ρ₂) :
    CH H τ₀ = 2 * ((zetaMult ρ₁ : ℂ) * (zetaMult ρ₂ : ℂ) * (Gamma ρ₁ * Gamma ρ₂ / Gamma (1 + τ₀ * I)) *
      evalH H ρ₁ ρ₂) := by
  classical
  set S := {p : ℂ × ℂ // p.1 ∈ NontrivialZeros ∧ p.2 ∈ NontrivialZeros ∧ p.1 + p.2 = 1 + τ₀ * I}
  have hsum' : ρ₂ + ρ₁ = 1 + τ₀ * I := by rw [add_comm]; exact hsum
  let a : S := ⟨(ρ₁, ρ₂), h₁, h₂, hsum⟩
  let b : S := ⟨(ρ₂, ρ₁), h₂, h₁, hsum'⟩
  have him : ∀ {x y : ℂ}, x + y = 1 + τ₀ * I → x.im + y.im = τ₀ := by
    intro x y hxy
    have := congrArg Complex.im hxy
    simpa using this
  have hab : a ≠ b := by
    intro h
    have := congrArg (fun p : S => p.1.1) h
    exact hne this
  have hall : ∀ p : S, p = a ∨ p = b := by
    rintro ⟨⟨x, y⟩, hx, hy, hxy⟩
    have hpair := hF x hx y hy ρ₁ h₁ ρ₂ h₂ (by rw [him hxy, him hsum]) (by rw [him hxy]; exact hτ₀)
    rcases Set.pair_eq_pair_iff.mp hpair with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · left
      have ex := F4_eq_of_im_eq hRH hx h₁ e1
      have ey := F4_eq_of_im_eq hRH hy h₂ e2
      subst ex; subst ey; rfl
    · right
      have ex := F4_eq_of_im_eq hRH hx h₂ e1
      have ey := F4_eq_of_im_eq hRH hy h₁ e2
      subst ex; subst ey; rfl
  have hCH : CH H τ₀ = CHterm H τ₀ a + CHterm H τ₀ b := by
    unfold CH
    rw [tsum_eq_sum (s := {a, b}) (fun p hp => by
      exfalso; rcases hall p with h | h <;> simp [h] at hp)]
    exact Finset.sum_pair hab
  rw [hCH]
  simp only [CHterm, a, b]
  rw [hHs ρ₂ ρ₁]
  ring

end GoldbachBoundaries.Paper2.M5
