import GoldbachBoundaries.Paper2.M5.FilterIII
import GoldbachBoundaries.Paper2.M5.Fill.Lambda0_eq_limit

/-!
# M5: Theorem F (iv) (`cl:thm:filter`(iv)): `η T₀(1 + η) → Λ₀ > 0` under RH alone

`T₀ = D_{H₀}` (`eqOn_DH_H0f_of_T0`), and Step 3 of (ii) at `τ₀ = 0` (no ordinate is `0`) gives the limit
`midLim H₀ 0 + ∑ limTerm H₀ 0` (`tendsto_eta_Fil`). That number is `Λ₀` (`Lambda0_eq_limit`): the middle term is
`R_{1/2} K_1(1/2) H₀(1/2, 1/2) R_{1/2} = (-1/2)·π·(1/4)·(-1/2) = π/16`, and for each zero `1 - ρ = ρ̄` (RH) is a zero of the
same multiplicity ((Z1)), so `limTerm ρ = m(ρ)²|Γ(ρ)|²|ρ - 1|²`, and the zeros come in conjugate pairs. Then no holomorphic
`g` on a disc about `1` agrees with `T₀` on the right half (it would make `η T₀(1 + η) → 0`), and a meromorphic one has a
simple pole with residue `Λ₀` (`order_residue_of_codiscrete_line`, `Λ₀ > 0`).
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-! ## Lemmas

Proved in `Fill/`, one file per lemma (same name, same statement): `Lambda0_eq_limit`. -/

/-! ## Real lemmas -/

/-- If `η F(1 + η) → c ≠ 0`, no `g` holomorphic on a disc about `1` agrees with `F` on the right half-disc: `g` is
continuous at `1`, so `η g(1 + η) → 0`, and the two functions agree for small `η > 0`. -/
lemma not_exists_holomorphic_of_tendsto {F : ℂ → ℂ} {c : ℂ} (hc : c ≠ 0)
    (hlim : Tendsto (fun η : ℝ => (η : ℂ) * F (1 + η)) (𝓝[>] 0) (𝓝 c)) {r : ℝ} (hr : 0 < r) :
    ¬ ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball 1 r) ∧ EqOn g F (ball 1 r ∩ HH) := by
  rintro ⟨g, hg, hgF⟩
  have hcont : ContinuousAt g 1 := (hg.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hr))).continuousAt
  have hpath : Tendsto (fun η : ℝ => (1 : ℂ) + η) (𝓝[>] 0) (𝓝 1) := by
    have : Tendsto (fun η : ℝ => (1 : ℂ) + η) (𝓝 0) (𝓝 (1 + ((0 : ℝ) : ℂ))) :=
      (continuous_const.add Complex.continuous_ofReal).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  have hη : Tendsto (fun η : ℝ => (η : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun η : ℝ => (η : ℂ)) (𝓝 0) (𝓝 ((0 : ℝ) : ℂ)) := Complex.continuous_ofReal.tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  have hg0 : Tendsto (fun η : ℝ => (η : ℂ) * g (1 + η)) (𝓝[>] 0) (𝓝 0) := by
    simpa using hη.mul ((hcont.tendsto).comp hpath)
  have hev : (fun η : ℝ => (η : ℂ) * g (1 + η)) =ᶠ[𝓝[>] 0] fun η : ℝ => (η : ℂ) * F (1 + η) := by
    have hball : ∀ᶠ η : ℝ in 𝓝[>] 0, (1 : ℂ) + η ∈ ball 1 r := hpath (isOpen_ball.mem_nhds (mem_ball_self hr))
    filter_upwards [hball, self_mem_nhdsWithin] with η hb hpos
    have hpos' : (0 : ℝ) < η := hpos
    have hH : (1 : ℂ) + η ∈ HH := by
      show (1 : ℝ) < ((1 : ℂ) + η).re
      simp only [add_re, one_re, ofReal_re]
      linarith
    rw [hgF ⟨hb, hH⟩]
  exact hc (tendsto_nhds_unique (hg0.congr' hev) hlim).symm

/-! ## Target -/

/-- `thm_filter_iv` of `Paper2/Statements.lean`, statement verbatim. -/
theorem thm_filter_iv_proof (hRH : RiemannHypothesis) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6) :
    Summable lambda0Term ∧
    ∀ F : ℂ → ℂ, DifferentiableOn ℂ F HH → EqOn F T0 (halfPlane 2) →
      Tendsto (fun η : ℝ => (η : ℂ) * F (1 + η)) (𝓝[>] 0) (𝓝 (Lambda0 : ℂ)) ∧
      (∀ r : ℝ, 0 < r → ¬ ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball 1 r) ∧ EqOn g F (ball 1 r ∩ HH)) ∧
      ∀ r : ℝ, 0 < r → ∀ f : ℂ → ℂ, MeromorphicOn f (ball 1 r) →
        f =ᶠ[codiscreteWithin (ball 1 r ∩ HH)] F →
        meromorphicOrderAt f 1 = -1 ∧ HasResidue f 1 (Lambda0 : ℂ) := by
  obtain ⟨_, hHs, hH1⟩ := H0f_conditions
  have hτ : ∀ ρ ∈ NontrivialZeros, ρ.im ≠ (0 : ℝ) := fun ρ hρ => im_ne_zero_of_mem_nontrivialZeros hρ
  obtain ⟨hsum, hlim⟩ := tendsto_eta_Fil hRH hZ1 hZ2 hZ3 H0f hHs hH1 hτ
  obtain ⟨hL0s, hL0⟩ := Lambda0_eq_limit hRH hZ1 hsum
  rw [hL0] at hlim
  have hΛ : (Lambda0 : ℂ) ≠ 0 := by exact_mod_cast Lambda0_pos'.ne'
  refine ⟨hL0s, fun F hF hFT => ?_⟩
  have hEq := eqOn_Fil_of_DH hRH H0f hHs hH1 hF (eqOn_DH_H0f_of_T0 hRH hZ1 hZ2 hZ3 hZ6 hF hFT)
  have hlimF : Tendsto (fun η : ℝ => (η : ℂ) * F (1 + η)) (𝓝[>] 0) (𝓝 (Lambda0 : ℂ)) := by
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with η hη
    have hη' : (0 : ℝ) < η := hη
    have hmem : (1 + η : ℂ) ∈ HH := by
      show (1 : ℝ) < ((1 : ℂ) + η).re
      simp only [add_re, one_re, ofReal_re]
      linarith
    simp only [ofReal_zero, zero_mul, add_zero]
    rw [hEq hmem]
  refine ⟨hlimF, fun r hr => not_exists_holomorphic_of_tendsto hΛ hlimF hr, fun r hr f hf hfF => ?_⟩
  exact order_residue_of_codiscrete_line hF (by simp) hr hf hfF hΛ hlimF

end GoldbachBoundaries.Paper2.M5
