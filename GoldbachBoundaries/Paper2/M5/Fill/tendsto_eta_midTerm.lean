import GoldbachBoundaries.Paper2.M5.Fill.F3Common

/-!
# Fill, group F3: `tendsto_eta_midTerm`

`η midTerm(s₀ + η) = f(η) · η Qcont(1/2 + iτ₀ + η)` with `f(η) = R_{1/2} K_s(1/2) H(1/2, s - 1/2)` continuous at `0`
(`Re s₀ = 1`, `Re(s₀ - 1/2) = 1/2`). If `τ₀ = 0`, `1/2 ∈ Σ_Q` and the second factor tends to `R_{1/2}`; otherwise
`1/2 + iτ₀ ∉ Σ_Q` (`poleSetQ_re_cases`, `hτ`) and it tends to `0`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

theorem tendsto_eta_midTerm (hRH : RiemannHypothesis) (H : MvPolynomial (Fin 2) ℂ) {τ₀ : ℝ}
    (hτ : ∀ ρ ∈ NontrivialZeros, ρ.im ≠ τ₀) :
    Tendsto (fun η : ℝ => (η : ℂ) * midTerm H (1 + τ₀ * I + η)) (𝓝[>] 0) (𝓝 (midLim H τ₀)) := by
  set s₀ : ℂ := 1 + τ₀ * I with hs₀
  set w : ℂ := 1 / 2 + τ₀ * I with hw
  set g : ℂ → ℂ := fun s => Rcoef (1 / 2) * KerS s (1 / 2) * evalH H (1 / 2) (s - 1 / 2) with hg
  have hs₀re : s₀.re = 1 := by simp [hs₀]
  have hwre : w.re = 1 / 2 := by simp [hw]
  have hgc : ContinuousAt g s₀ := by
    have hK : ContinuousAt (fun s => KerS s (1 / 2)) s₀ :=
      (F3_differentiableAt_KerS (by rw [hs₀re]; norm_num)
        (by simp [hs₀]; norm_num)).continuousAt
    have hP : Continuous (fun s : ℂ => evalH H (1 / 2) (s - 1 / 2)) :=
      F3_continuous_evalH H continuous_const (continuous_id.sub continuous_const)
    exact (continuousAt_const.mul hK).mul hP.continuousAt
  have hrw : ∀ η : ℝ, (η : ℂ) * midTerm H (s₀ + η) = g (s₀ + η) * ((η : ℂ) * Qcont (w + η)) := by
    intro η
    have : (s₀ + η - 1 / 2 : ℂ) = w + η := by rw [hw, hs₀]; ring
    simp only [midTerm, hg]
    rw [this]
    ring
  simp_rw [hrw]
  by_cases h0 : τ₀ = 0
  · have hmem : w ∈ PoleSetQ := by
      refine Or.inl (Or.inr ⟨2, le_refl 2, Nat.squarefree_two, ?_⟩)
      simp [hw, h0]
    have hlim := (F3_tendsto_comp_shift hgc).mul (F3_tendsto_eta_Qcont_pole hmem)
    convert hlim using 2
    simp only [midLim, h0, ite_true, hg, hs₀, hw]
    norm_num
  · have hnot : w ∉ PoleSetQ := by
      refine F3_not_mem_poleSetQ hRH hwre ?_ ?_
      · intro h
        have := congrArg Complex.im h
        simp [hw] at this
        exact h0 this
      · intro hz
        exact hτ w hz (by simp [hw])
    have hlim := (F3_tendsto_comp_shift hgc).mul (F3_tendsto_eta_Qcont_reg (by rw [hwre]; norm_num) hnot)
    convert hlim using 2
    simp [midLim, h0]

end GoldbachBoundaries.Paper2.M5
