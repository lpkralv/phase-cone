import GoldbachBoundaries.Paper2.M5.Fill.F3Common

/-!
# Fill, group F3: `tendsto_eta_resTerm`

`w₀ = s₀ - ρ = 1/2 + i(τ₀ - γ)` (RH). `η resTerm(s₀ + η, ρ) = f(η) · η Qcont(w₀ + η)` with
`f(η) = R_ρ K_s(ρ) H(ρ, s - ρ)` continuous at `0` (`Re s₀ = 1`, `Re(s₀ - ρ) = 1/2`). If `w₀` is a zero, it lies in `Σ_Q`
and the second factor tends to `R_{w₀}`; otherwise `w₀ ∉ Σ_Q` (`w₀ ≠ 1/2` as `γ ≠ τ₀`) and it tends to `0`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

theorem tendsto_eta_resTerm (hRH : RiemannHypothesis) (H : MvPolynomial (Fin 2) ℂ) {τ₀ : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ NontrivialZeros) (hρτ : ρ.im ≠ τ₀) :
    Tendsto (fun η : ℝ => (η : ℂ) * resTerm H (1 + τ₀ * I + η) ρ) (𝓝[>] 0) (𝓝 (limTerm H τ₀ ρ)) := by
  set s₀ : ℂ := 1 + τ₀ * I with hs₀
  set w : ℂ := s₀ - ρ with hw
  set g : ℂ → ℂ := fun s => Rcoef ρ * KerS s ρ * evalH H ρ (s - ρ) with hg
  have hρre : ρ.re = 1 / 2 := F3_re_zero hRH hρ
  have hs₀re : s₀.re = 1 := by simp [hs₀]
  have hwre : w.re = 1 / 2 := by rw [hw, sub_re, hs₀re, hρre]; norm_num
  have hgc : ContinuousAt g s₀ := by
    have hK : ContinuousAt (fun s => KerS s ρ) s₀ :=
      (F3_differentiableAt_KerS (by rw [hs₀re]; norm_num) (by rw [← hw, hwre]; norm_num)).continuousAt
    have hP : Continuous (fun s : ℂ => evalH H ρ (s - ρ)) :=
      F3_continuous_evalH H continuous_const (continuous_id.sub continuous_const)
    exact (continuousAt_const.mul hK).mul hP.continuousAt
  have hrw : ∀ η : ℝ, (η : ℂ) * resTerm H (s₀ + η) ρ = g (s₀ + η) * ((η : ℂ) * Qcont (w + η)) := by
    intro η
    have : (s₀ + η - ρ : ℂ) = w + η := by rw [hw]; ring
    simp only [resTerm, hg]
    rw [this]
    ring
  simp_rw [hrw]
  by_cases hz : w ∈ NontrivialZeros
  · have hmem : w ∈ PoleSetQ := Or.inr ⟨1, le_refl 1, squarefree_one, w, hz, by simp⟩
    have hlim := (F3_tendsto_comp_shift hgc).mul (F3_tendsto_eta_Qcont_pole hmem)
    convert hlim using 2
    have hz' : 1 + τ₀ * I - ρ ∈ NontrivialZeros := hz
    simp only [limTerm, hz', ite_true, hg, hw, hs₀]
  · have hnot : w ∉ PoleSetQ := by
      refine F3_not_mem_poleSetQ hRH hwre ?_ hz
      intro h
      have := congrArg Complex.im h
      simp [hw, hs₀] at this
      exact hρτ (by linarith)
    have hlim := (F3_tendsto_comp_shift hgc).mul (F3_tendsto_eta_Qcont_reg (by rw [hwre]; norm_num) hnot)
    convert hlim using 2
    have hz' : 1 + τ₀ * I - ρ ∉ NontrivialZeros := hz
    simp [limTerm, hz']

end GoldbachBoundaries.Paper2.M5
