import GoldbachBoundaries.Paper2.M5.FilterI
import GoldbachBoundaries.Paper2.M5.Fill.F1Common

/-!
# Filler F1: `eqOn_DH_H0f_of_T0` (statement verbatim from `Paper2/M5/FilterII.lean`)

M4b's `prop_T0_proof` gives (R) for `k₀`, `W₀^log`, `Q` and `L = id`: on `2 < σ < 3` (`R_L ∩ D_L`) and the line
`c = σ/2 ∈ (1, σ - 1)`, `T₀(s)` is the line integral of `k₀(z, s)Q(z)Q(s - z)`, which is `DH H0f s` (`kH_H0f`). So
`F = DH H0f = Fil H0f` on `2 < σ < 3` (`F1_Fil_eq_DH_H0f`), hence `F = Fil H0f` on `ℍ` (`eqOn_HH_of_eqOn_open`,
`F1_differentiableOn_Fil`), and `F = DH H0f` on `σ > 2`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

theorem eqOn_DH_H0f_of_T0 (hRH : RiemannHypothesis) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F HH) (hFT : EqOn F T0 (halfPlane 2)) : EqOn F (DH H0f) (halfPlane 2) := by
  obtain ⟨-, -, -, -, hR, -⟩ := M4b.prop_T0_proof hRH hZ1 hZ2 hZ3 hZ6
  have happ : ∀ s : ℂ, Aff.idL.app s = s := fun s => by simp [Aff.app, Aff.idL]
  set V : Set ℂ := {s | 2 < s.re ∧ s.re < 3} with hVdef
  have hVo : IsOpen V := (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)
  have hV : EqOn F (Fil H0f) V := by
    rintro s ⟨h2, h3⟩
    have hRL : s ∈ Aff.idL.RL ∩ Aff.idL.DL := by
      show 2 < (Aff.idL.app s).re ∧ 1 < (Aff.idL.app s).re ∧ (Aff.idL.app s).re < 3
      rw [happ]
      exact ⟨h2, by linarith, h3⟩
    have hint := hR.2.2.2 s hRL (s.re / 2) (by linarith) (by rw [happ]; linarith)
    have hs2 : s ∈ halfPlane 2 := h2
    rw [hFT hs2, T0, hint, F1_Fil_eq_DH_H0f hs2, DH, kH_H0f, happ]
  have hEq : EqOn F (Fil H0f) HH :=
    eqOn_HH_of_eqOn_open hF (F1_differentiableOn_Fil hRH H0f) hVo ⟨5 / 2, by
      show 2 < (5 / 2 : ℂ).re ∧ (5 / 2 : ℂ).re < 3
      norm_num⟩ (fun s hs => by
        show (1 : ℝ) < s.re
        linarith [hs.1]) hV
  intro s hs
  have hs' : (2 : ℝ) < s.re := hs
  rw [hEq (show (1 : ℝ) < s.re by linarith), F1_Fil_eq_DH_H0f hs]

end GoldbachBoundaries.Paper2.M5
