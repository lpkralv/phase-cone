import GoldbachBoundaries.Paper2.M5.Fill.T2Common

/-!
# Fill: `TkLine_eq_of_no_pole`

`T2.shift` (M1's `verticalIntegral'_eq_add_sum_of_simplePoles` with tails and integrability discharged) with `S = ∅`.
On the closed strip `c ≤ Re w ≤ c'` the integrand is holomorphic: `w ≠ m` by `h1`, `s - w ≠ 1` by `h2`, and
`Re(s - w) ≥ σ - c' > 1/2`.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2

theorem TkLine_eq_of_no_pole (hRH : RiemannHypothesis) {m : ℕ} (hm : 1 ≤ m) {F H : ℂ → ℂ} (hP : TkPack m F H) {s : ℂ}
    {c c' : ℝ} (hc : (m : ℝ) - 1 / 2 < c) (hcc' : c ≤ c') (hc' : c' + 1 / 2 < s.re)
    (h1 : ¬ (c ≤ m ∧ (m : ℝ) ≤ c')) (h2 : ¬ (c ≤ s.re - 1 ∧ s.re - 1 ≤ c')) :
    TkLine F c' s = TkLine F c s := by
  have hf : DifferentiableOn ℂ (fun w => KerS s w * F w * Qcont (s - w))
      (Icc c c' ×ℂ univ \ ((∅ : Finset ℂ) : Set ℂ)) := by
    intro w hw
    obtain ⟨⟨hw1, hw2⟩, -⟩ := Complex.mem_reProdIm.mp hw.1
    refine (T2.differentiableAt_integrand_slice hRH hm hP (by linarith) ?_ (by simp; linarith)
      ?_).differentiableWithinAt
    · rintro rfl; simp at hw1 hw2; exact h1 ⟨hw1, hw2⟩
    · intro h
      have := congrArg Complex.re h
      simp at this
      exact h2 ⟨by linarith, by linarith⟩
  have := T2.shift hRH hm hP hc hcc' hc' (fun h => h1 ⟨h.le, by rw [← h]; exact hcc'⟩)
    (fun h => h1 ⟨by rw [← h]; exact hcc', h.ge⟩)
    (fun h => h2 ⟨by linarith, by linarith⟩) (fun h => h2 ⟨by linarith, by linarith⟩)
    ∅ (fun _ => 0) (by simp) hf (by simp)
  simpa using this

end GoldbachBoundaries.Paper2.M5
