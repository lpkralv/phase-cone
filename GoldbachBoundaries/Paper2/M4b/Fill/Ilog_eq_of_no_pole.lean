import GoldbachBoundaries.Paper2.M4b.Fill.BShiftCommon

/-!
# Fill: `Ilog_eq_of_no_pole`

`Ilog_shift` (M1's multi-pole shift with tails and integrability discharged) with `S = ∅`: on the closed strip
`c ≤ Re z ≤ c'` neither `z = 1` (`h1`) nor `z = L(s) - 1` (`h2`) occurs, and `1/2 < Re z`, `1/2 < Re(L(s) - z)`, so
the integrand is holomorphic there (`differentiableAt_integrand`).
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M4b

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **A line move with no pole in between** (RH, (K1), (K2); Step 1, "the value does not depend on `c`"). The only
poles of the integrand in `1/2 < Re z < Re L(s) - 1/2` are `z = 1` and `z = L(s) - 1` (`differentiableAt_integrand`);
`h1`, `h2` keep both off the closed strip `[c, c']`. M1's `verticalIntegral'_eq_add_sum_of_simplePoles` with
`S = ∅`: holomorphy on the strip (`differentiableAt_integrand`), the horizontal integrals tend to `0`
(`norm_integrand_le_far` with `K = {s}`, `[c₁, c₂] = [c, c']`: `|∫_c^{c'} f(x + iy) dx| ≤ (c' - c)M(1+|y|)^{-3/2}`), and
integrability on both lines (`differentiableOn_Ilog`; `c ≠ 1 ≠ c'` and `Re L(s) - c ≠ 1 ≠ Re L(s) - c'` follow from
`h1`, `h2`). Size: 100–200 lines. -/
theorem Ilog_eq_of_no_pole (hRH : RiemannHypothesis) (A : Aff) (k : ℂ → ℂ → ℂ) (hK1 : K1 A k)
    (hK2 : K2 A k) {s : ℂ} (hs : s ∈ A.DL) {c c' : ℝ} (hc : 1 / 2 < c) (hcc' : c ≤ c')
    (hc' : c' + 1 / 2 < (A.app s).re) (h1 : ¬ (c ≤ 1 ∧ 1 ≤ c'))
    (h2 : ¬ (c ≤ (A.app s).re - 1 ∧ (A.app s).re - 1 ≤ c')) :
    Ilog A k c' s = Ilog A k c s := by
  have hc1 : c ≠ 1 := fun h => h1 ⟨h.le, h ▸ hcc'⟩
  have hc'1 : c' ≠ 1 := fun h => h1 ⟨h ▸ hcc', h.ge⟩
  have hcL : (A.app s).re - c ≠ 1 := fun h => h2 ⟨by linarith, by linarith⟩
  have hc'L : (A.app s).re - c' ≠ 1 := fun h => h2 ⟨by linarith, by linarith⟩
  have hf : DifferentiableOn ℂ (fun z => k z s * Qcont z * Qcont (A.app s - z))
      (Icc c c' ×ℂ univ \ ((∅ : Finset ℂ) : Set ℂ)) := by
    intro z hz
    obtain ⟨⟨hz1, hz2⟩, -⟩ := Complex.mem_reProdIm.mp hz.1
    refine (differentiableAt_integrand_slice hRH A k hK1 hs (by linarith) (by simp; linarith)
      ?_ ?_).differentiableWithinAt
    · rintro rfl; exact h1 ⟨by simpa using hz1, by simpa using hz2⟩
    · intro h
      have := congrArg Complex.re h
      simp at this
      exact h2 ⟨by linarith, by linarith⟩
  have := Ilog_shift hRH A k hK1 hK2 hs hc hcc' hc' hc1 hc'1 hcL hc'L ∅ (fun _ => 0)
    (by simp) hf (by simp)
  simpa using this

end GoldbachBoundaries.Paper2.M4b
