import GoldbachBoundaries.Paper2.M4a.Fill.ECommon

/-!
# M4a filler E: `analyticOnNhd_lineCoeff`

On the open ball, `iteratedDeriv j (u(·, s))` at `w` equals `(∂_z)^j u (w, s)` (`FillE.iteratedDeriv_slice`), and
`(∂_z)^j u` is analytic on the ball (`FillE.analyticOnNhd_iterate_pz`). Compose with `s ↦ (c₀ + c₁s, s)`.
-/

noncomputable section

open Complex Filter Topology Set Metric

namespace GoldbachBoundaries.Paper2.M4a

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **The transverse Taylor coefficients are holomorphic along the line** (general). For `s` with
`(c₀ + c₁s, s) ∈ ball p r`, `lineCoeff u c₀ c₁ j s = iteratedFDeriv ℂ j u (c₀ + c₁s, s) (fun _ => (1, 0))`: the slice
`z ↦ u(z, s)` is `u ∘ (z ↦ (z, 0) + (0, s))`, and the iterated derivative of a smooth function composed with an affine
map whose linear part is `ContinuousLinearMap.inl` (`ContinuousLinearMap.iteratedFDeriv_comp_right`, plus translation
invariance `iteratedFDeriv_comp_add_right`; `iteratedDeriv_eq_iteratedFDeriv`). `iteratedFDeriv ℂ j u` is analytic on
the ball (`AnalyticOnNhd.iteratedFDeriv`), evaluation at the fixed vectors is a continuous multilinear map, and
`s ↦ (c₀ + c₁s, s)` is affine; compose. (Alternatively: Cauchy's integral formula for the `j`-th derivative on a
small circle in `z`, holomorphic in `s` as a parametric integral.) Size: 100–200 lines. -/
theorem analyticOnNhd_lineCoeff {u : ℂ × ℂ → ℂ} {p : ℂ × ℂ} {r : ℝ} (hu : AnalyticOnNhd ℂ u (ball p r))
    (c₀ c₁ : ℂ) (j : ℕ) :
    AnalyticOnNhd ℂ (lineCoeff u c₀ c₁ j) {s | (c₀ + c₁ * s, s) ∈ ball p r} := by
  have hc : Continuous fun s : ℂ => (c₀ + c₁ * s, s) := by fun_prop
  have hS : IsOpen {s : ℂ | (c₀ + c₁ * s, s) ∈ ball p r} := isOpen_ball.preimage hc
  intro s hs
  have hA : AnalyticAt ℂ (fun t : ℂ => (FillE.pz^[j] u) (c₀ + c₁ * t, t)) s := by
    have h1 : AnalyticAt ℂ (fun t : ℂ => (c₀ + c₁ * t, t)) s := by fun_prop
    exact (FillE.analyticOnNhd_iterate_pz hu j _ hs).comp_of_eq
      (f := fun t : ℂ => (c₀ + c₁ * t, t)) h1 rfl
  refine hA.congr ?_
  filter_upwards [hS.mem_nhds hs] with t ht
  exact (FillE.iteratedDeriv_slice isOpen_ball j u hu _ _ ht).symm

end GoldbachBoundaries.Paper2.M4a
