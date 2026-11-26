import GoldbachBoundaries.Paper2.M4a.Fill.ECommon

/-!
# M4a filler E: `analyticOnNhd_bracket`

For `s ∈ D_L` the points `(1, s)` and `(L(s) - 1, s)` lie in the open (K1) domain, where `k` is jointly
differentiable; compose with `s ↦ (1, s)` and `s ↦ (L(s) - 1, s)`, and use that `D_L` is open.
-/

noncomputable section

open Complex Filter Topology Set Metric

namespace GoldbachBoundaries.Paper2.M4a

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **The bracket is holomorphic on `D_L`** ((K1)). For `s ∈ D_L`, `(1, s)` and `(L(s) - 1, s)` lie in the open (K1)
domain (`0 < 1 < Re L(s)`, `0 < Re L(s) - 1 < Re L(s)`), where `k` is jointly differentiable; compose with the
affine maps `s ↦ (1, s)`, `s ↦ (L(s) - 1, s)`. `D_L` is open, so `DifferentiableOn.analyticOnNhd`. Size: 40–80 lines. -/
theorem analyticOnNhd_bracket (A : Aff) (k : ℂ → ℂ → ℂ) (hK1 : K1 A k) : AnalyticOnNhd ℂ (bracket A k) A.DL := by
  refine DifferentiableOn.analyticOnNhd (fun s hs => ?_) (isOpen_DL A)
  have h1 : DifferentiableAt ℂ (fun t => k 1 t) s := by
    have hd := FillE.differentiableAt_of_K1 hK1 hs (FillE.one_mem_Str hs).1 (FillE.one_mem_Str hs).2
    have hc : DifferentiableAt ℂ (fun t : ℂ => ((1 : ℂ), t)) s := by fun_prop
    exact DifferentiableAt.comp (g := fun p : ℂ × ℂ => k p.1 p.2) (f := fun t : ℂ => ((1 : ℂ), t)) s hd hc
  have h2 : DifferentiableAt ℂ (fun t => k (A.app t - 1) t) s := by
    have hd := FillE.differentiableAt_of_K1 hK1 hs (FillE.app_sub_one_mem_Str hs).1
      (FillE.app_sub_one_mem_Str hs).2
    have hc : DifferentiableAt ℂ (fun t : ℂ => (A.app t - 1, t)) s := by
      unfold Aff.app; fun_prop
    exact DifferentiableAt.comp (g := fun p : ℂ × ℂ => k p.1 p.2) (f := fun t : ℂ => (A.app t - 1, t)) s hd hc
  exact (h1.add h2).differentiableWithinAt

end GoldbachBoundaries.Paper2.M4a
