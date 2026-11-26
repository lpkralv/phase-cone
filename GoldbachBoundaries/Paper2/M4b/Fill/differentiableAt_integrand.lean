import GoldbachBoundaries.Paper2.M4b.Fill.BCommon

/-!
# Fill: `differentiableAt_integrand`

`(z, s) ∈ domK1` (`0 < 1/2 < Re z < Re L(s) - 1/2`), so `k` is jointly differentiable there; `Qcont` is analytic at
`z` and at `L(s) - z` (`TIdentity.analyticAt_Qcont_of_RH`), composed with the projection and the affine map.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M4b

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **The integrand is holomorphic in `(z, s)` off its two poles** (RH, (K1)). `z ∈ Str(s)` (`0 < 1/2 < Re z` and
`Re z < Re L(s) - 1/2`), so `(z, s) ↦ k(z, s)` is differentiable at `(z, s)` (`hK1` on the open `domK1`, M4a's
`isOpen_domK1`). `Qcont` is analytic at `z` and at `L(s) - z` (paper 1's `analyticAt_Qcont_of_RH`: real part
`> 1/2`, `≠ 1`), composed with the projections and with `(z, s) ↦ L(s) - z` (affine). Size: 50–100 lines. -/
theorem differentiableAt_integrand (hRH : RiemannHypothesis) (A : Aff) (k : ℂ → ℂ → ℂ)
    (hK1 : K1 A k) {z s : ℂ} (hs : s ∈ A.DL) (hz : 1 / 2 < z.re) (hzs : 1 / 2 < (A.app s - z).re)
    (hz1 : z ≠ 1) (hzs1 : A.app s - z ≠ 1) :
    DifferentiableAt ℂ (fun p : ℂ × ℂ => k p.1 p.2 * Qcont p.1 * Qcont (A.app p.2 - p.1)) (z, s) := by
  have hzs' : z.re < (A.app s).re := by simp at hzs; linarith
  have hk := differentiableAt_k_of_K1B hK1 hs (by linarith) hzs'
  have hQ1 : DifferentiableAt ℂ (fun p : ℂ × ℂ => Qcont p.1) (z, s) :=
    DifferentiableAt.comp (f := fun p : ℂ × ℂ => p.1) (z, s)
      (TIdentity.analyticAt_Qcont_of_RH hRH hz hz1).differentiableAt differentiableAt_fst
  have happ : DifferentiableAt ℂ (fun p : ℂ × ℂ => A.app p.2 - p.1) (z, s) := by
    unfold Aff.app; fun_prop
  have hQ2 : DifferentiableAt ℂ (fun p : ℂ × ℂ => Qcont (A.app p.2 - p.1)) (z, s) :=
    DifferentiableAt.comp (f := fun p : ℂ × ℂ => A.app p.2 - p.1) (z, s)
      (TIdentity.analyticAt_Qcont_of_RH hRH hzs hzs1).differentiableAt happ
  exact (hk.mul hQ1).mul hQ2

end GoldbachBoundaries.Paper2.M4b
