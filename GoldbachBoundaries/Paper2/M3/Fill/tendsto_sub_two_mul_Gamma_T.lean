import GoldbachBoundaries.Paper2.M3.Fill.CCommon
import GoldbachBoundaries.Paper2.M3.Fill.tendsto_sub_two_mul_Mcal
import GoldbachBoundaries.Paper2.M3.Fill.Mcal_eq_formula

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
namespace GoldbachBoundaries.Paper2.M3
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **`(s - 2)Γ(s)T(s) → 1` as `s ↓ 2`** (from `Mcal_eq_formula`). Multiply `(nr:eq:hsq)` by `x - 2`:
`(x-2)Γ(x)T(x) = (x-2)𝓜(x) + 2(x-2)Γ(x-1)Q(x-1) - 1 + (x-2)E(x) - 2(x-2)e(x-1)`. Here `(x-2)𝓜(x) → 0`
(`tendsto_sub_two_mul_Mcal`); `(x-2)Q(x-1) → 1` (M1's `hasResidue_Qcont_Rcoef` at `a = 1` with `Rcoef_one'`, and
`TIdentity.Qcont_eq_Q_of_one_lt`; `HasResidue` is a limit on `𝓝[≠] 1`, composed with `x ↦ x - 1` on `𝓝[>] 2`) and
`Γ(x-1) → Γ(1) = 1`; `E`, `e` are continuous (`TIdentity.differentiable_E2`, `differentiable_e1`). Size: 100–200
lines. -/
theorem tendsto_sub_two_mul_Gamma_T :
    Tendsto (fun x : ℝ => ((x : ℂ) - 2) * Gamma x * T x) (𝓝[>] 2) (𝓝 1) := by
  -- the pieces
  have hM : Tendsto (fun x : ℝ => ((x : ℂ) - 2) * Mcal x) (𝓝[>] 2) (𝓝 0) := tendsto_sub_two_mul_Mcal
  have hofR : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[>] (2 : ℝ)) (𝓝 2) := by
    have := (Complex.continuous_ofReal.tendsto (2 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi (2 : ℝ)))
    simpa using this
  have hlin : Tendsto (fun x : ℝ => (x : ℂ) - 2) (𝓝[>] (2 : ℝ)) (𝓝 0) := by
    simpa using hofR.sub_const 2
  have hG1 : Tendsto (fun x : ℝ => Gamma ((x : ℂ) - 1)) (𝓝[>] (2 : ℝ)) (𝓝 1) := by
    have hc : ContinuousAt Gamma 1 := (cc_analyticAt_Gamma (z := 1) (by simp)).continuousAt
    have h1 : Tendsto (fun x : ℝ => (x : ℂ) - 1) (𝓝[>] (2 : ℝ)) (𝓝 1) := by
      have := hofR.sub_const 1
      norm_num at this
      exact this
    have := hc.tendsto.comp h1
    rw [Complex.Gamma_one] at this
    exact this
  have hQ : Tendsto (fun x : ℝ => ((x : ℂ) - 2) * Qcont ((x : ℂ) - 1)) (𝓝[>] (2 : ℝ)) (𝓝 1) := by
    have hres : HasResidue Qcont 1 (Rcoef 1) := hasResidue_Qcont_Rcoef (Or.inl (Or.inl rfl))
    rw [Rcoef_one'] at hres
    have hmap : Tendsto (fun x : ℝ => (x : ℂ) - 1) (𝓝[>] (2 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have := hofR.sub_const 1
        norm_num at this
        exact this
      · filter_upwards [self_mem_nhdsWithin] with x hx
        simp only [mem_compl_iff, mem_singleton_iff]
        intro h
        have := congrArg Complex.re h
        simp at this
        have hx' : (2 : ℝ) < x := hx
        linarith
    refine (hres.comp hmap).congr fun x => ?_
    simp only [Function.comp_apply]
    ring_nf
  have hE : Tendsto (fun x : ℝ => ((x : ℂ) - 2) * Ecal x) (𝓝[>] (2 : ℝ)) (𝓝 0) := by
    have hc : ContinuousAt Ecal 2 := by
      rw [Ecal_eq_E2]; exact TIdentity.differentiable_E2.continuous.continuousAt
    simpa using hlin.mul (hc.tendsto.comp hofR)
  have he : Tendsto (fun x : ℝ => ((x : ℂ) - 2) * ecal ((x : ℂ) - 1)) (𝓝[>] (2 : ℝ)) (𝓝 0) := by
    have hc : Continuous ecal := by
      rw [ecal_eq_e1]; exact TIdentity.differentiable_e1.continuous
    simpa using hlin.mul ((hc.tendsto _).comp (hofR.sub_const 1))
  have hsum := ((((hM.add ((tendsto_const_nhds (x := (2 : ℂ))).mul (hG1.mul hQ))).sub
    (tendsto_const_nhds (x := (1 : ℂ)))).add hE).sub ((tendsto_const_nhds (x := (2 : ℂ))).mul he))
  norm_num at hsum
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx2 : (2 : ℝ) < x := hx
  have hs : 2 < (x : ℂ).re := by simpa using hx2
  have hF := Mcal_eq_formula hs
  have hQQ : Qcont ((x : ℂ) - 1) = Q ((x : ℂ) - 1) :=
    TIdentity.Qcont_eq_Q_of_one_lt (by simp; linarith)
  have hne : (x : ℂ) - 2 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  rw [hF, hQQ]
  field_simp
  ring

end GoldbachBoundaries.Paper2.M3
