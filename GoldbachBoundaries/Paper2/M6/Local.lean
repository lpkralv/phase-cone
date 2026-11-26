import GoldbachBoundaries.Paper2.M6.Branch
import GoldbachBoundaries.Paper2.M6.Fill.exists_E_pole
import GoldbachBoundaries.Paper2.M6.Fill.isClosed_rayFrom
import GoldbachBoundaries.Paper2.M6.Fill.hasDerivAt_log_ray
import GoldbachBoundaries.Paper2.M6.Fill.eventuallyEq_add_const_of_hasDerivAt

/-!
# M6: `P` near a point of `Σ` (`cl:lem:P`(iv), local form)

The paper's proof: on `Δ`, `-Q = c_a/(z - a) + q_a` with `q_a` holomorphic; `E_a` is a primitive of `q_a`; a branch of
`P` minus `c_a log(z - a)` minus `E_a` has derivative `0` on the slit disc. Here the split is paper 1's
`ThmA.Qcont_pole_split` (RH; `Qcont = Res_a(Qcont)/(z - a) + q` off `Σ`, `q` holomorphic on `{Re z > 0} ∖ (Σ ∖ {a})`),
with `Res_a(Qcont) = R_a = -c_a` (M1's `hasResidue_Qcont_Rcoef`). The branch of `log` is
`Log((z - a)/(-e^{iθ}))`, holomorphic off the ray `a + [0, ∞)e^{iθ}` with derivative `1/(z - a)`
(`hasDerivAt_log_ray`). "Derivative zero, so constant" is local at the base point `z₁`
(`eventuallyEq_add_const_of_hasDerivAt`), which is all the statement asks (equality of germs at `z₁`).
(Z1) is not used.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M6

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-! ## Lemmas

Proved in `Fill/`, one file per lemma (same name, same statement): `exists_E_pole`, `isClosed_rayFrom`, `hasDerivAt_log_ray`, `eventuallyEq_add_const_of_hasDerivAt`. -/

/-! ## Target -/

/-- `lem_P_iv` of `Paper2/Statements.lean`, statement verbatim. -/
theorem lem_P_iv_proof (hRH : RiemannHypothesis) (hZ1 : Z1) {a : ℂ} (ha : a ∈ PoleSetQ) {R : ℝ} (hR : 0 < R)
    (hΔ : ball a R ⊆ halfPlane 0) (hΔS : ball a R ∩ PoleSetQ = {a}) :
    ∃ E : ℂ → ℂ, DifferentiableOn ℂ E (ball a R) ∧
      ∀ θ : ℝ, ∀ z₁ ∈ ball a R \ {z | ∃ t : ℝ, 0 ≤ t ∧ z = a + t * exp (θ * I)},
        ∀ g : ℂ → ℂ, IsPBranch g z₁ → ∃ C : ℂ,
          g =ᶠ[𝓝 z₁] fun z => cP a * Complex.log ((z - a) / (-exp (θ * I))) + E z + C := by
  have _ := hZ1  -- (Z1) is not used: `Res_a Qcont = R_a` is M1's `hasResidue_Qcont_Rcoef`, unconditional
  have _ := hR
  obtain ⟨E, hEd, hE⟩ := exists_E_pole hRH ha hΔ hΔS
  refine ⟨E, hEd, fun θ z₁ hz₁ g hg => ?_⟩
  obtain ⟨han, hd⟩ := pBranchFam_of_isPBranch hg
  have hopen : IsOpen (ball a R \ rayFrom a θ) := isOpen_ball.sdiff (isClosed_rayFrom a θ)
  have hz₁' : z₁ ∈ ball a R \ rayFrom a θ := hz₁
  refine eventuallyEq_add_const_of_hasDerivAt (φ := fun z => -Qcont z)
    (g := fun z => cP a * Complex.log ((z - a) / (-exp (θ * I))) + E z) ?_
  filter_upwards [hopen.mem_nhds hz₁', han.eventually_analyticAt, hd] with z hz hza hzd
  have hza' : z ≠ a := fun h => hz.2 ⟨0, le_rfl, by simp [h]⟩
  refine ⟨?_, ?_⟩
  · have h2 : deriv g z = -Qcont z := by rw [← hzd]; ring
    exact h2 ▸ hza.differentiableAt.hasDerivAt
  · have h1 := ((hasDerivAt_log_ray hz.2).const_mul (cP a)).add (hE z hz.1 hza')
    have hsub : z - a ≠ 0 := sub_ne_zero.mpr hza'
    convert h1 using 1
    simp only [cP]
    field_simp
    ring

end GoldbachBoundaries.Paper2.M6
