import GoldbachBoundaries.Paper2.M6.Local
import GoldbachBoundaries.Paper2.M6.Fill.OmegaP_inter_halfPlane_half
import GoldbachBoundaries.Paper2.M6.Fill.isOpen_isPreconnected_slitHalf
import GoldbachBoundaries.Paper2.M6.Fill.eqOn_neg_log_add_Eaux
import GoldbachBoundaries.Paper2.M6.Fill.norm_neg_log_add_Eaux_le
import GoldbachBoundaries.Paper2.M6.Fill.norm_P_le

/-!
# M6: `P̃` on `Re z > 1/2` and its growth (`cl:lem:P`(v), (vi))

(v) Under RH the only point of `Σ` with `Re > 1/2` is `1` (paper 1's `lem_Sigma_iv_proof`), and the other cuts lie in
`Re ≤ 1/2`, so `Ω ∩ {Re z > 1/2} = {Re z > 1/2} ∖ (1/2, 1]`. Paper 1's `ThmA.Eaux` (the paper's `E`, `exists_Eaux`:
holomorphic on `Re z > 1/2`, `= P + Log(z - 1)` on `Re z > 1`) is the `E₁` of (v): `P̃ + Log(z - 1) - Eaux` is holomorphic
on the connected set `{Re z > 1/2} ∖ (1/2, 1]` and vanishes on `Re z > 1`. The paper's "a primitive of `1/(z - 1) - Q`,
then absorb the constant" is the same function.

(vi) The paper applies `nr:lem:growthQ` (which carries (Z1)-(Z3)) to `Q` and integrates horizontally. Here the bound comes
from (v) and paper 1's `ThmA.norm_Eaux_le` (RH only: `|E(z)| ≤ C(1 + log |Im z|)` on `1/2 + ε ≤ Re z ≤ σ₁`,
`|Im z| ≥ 2`) plus `|Log(z - 1)| ≤ log|z - 1| + π`. So (Z1)-(Z3) are not used (as in M4b-M5, item "under RH, paper 1's
bounds on `Q`"). The second bound is termwise.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M6

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-! ## Lemmas

Proved in `Fill/`, one file per lemma (same name, same statement): `OmegaP_inter_halfPlane_half`, `isOpen_isPreconnected_slitHalf`, `eqOn_neg_log_add_Eaux`, `norm_neg_log_add_Eaux_le`, `norm_P_le`. -/

/-! ## Targets -/

/-- `lem_P_v` of `Paper2/Statements.lean`, statement verbatim. -/
theorem lem_P_v_proof (hRH : RiemannHypothesis) :
    OmegaP ∩ halfPlane (1 / 2) = halfPlane (1 / 2) \ {z | ∃ x : ℝ, 1 / 2 < x ∧ x ≤ 1 ∧ z = x} ∧
    ∀ Pt : ℂ → ℂ, DifferentiableOn ℂ Pt OmegaP → EqOn Pt P (halfPlane 1) →
      ∃ E₁ : ℂ → ℂ, DifferentiableOn ℂ E₁ (halfPlane (1 / 2)) ∧
        ∀ z ∈ OmegaP ∩ halfPlane (1 / 2), Pt z = -Complex.log (z - 1) + E₁ z :=
  ⟨OmegaP_inter_halfPlane_half hRH, fun _ hPt hEq =>
    ⟨ThmA.Eaux, (ThmA.Eaux_spec hRH).1.differentiableOn, eqOn_neg_log_add_Eaux hRH hPt hEq⟩⟩

/-- `lem_P_vi` of `Paper2/Statements.lean`, statement verbatim. -/
theorem lem_P_vi_proof (hRH : RiemannHypothesis) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) :
    ∀ Pt : ℂ → ℂ, DifferentiableOn ℂ Pt OmegaP → EqOn Pt P (halfPlane 1) →
      (∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∃ C : ℝ, ∀ x y : ℝ, 1 / 2 + ε ≤ x → x ≤ 3 → 3 ≤ |y| →
        ‖Pt (x + y * I)‖ ≤ C * Real.log |y|) ∧
      ∀ z : ℂ, 1 < z.re → ‖Pt z‖ ≤ (P z.re).re := by
  have _ := hZ1  -- (Z1)-(Z3) are not used: under RH the growth comes from paper 1's `ThmA.norm_Eaux_le`
  have _ := hZ2
  have _ := hZ3
  intro Pt hPt hEq
  refine ⟨fun ε hε _ => ?_, fun z hz => ?_⟩
  · obtain ⟨C, hC⟩ := norm_neg_log_add_Eaux_le hRH hε
    refine ⟨C, fun x y hx hx3 hy => ?_⟩
    have hy0 : y ≠ 0 := by
      intro h; rw [h, abs_zero] at hy; norm_num at hy
    have hmem : (x : ℂ) + y * I ∈ OmegaP ∩ halfPlane (1 / 2) := by
      rw [OmegaP_inter_halfPlane_half hRH]
      refine ⟨?_, ?_⟩
      · show (1 / 2 : ℝ) < ((x : ℂ) + y * I).re
        simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero]
        linarith
      · rintro ⟨x', -, -, hx'⟩
        apply hy0
        have := congrArg Complex.im hx'
        simpa using this
    rw [eqOn_neg_log_add_Eaux hRH hPt hEq _ hmem]
    exact hC x y hx hx3 hy
  · rw [hEq hz]; exact norm_P_le hz

end GoldbachBoundaries.Paper2.M6
