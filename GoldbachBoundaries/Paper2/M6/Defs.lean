import GoldbachBoundaries.Paper2.M5.Skeleton

/-!
# Paper 2, Milestone M6 (the principal sheet of `P`; Theorem D for `G`): definitions and small facts

Everything in this file has a real proof.

## Objects

* `Ptil`: the principal sheet `P̃` as an explicit formula, `P̃(z) = P(z + 2) + ∫_0^2 Q(z + t) dt` with `Q` paper 1's
  `Qcont`. On `Ω` the segment `z + [0, 2]` stays in `Ω` (eastward rays stay in `Ω`), where `Qcont` is holomorphic, so
  `P̃` is holomorphic there with `P̃' = -Q(z+2) + (Q(z+2) - Q(z)) = -Q(z)`, and `P̃ = P` on `Re z > 1` by the
  fundamental theorem of calculus. This replaces the paper's `P(2) - ∫_2^z Q` "along any path in `Ω`", so no
  simple-connectivity argument is needed for `cl:lem:P`(ii) (the plan's section 1 row).
* `leftCut a = a - [0, ∞)`, the cut of `Ω` at `a` (so `OmegaP = halfPlane 0 \ ⋃_{a ∈ Σ} leftCut a`, `OmegaP_eq`).
* `rayFrom a θ = a + [0, ∞) e^{iθ}`, the ray of `cl:lem:P`(iv) (the same set as in the statement of `lem_P_iv`).
* `PBranchFam q f`: `f` is analytic at `q` and `-f' = Q` near `q`. Germs of branches of `P` are in this family
  (`pBranchFam_of_isPBranch`), and the family is uniform on `{Re z > 0} ∖ Σ` in the sense of paper 1's
  `ThmA.UniformFamily` (`uniformFamily_PBranchFam`), which is what `cl:lem:P`(iii) needs.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M6

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- The principal sheet `P̃(z) = P(z + 2) + ∫_0^2 Q(z + t) dt` of `P` (with `Q = Qcont`). Meaningful on `Ω`
(`hasDerivAt_Ptil`, `Ptil_eqOn_P`); elsewhere the integrand may meet a pole of `Qcont` and the value is junk. -/
def Ptil (z : ℂ) : ℂ := P (z + 2) + ∫ t in (0 : ℝ)..2, Qcont (z + t)

/-- The horizontal cut `a - [0, ∞)` running west from `a`. -/
def leftCut (a : ℂ) : Set ℂ := {z | ∃ t : ℝ, 0 ≤ t ∧ z = a - t}

/-- The ray `a + [0, ∞) e^{iθ}` of `cl:lem:P`(iv). -/
def rayFrom (a : ℂ) (θ : ℝ) : Set ℂ := {z | ∃ t : ℝ, 0 ≤ t ∧ z = a + t * exp (θ * I)}

/-- The germ family of branches of `P`: `f` analytic at `q` with `-f' = Qcont` near `q`. -/
def PBranchFam (q : ℂ) (f : ℂ → ℂ) : Prop :=
  AnalyticAt ℂ f q ∧ (fun z => -deriv f z) =ᶠ[𝓝 q] Qcont

/-! ## Real proofs -/

lemma OmegaP_eq : OmegaP = halfPlane 0 \ ⋃ a ∈ PoleSetQ, leftCut a := rfl

/-- An admissible germ is analytic at its base point. -/
lemma analyticAt_of_isAdmissibleGermOn {F : ℂ → ℂ} {Ω S : Set ℂ} {g : ℂ → ℂ} {s : ℂ}
    (h : IsAdmissibleGermOn F Ω S g s) : AnalyticAt ℂ g s := by
  obtain ⟨γ, -, -, h1, f, hf, -, hg1⟩ := h
  rw [← h1]; exact (hf.analyticAt 1).congr hg1.symm

/-- The base point of an admissible germ lies in the region. -/
lemma mem_of_isAdmissibleGermOn {F : ℂ → ℂ} {Ω S : Set ℂ} {g : ℂ → ℂ} {s : ℂ}
    (h : IsAdmissibleGermOn F Ω S g s) : s ∈ Ω := by
  obtain ⟨γ, hγ, -, h1, -⟩ := h
  rw [← h1]; exact hγ 1

/-- Germs of branches of `P` are in the family `PBranchFam` (M2's `neg_deriv_eventuallyEq_Qcont_of_isPBranch`). -/
lemma pBranchFam_of_isPBranch {g : ℂ → ℂ} {z₁ : ℂ} (hg : IsPBranch g z₁) : PBranchFam z₁ g :=
  ⟨analyticAt_of_isAdmissibleGermOn hg, (M2.neg_deriv_eventuallyEq_Qcont_of_isPBranch hg).2⟩

end GoldbachBoundaries.Paper2.M6
