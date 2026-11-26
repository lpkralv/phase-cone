import GoldbachBoundaries.Paper2.M2.Single
import GoldbachBoundaries.Paper2.M2.Fill.cor_LW_branch
import GoldbachBoundaries.Paper2.M2.Fill.cor_LW_ext
import GoldbachBoundaries.Paper2.M2.Fill.eventuallyEq_codiscreteWithin_of_nhdsNE
import GoldbachBoundaries.Paper2.M2.Fill.exists_imagAxis_mem
import GoldbachBoundaries.Paper2.M2.Fill.neg_deriv_eventuallyEq_Qcont_of_isPBranch
import GoldbachBoundaries.Paper2.M2.Fill.singleRep_points_infinite

/-!
# M2: the theorem of Landau–Walfisz (`nr:cor:LW`)

(Z1), (Z2), (Z4), (Z5), as in the signed-off statement (the paper's route goes through `nr:thm:single`).

1. Poles accumulate at every `iy`: `thm_single_infinite_proof` gives infinitely many single-representation points
   `u = ρ/q` near `iy` for `y > 0`; conjugation (`y < 0`) and a shifted disc (`y = 0`) give the other `y`. Each is a
   pole of every continuation `Qc` (`R_u = m(ρ)/q ≠ 0`, `meromorphicOrderAt_Qcont_neg_iff`, `isQCont_eventuallyEq`).
2. Hence `Qcont` has no meromorphic extension across any point `iy` (paper 1's
   `noMeromorphicExtensionAt_of_poles_in_every_ball`).
3. A meromorphic `f` on a connected open `W ⊋ {Re z > 0}` agreeing with `Q` off a discrete subset of `Re z > 1` agrees
   with `Qcont` off a discrete subset of `{Re z > 0}` (identity theorem), and `W` contains a point `iy`
   (connectedness): this contradicts 2.
4. For a branch `g` of `P` at `z₁`, `-g'` is the germ of `Qcont` at `z₁` (the derivative of a continuation along a path
   is a continuation of the derivative, and `Qcont` is analytic along the path, so `germ_unique` of paper 1's ThmA
   applies). A meromorphic extension `f` of `g` to a disc about `iy` would make `-f'` a meromorphic extension of
   `Qcont` (identity theorem on the convex set `disc ∩ {Re z > 0}`), contradicting 2.

**Integrated layout.** The six lemmas this file stated with `sorry` (`singleRep_points_infinite`,
`eventuallyEq_codiscreteWithin_of_nhdsNE`, `exists_imagAxis_mem`, `neg_deriv_eventuallyEq_Qcont_of_isPBranch`,
`cor_LW_ext`, `cor_LW_branch`) are proved in `Fill/<name>.lean`, statements unchanged, each with its sketch as
docstring; the fill files import `Single.lean` (and each other where needed), and this file imports them. The real
lemmas `poles_Qc_accumulate` and `noMeromorphicExtensionAt_Qcont`, which use `singleRep_points_infinite`, sit at the
end of `Fill/singleRep_points_infinite.lean`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M2

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-! ## Target -/

/-- `cor_LW` of `Paper2/Statements.lean`, statement verbatim. -/
theorem cor_LW_proof (hZ1 : Z1) (hZ2 : Z2) (hZ4 : Z4) (hZ5 : Z5) :
    (∀ Qc : ℂ → ℂ, IsQCont Qc → ∀ y : ℝ, ∀ ε : ℝ, 0 < ε →
      {a | a ∈ halfPlane 0 ∧ ‖a - y * I‖ < ε ∧ meromorphicOrderAt Qc a < 0}.Infinite) ∧
    (∀ W : Set ℂ, IsOpen W → IsConnected W → halfPlane 0 ⊂ W →
      ¬ ∃ f : ℂ → ℂ, MeromorphicOn f W ∧ f =ᶠ[codiscreteWithin (halfPlane 1)] Q) ∧
    ∀ (g : ℂ → ℂ) (z₁ : ℂ), IsPBranch g z₁ → ∀ y r : ℝ, 0 < r → z₁ ∈ ball ((y : ℂ) * I) r →
      ¬ GermExtendsMeromorphically g z₁ (ball ((y : ℂ) * I) r) :=
  ⟨poles_Qc_accumulate hZ1 hZ2 hZ4 hZ5, cor_LW_ext hZ1 hZ2 hZ4 hZ5, cor_LW_branch hZ1 hZ2 hZ4 hZ5⟩

end GoldbachBoundaries.Paper2.M2
