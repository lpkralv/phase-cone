import GoldbachBoundaries.Paper2.M2.Skeleton
import GoldbachBoundaries.Paper2.M1.Skeleton
import GoldbachBoundaries.TIdentity.Assembly

/-!
# Paper 2, Milestone M3 (Theorem C of paper 2): definitions

M3 closes the statements of `Paper2/Statements.lean` behind Theorem C (Section 3.7, "Off-line zeros and
the real axis", and `nr:prop:dichotomy`(ii)): `lem_A`, `thm_real_a`, `thm_real_b`, `lem_hsq`, `lem_Landau`, `thm_test`,
`cor_test`, `rem_classical_ii`, `rem_classical_iii`, `rem_dichotomy_ii`, and `cor_one_add_RH` (Section 3.3). With
them `intro_thm_C` of `Paper2/Statements.lean` is proved.

Nothing here imports `Paper2/Statements.lean`; the targets restate its statements verbatim. Layout (acyclic, in
dependency order): `Zeros` (Mathlib's RH against the strip), `Numerics` (`C₀`), `AConst` (`lem_A_proof`), `Real`
(`cor_one_add_RH_proof`, `thm_real_a_proof`, `thm_real_b_proof`, `rem_dichotomy_ii_proof`), `Hsq` (`lem_hsq_proof`),
`Landau` (`lem_Landau_proof`), `Mellin` (the abscissa of `𝓜`), `Test` (`thm_test_proof`, `cor_test_proof`),
`Classical` (`rem_classical_ii_proof`), `Skeleton` (`rem_classical_iii_proof`, and the index). A target that a later
file needs is proved in its own file, so a filler of a later lemma can import it.

## Objects

* `Mform F s = Γ(s)F(s) - 2Γ(s-1)Q(s-1) + 1/(s-2) - E(s) + 2e(s-1)`, the right side of `(nr:eq:hsq)` with `F` for `T`
  and paper 1's `Qcont` for `Q`: the function `𝓜̃` of Step 1 of `nr:thm:test` (`F = T̃`) and the continued `𝓜` of
  `nr:rem:classical`(iii) (`F = Tcont`, M1's continuation of `T`).
* `phiH u = h(e^{-u})²`, the function `φ` of Step 2 of `nr:thm:test`, whose Laplace transform is `𝓜`.
* `ballsU a b r = ⋃_{x ∈ (a, b]} Δ(x, r x)`, the open set `U₀` of Step 1 of `nr:thm:test` (discs centred on the real
  segment).
* `IsTestPair U T̃`: the right side of `nr:thm:test` (an open `U ⊇ (1, 2]` and a meromorphic `T̃` on `U` with the RH
  polar data on `(1, 2)`).

Paper 1's `TIdentity` library has the same functions under other names: `Theta = Fw`, `hErr = TIdentity.hErr`,
`Mcal = Rr`, `Ecal = E2`, `ecal = e1` (definitionally; the real lemmas below). Its `m1 z = ∫_0^1 h(t) t^{z-1} dt` is
the function `N(z)` of Step 3 of `nr:thm:test`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M3

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- The right side of `(nr:eq:hsq)` with `F` in place of `T` and `Qcont` for `Q`:
`Γ(s)F(s) - 2Γ(s-1)Q(s-1) + 1/(s-2) - E(s) + 2e(s-1)`. -/
def Mform (F : ℂ → ℂ) (s : ℂ) : ℂ :=
  Gamma s * F s - 2 * Gamma (s - 1) * Qcont (s - 1) + 1 / (s - 2) - Ecal s + 2 * ecal (s - 1)

/-- `φ(u) = h(e^{-u})²` (Step 2 of `nr:thm:test`): with `t = e^{-u}`, `𝓜(s) = ∫_0^∞ φ(u) e^{-su} du`. -/
def phiH (u : ℝ) : ℝ := hErr (Real.exp (-u)) ^ 2

/-- `⋃_{x ∈ (a, b]} Δ(x, r x)`: discs centred on the real segment `(a, b]`. -/
def ballsU (a b : ℝ) (r : ℝ → ℝ) : Set ℂ := ⋃ x ∈ Ioc a b, ball (x : ℂ) (r x)

/-- The right side of `nr:thm:test`: `U` open, `U ⊇ (1, 2]`, `T̃` meromorphic on `U`, `T̃ = T` on `U ∩ {σ > 2}`, the
poles of `T̃` on `(1, 2)` exactly the `1 + 1/k` (`k ≥ 2` squarefree), each simple with residue `2μ(k)`. -/
def IsTestPair (U : Set ℂ) (Tt : ℂ → ℂ) : Prop :=
  IsOpen U ∧ (∀ x : ℝ, x ∈ Ioc (1 : ℝ) 2 → (x : ℂ) ∈ U) ∧ MeromorphicOn Tt U ∧ EqOn Tt T (U ∩ halfPlane 2) ∧
    (∀ x : ℝ, x ∈ Ioo (1 : ℝ) 2 →
      (meromorphicOrderAt Tt x < 0 ↔ ∃ k : ℕ, 2 ≤ k ∧ Squarefree k ∧ (x : ℂ) = 1 + 1 / (k : ℂ))) ∧
    ∀ k : ℕ, 2 ≤ k → Squarefree k →
      meromorphicOrderAt Tt (1 + 1 / (k : ℂ)) = -1 ∧ HasResidue Tt (1 + 1 / (k : ℂ)) (2 * mu k)

/-! ## Paper 1's names (definitional) -/

lemma Theta_eq_Fw : Theta = TIdentity.Fw := rfl

lemma hErr_eq : hErr = TIdentity.hErr := rfl

lemma Mcal_eq_Rr : Mcal = TIdentity.Rr := rfl

lemma Ecal_eq_E2 : Ecal = TIdentity.E2 := rfl

lemma ecal_eq_e1 : ecal = TIdentity.e1 := rfl

/-! ## Small real lemmas -/

/-- RH implies `(H_∞)` (the proof of `hinf_of_RH` in `Paper2/Statements.lean`, which this file may not import). -/
lemma hinf_of_RH' (hRH : RiemannHypothesis) : Hinf := by
  intro δ hδ
  convert Set.finite_empty
  ext ρ
  simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_lt]
  intro hρ
  rw [re_eq_half_of_mem_nontrivialZeros hRH hρ]
  linarith

/-- Agreement on a set gives agreement off a discrete subset of it. -/
lemma eventuallyEq_codiscreteWithin_of_eqOn {f g : ℂ → ℂ} {S : Set ℂ} (h : EqOn f g S) :
    f =ᶠ[codiscreteWithin S] g := by
  rw [Filter.EventuallyEq, Filter.Eventually, mem_codiscreteWithin]
  intro x _
  rw [Filter.disjoint_principal_right]
  filter_upwards [self_mem_nhdsWithin] with y _
  simp only [mem_compl_iff, Set.mem_sdiff, mem_ofPred_eq, not_and, not_not]
  exact fun hyS => h hyS

end GoldbachBoundaries.Paper2.M3
