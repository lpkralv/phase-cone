import GoldbachBoundaries.Paper2.M5.FilterII
import GoldbachBoundaries.Paper2.M5.Fill.evalH_root_bound
import GoldbachBoundaries.Paper2.M5.Fill.exists_ordinate_in_interval
import GoldbachBoundaries.Paper2.M5.Fill.CH_eq_two_terms
import GoldbachBoundaries.Paper2.M5.Fill.exists_tau0_CH_ne_zero
import GoldbachBoundaries.Paper2.M5.Fill.noMeromorphicExtensionAt_of_line_blowup

/-!
# M5: Theorem F (iii) (`cl:thm:filter`(iii)): `σ = 1` is a natural boundary of `D_H` under RH, (F) and Littlewood

The paper's argument. Fix `s₁ = 1 + iτ` and `ε > 0`. **The claim** (`exists_tau0_CH_ne_zero`): some `τ₀ ≠ τ` with
`|τ₀ - τ| < ε`, neither `0` nor an ordinate, has `C_H(τ₀) ≠ 0`. Given it, (ii) says `η D_H(s₀ + η) → C_H(τ₀) ≠ 0`, so every
`f` meromorphic on a disc about `s₁` and agreeing with `D_H` off a discrete set has a pole at `s₀ = 1 + iτ₀`
(`order_residue_of_codiscrete_line`), and these poles accumulate at `s₁` (`noMeromorphicExtensionAt_of_line_blowup`).

The claim, as in the paper (Egami–Matsumoto's construction): for all but finitely many `z`, `w ↦ H(z, w)` has at most `d`
roots (`evalH_root_bound`). Littlewood's theorem (`ZLittlewood`) puts an ordinate in every interval of length `2ε/N` far
out (`exists_ordinate_in_interval`). Pick a zero `ρ₁ = 1/2 + iγ₁` high up with `H(ρ₁, ·)` of at most `d` roots, and `N`
ordinates `γ'_i` in the window `(γ₁ - τ - ε, γ₁ - τ + ε)`, one per subinterval; `τ_i = γ₁ - γ'_i` are distinct points of
`(τ - ε, τ + ε)`, and at most `N - 1` of them are bad (a root of `H(ρ₁, ·)` at `ρ̄'_i`, an ordinate, `0`, or `τ`). For a good
one, (F) leaves exactly the two ordered pairs `(ρ₁, ρ̄'_i)`, `(ρ̄'_i, ρ₁)` with sum `1 + iτ₀`, and `C_H(τ₀)` is twice one
non-zero term (`CH_eq_two_terms`).

**How `thm_filter_iii` takes Littlewood's theorem.** As a premise, `hL : ZLittlewood` (signed-off review choice 7). The
paper names the same statement (Z8) ("an absolute constant `a` such that for every
sufficiently large `t` some zero has ordinate `γ` with `|γ - t| < a/log log log t`"); `ZLittlewood` is that statement
with `∀ᶠ t in atTop`. The Lean name differs (`ZLittlewood`, not `Z8`); the content matches.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-! ## Lemmas

Proved in `Fill/`, one file per lemma (same name, same statement): `evalH_root_bound`, `exists_ordinate_in_interval`, `CH_eq_two_terms`, `exists_tau0_CH_ne_zero`, `noMeromorphicExtensionAt_of_line_blowup`. -/

/-! ## Target -/

/-- `thm_filter_iii` of `Paper2/Statements.lean`, statement verbatim. -/
theorem thm_filter_iii_proof (hRH : RiemannHypothesis) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6)
    (hL : ZLittlewood) (hF : HypF)
    (H : MvPolynomial (Fin 2) ℂ) (hH0 : H ≠ 0) (hHs : ∀ z w, evalH H z w = evalH H w z)
    (hH1 : ∀ w, evalH H 1 w = 0) :
    (∀ F : ℂ → ℂ, DifferentiableOn ℂ F HH → EqOn F (DH H) (halfPlane 2) →
      IsNaturalBoundary F HH lineOne) ∧
    ∀ F : ℂ → ℂ, DifferentiableOn ℂ F HH → EqOn F T0 (halfPlane 2) → IsNaturalBoundary F HH lineOne := by
  have hpart : ∀ H : MvPolynomial (Fin 2) ℂ, H ≠ 0 → (∀ z w, evalH H z w = evalH H w z) →
      (∀ w, evalH H 1 w = 0) → ∀ F : ℂ → ℂ, DifferentiableOn ℂ F HH → EqOn F (DH H) (halfPlane 2) →
        IsNaturalBoundary F HH lineOne := by
    intro H hH0 hHs hH1 F hFh hFD s₁ hs₁
    have hs₁' : s₁.re = 1 := hs₁
    have hs₁eq : s₁ = 1 + (s₁.im : ℂ) * I := by
      apply Complex.ext <;> simp [hs₁']
    rw [hs₁eq]
    refine noMeromorphicExtensionAt_of_line_blowup hFh fun ε hε => ?_
    obtain ⟨τ₀, hne, hlt, h0, hord, hCH⟩ := exists_tau0_CH_ne_zero hRH hL hF H hH0 hHs s₁.im hε
    exact ⟨τ₀, hne, hlt, CH H τ₀, hCH,
      (thm_filter_ii_proof hRH hZ1 hZ2 hZ3 hZ6 H hH0 hHs hH1 h0 hord F hFh hFD).2⟩
  refine ⟨hpart H hH0 hHs hH1, fun F hFh hFT => ?_⟩
  obtain ⟨h0, hs, h1⟩ := H0f_conditions
  exact hpart H0f h0 hs h1 F hFh (eqOn_DH_H0f_of_T0 hRH hZ1 hZ2 hZ3 hZ6 hFh hFT)

end GoldbachBoundaries.Paper2.M5
