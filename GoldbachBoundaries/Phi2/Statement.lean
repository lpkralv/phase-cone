import GoldbachBoundaries.Phi2.Defs
import GoldbachBoundaries.Phi2.Proof.M5Boundary

/-!
The statement is in the style of paper 1's `thm_B` (parts 2 and 3): a meromorphic continuation of `Φ₂` to `ℍ` with
simple poles exactly at `2` and `1 + ρ` and the residues there, and the line `σ = 1` as a natural boundary of every
meromorphic continuation, in paper 1's sense `IsNaturalBoundary` (no meromorphic function on any disc centred on the
line agrees with it on the part of the disc in `ℍ`, off a discrete set).

Hypotheses: RH (Mathlib's `RiemannHypothesis`), and three classical theorems taken as named premises, exactly as paper 2
did (`Paper2/Defs.lean`): (Z2) Riemann–von Mangoldt with the local count `N(t+1) - N(t) ≪ log t`, (Z3) the local
expansion of `ζ'/ζ`, and Littlewood's gap theorem `ZLittlewood` (paper 2's (Z8)). (Z1) is not needed: under RH it is
proved (`Phi2Proof.Z1_of_RH`).
-/

noncomputable section

open Complex Filter Topology Set Metric

namespace GoldbachBoundaries

open GoldbachBoundaries.Paper2

/-! ## Sanity lemmas (real proofs) -/

/-- The terms of `Φ₂` with `m = 0` vanish (`Λ(0) = 0`), so `Phi2` is the sum over `m, n ≥ 1`. -/
theorem Phi2_term_zero_left (n : ℕ) (s : ℂ) :
    ((ArithmeticFunction.vonMangoldt 0 : ℝ) : ℂ) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
      (((0 + n : ℕ) : ℂ)) ^ (-s) = 0 := by
  simp

/-- The terms of `Φ₂` with `n = 0` vanish. -/
theorem Phi2_term_zero_right (m : ℕ) (s : ℂ) :
    ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) * ((ArithmeticFunction.vonMangoldt 0 : ℝ) : ℂ) *
      (((m + 0 : ℕ) : ℂ)) ^ (-s) = 0 := by
  simp

/-- The pole set lies in `ℍ`, unconditionally (`Re(1 + ρ) = 1 + Re ρ > 1`). -/
theorem phi2Poles_subset_HH : phi2Poles ⊆ HH := by
  rintro s (hs | ⟨ρ, hρ, rfl⟩)
  · rw [mem_singleton_iff.mp hs]; norm_num [halfPlane]
  · show 1 < (1 + ρ).re
    simp only [add_re, one_re]
    linarith [hρ.2.1]

/-- Non-vacuity of `HasPhi2Residues` (no RH): the two clauses never conflict, since `1 + ρ ≠ 2` (`0 < Re ρ < 1`). -/
theorem exists_hasPhi2Residues : ∃ v, HasPhi2Residues v := by
  classical
  refine ⟨fun s => if s = 2 then 1 else -(2 * (zetaMult (s - 1) : ℂ)) / (s - 1), by simp, ?_⟩
  intro ρ hρ
  have hne : (1 + ρ : ℂ) ≠ 2 := by
    intro h
    have := congrArg Complex.re h
    simp only [add_re, one_re] at this
    norm_num at this
    linarith [hρ.2.2]
  simp [hne]

/-! ## The theorem -/

/--
Assume RH. Then `Φ₂` continues from `σ > 2` to a meromorphic function on `ℍ = {σ > 1}` whose poles are exactly the
points `2` and `1 + ρ` (`ρ` a non-trivial zero), all simple, with residue `1` at `2` and `-2m(ρ)/ρ` at `1 + ρ`; and
`σ = 1` is a natural boundary of `Φ₂`: no meromorphic function on any disc centred on the line agrees with `Φ₂` on the
part of the disc in `ℍ`.
-/
theorem phi2_natural_boundary (hRH : RiemannHypothesis) (hZ2 : Z2) (hZ3 : Z3) (hL : ZLittlewood) :
    (∃ F : ℂ → ℂ, MeromorphicOn F HH ∧ EqOn F Phi2 (halfPlane 2) ∧
      AnalyticOnNhd ℂ F (HH \ phi2Poles) ∧
      (∀ α ∈ phi2Poles, meromorphicOrderAt F α = -1) ∧
      ∃ res : ℂ → ℂ, (∀ α ∈ phi2Poles, HasResidue F α (res α)) ∧ HasPhi2Residues res ∧
        ∀ α ∈ phi2Poles, res α ≠ 0) ∧
    (∀ F : ℂ → ℂ, MeromorphicOn F HH → F =ᶠ[codiscreteWithin (halfPlane 2)] Phi2 →
      IsNaturalBoundary F HH lineOne) :=
  ⟨⟨Phi2Proof.Phi2c, Phi2Proof.phi2_continuation hRH⟩,
    fun F hF hFΦ => Phi2Proof.phi2_boundary hRH hZ2 hZ3 hL F hF hFΦ⟩

end GoldbachBoundaries
