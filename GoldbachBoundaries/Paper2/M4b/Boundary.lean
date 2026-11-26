import GoldbachBoundaries.Paper2.M4b.Mero
import GoldbachBoundaries.Paper2.M4b.Fill.exists_pole_near_line

/-!
# M4b: Theorem E (iii) (`cl:thm:mero`(iii)), the natural boundary of `D^log`

The paper's proof: under (K4), `𝔟` is meromorphic near each point `s₀` of the line `Re L = 1` and not identically zero
there (M4a: `bracket_meromorphic_of_K4`, `not_eventually_zero_of_eqOn_bracket`), so it has no zero in a punctured
disc about `s₀`; the scaled-zero pinches `α = L⁻¹(1 + ρ/n)` accumulate at `s₀` (M4a: `prop_catalogue_ii_proof`), lie
in the strip `1 < Re L < 2` and have `𝔟(α) ≠ 0`, so each is a pole of every admissible continuation (Theorem E(i)), and
poles accumulating at `s₀` exclude a meromorphic extension there (paper 1's
`noMeromorphicExtensionAt_of_poles_in_every_ball`).
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M4b

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-! ## Lemmas

Proved in `Fill/`, one file per lemma (same name, same statement): `exists_pole_near_line`. -/

/-! ## Target -/

/-- `thm_mero_iii` of `Paper2/Statements.lean`, statement verbatim. -/
theorem thm_mero_iii_proof (hRH : RiemannHypothesis) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (A : Aff)
    (k : ℂ → ℂ → ℂ) (W : ℂ → ℕ → ℕ → ℂ) (hK1 : K1 A k) (hK2 : K2 A k) (hR : HypR A k W Q)
    (hK4 : K4 k) (hb : ∃ s ∈ A.DL, bracket A k s ≠ 0) :
    ∀ F : ℂ → ℂ, MeromorphicOn F A.HL → F =ᶠ[codiscreteWithin A.RL] Dser W →
      IsNaturalBoundary F A.HL A.lineL := by
  have _ := hZ1  -- (Z1)-(Z3) are not used, as in `thm_mero_i_proof`
  have _ := hZ2
  have _ := hZ3
  intro F hF hFW z₀ hz₀
  exact noMeromorphicExtensionAt_of_poles_in_every_ball (M4a.isOpen_HL A)
    (exists_pole_near_line hRH A k W hK1 hK2 hR hK4 hb hF hFW hz₀)

end GoldbachBoundaries.Paper2.M4b
