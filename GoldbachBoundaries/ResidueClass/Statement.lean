import GoldbachBoundaries.ResidueClass.HigherReduction
import GoldbachBoundaries.ResidueClass.ExceptionalHigher

/-! # Natural boundary theorems for Goldbach series in residue class one -/

noncomputable section

open Complex Filter Set
open scoped Topology

namespace GoldbachBoundaries.ResidueClass

variable {q : ℕ} [NeZero q]

/-- The binary series continues meromorphically to
`Re s > 1`. Every meromorphic continuation from `Re s > 2`, with agreement in
the codiscrete sense, has the line `Re s = 1` as a natural boundary. The classical
inputs are the two local logarithmic-derivative expansions, the zeta zero gap
estimate, and the strip version of Stirling's formula. -/
theorem phi2_natural_boundary (_hq : 2 ≤ q) (_hGRH : GRH q) (_hZ3 : Paper2.Z3)
    (_hLocal : LogDerivPrimitiveLocal q) (_hGap : Paper2.ZLittlewood)
    (_hStir : Phi2HInf.StirlingStrip) :
    (∃ F : ℂ → ℂ, MeromorphicOn F HH ∧ EqOn F (Phi2 q) (halfPlane 2)) ∧
    (∀ F : ℂ → ℂ, MeromorphicOn F HH → F =ᶠ[codiscreteWithin (halfPlane 2)] Phi2 q →
      IsNaturalBoundary F HH lineOne) := by
  exact ⟨⟨phi2Continuation q, meromorphicOn_phi2Continuation _hGRH _hZ3 _hLocal,
    eqOn_phi2Continuation _hGRH _hZ3 _hLocal⟩,
    isNaturalBoundary_phi2_of_agrees _hGRH _hZ3 _hLocal _hGap _hStir⟩

/-- For every `r ≥ 2`, the `r`-fold series continues
meromorphically to `Re s > r - 1`. Every meromorphic continuation from `Re s > r`,
with agreement in the codiscrete sense, has the line `Re s = r - 1` as a natural
boundary. The classical inputs are those of the binary theorem. -/
theorem phiR_natural_boundary (_hq : 2 ≤ q) (_hGRH : GRH q) (_hZ3 : Paper2.Z3)
    (_hLocal : LogDerivPrimitiveLocal q) (_hGap : Paper2.ZLittlewood)
    (_hStir : Phi2HInf.StirlingStrip) {r : ℕ} (_hr : 2 ≤ r) :
    (∃ F : ℂ → ℂ, MeromorphicOn F (halfPlane ((r : ℝ) - 1)) ∧
      EqOn F (PhiR q r) (halfPlane r)) ∧
    (∀ F : ℂ → ℂ, MeromorphicOn F (halfPlane ((r : ℝ) - 1)) →
      F =ᶠ[codiscreteWithin (halfPlane r)] PhiR q r →
      IsNaturalBoundary F (halfPlane ((r : ℝ) - 1)) (lineAt ((r : ℝ) - 1))) := by
  exact ⟨⟨phiRContinuation q r, meromorphicOn_phiRContinuation _hGRH _hZ3 _hLocal _hr,
    eqOn_phiRContinuation _hGRH _hZ3 _hLocal _hr⟩,
    isNaturalBoundary_phiR_of_agrees _hGRH _hZ3 _hLocal _hGap _hStir _hr⟩

end GoldbachBoundaries.ResidueClass
