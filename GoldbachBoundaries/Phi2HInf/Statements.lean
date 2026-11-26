import GoldbachBoundaries.Phi2HInf.Defs
import GoldbachBoundaries.PhiR.Statement
import GoldbachBoundaries.Paper2.Statements
import GoldbachBoundaries.Phi2HInf.Proof.M5Boundary
import GoldbachBoundaries.Phi2HInf.Proof.RBoundary

/-!
The two theorems have exactly the shape of the RH versions `GoldbachBoundaries.phi2_natural_boundary` and
`GoldbachBoundaries.phiR_natural_boundary` (`Phi2/Statement.lean`, `PhiR/Statement.lean`), with `RiemannHypothesis`
replaced by `Hinf`, and with these two changes dictated by the mathematics:

Non-vacuity (deliverable 3) is discussed in the plan; `bsup_lt_one_of_hinf` below records the one consequence of
`Hinf` the whole argument rests on.
-/

noncomputable section

open Complex Filter Topology Set Metric

namespace GoldbachBoundaries.Phi2HInf

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-! ## A consequence of `(H_∞)` the cone rests on (real proof) -/



theorem bsup_lt_one_of_hinf (hH : Hinf) : Bsup < 1 := lem_B_iii hH

 

/--
Assume `(H_∞)` (for every `δ > 0` only finitely many zeros have `β > 1/2 + δ`), together with the classical inputs
`Z1`, `Z2`, `Z3`, `ZLittlewood` and the Stirling expansion `(Stir)`. Then `Φ₂` continues from `σ > 2` to a
single-valued meromorphic function on `ℍ = {σ > 1}`, and `σ = 1` is a natural boundary of `Φ₂`: no meromorphic function
on any disc centred on the line agrees with `Φ₂` on the part of the disc in `ℍ` (paper 1's `IsNaturalBoundary`, for
every meromorphic continuation `F`).

The shape is `phi2_natural_boundary` with `RiemannHypothesis` replaced by `Hinf` and the exact pole/residue clause
dropped (under `(H_∞)` the continuation also has poles at `ρ + ρ'`; see the module docstring).
-/
theorem phi2_hinf_natural_boundary (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hL : ZLittlewood)
    (hStir : StirlingStrip) :
    (∃ F : ℂ → ℂ, MeromorphicOn F HH ∧ EqOn F Phi2 (halfPlane 2)) ∧
    (∀ F : ℂ → ℂ, MeromorphicOn F HH → F =ᶠ[codiscreteWithin (halfPlane 2)] Phi2 →
      IsNaturalBoundary F HH lineOne) := by
  exact ⟨⟨Phi2cHInf, phi2_hinf_continuation hH hZ1 hZ2 hZ3 hStir⟩,
    phi2_hinf_boundary hH hZ1 hZ2 hZ3 hL hStir⟩

 

/--
The shape is `phiR_natural_boundary` with `RiemannHypothesis` replaced by `Hinf` and the pole/residue clause dropped.
-/
theorem phiR_hinf_natural_boundary (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hL : ZLittlewood)
    (hStir : StirlingStrip) {r : ℕ} (hr : 2 ≤ r) :
    (∃ F : ℂ → ℂ, MeromorphicOn F (halfPlane ((r : ℝ) - 1)) ∧ EqOn F (PhiR r) (halfPlane r)) ∧
    (∀ F : ℂ → ℂ, MeromorphicOn F (halfPlane ((r : ℝ) - 1)) →
      F =ᶠ[codiscreteWithin (halfPlane r)] PhiR r →
      IsNaturalBoundary F (halfPlane ((r : ℝ) - 1)) (lineAt ((r : ℝ) - 1))) := by
  obtain ⟨E, hE⟩ := exists_cutoff hH
  exact ⟨⟨PhiRcHInf E r, phiR_hinf_continuation hH hZ1 hZ2 hZ3 hStir hE hr⟩,
    phiR_hinf_boundary hH hZ1 hZ2 hZ3 hL hStir hr⟩

end GoldbachBoundaries.Phi2HInf
