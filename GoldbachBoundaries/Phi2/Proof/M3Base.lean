import GoldbachBoundaries.Phi2.Proof.M2Explicit




noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics

namespace GoldbachBoundaries.Phi2Proof

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **`∑_{(ρ,ρ')} |a_ρ a_ρ'| < ∞`** (RH, (Z2)): the product of two absolutely summable families.
Real proof from `summable_norm_zeroCoef` and Mathlib's `Summable.mul_norm`. -/
theorem summable_norm_pair (hRH : RiemannHypothesis) (hZ2 : Z2) :
    Summable (fun p : NontrivialZeros × NontrivialZeros => ‖zeroCoef p.1 * zeroCoef p.2‖) :=
  Summable.mul_norm (f := fun ρ : NontrivialZeros => zeroCoef (ρ : ℂ))
    (g := fun ρ : NontrivialZeros => zeroCoef (ρ : ℂ)) (summable_norm_zeroCoef hRH hZ2)
    (summable_norm_zeroCoef hRH hZ2)

end GoldbachBoundaries.Phi2Proof
