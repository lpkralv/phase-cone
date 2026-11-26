import GoldbachBoundaries.Phi2HInf.Statements

/-! T₀, route B §§4–6: definitions. The prime sum and the Lambda sum are distinct.
Every zero pair below is ordered; multiplicity is included in `zeroCoef`.
The six final premises are reused without modification. -/
noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
namespace GoldbachBoundaries.T0HInf
open GoldbachBoundaries Paper2
open _root_.GoldbachBoundaries.Phi2HInf (StirlingStrip)

abbrev Fp := TIdentity.Fw

def FpPrime (x : ℝ) : ℝ :=
  ∑' p : Nat.Primes, -((p : ℕ) : ℝ) * Real.log (p : ℕ) * Real.exp (-((p : ℕ) * x))

def L (x : ℝ) : ℂ := (Fp x + x * FpPrime x : ℝ)

def zeroCoef (ρ : ℂ) : ℂ := (ρ - 1) * Phi2Proof.zeroCoef ρ

def U (x : ℝ) : ℂ := ∑' ρ : NontrivialZeros, zeroCoef ρ * (x : ℂ) ^ (-(ρ : ℂ))

def primeSquareCoef : ℂ := -(Real.sqrt Real.pi : ℂ) / 4

def remainderAbscissa : ℝ := (1 / 2 + max (Bsup / 2) (1 / 3)) / 2

def cutoffAbscissa : ℝ := 3 / 4 - remainderAbscissa / 2

def crossingAbscissa : ℝ := max Bsup (remainderAbscissa + cutoffAbscissa)

def IsCutoff (E : Finset NontrivialZeros) : Prop :=
  ∀ ρ : NontrivialZeros, ρ ∈ E ↔ cutoffAbscissa < (ρ : ℂ).re

def exceptionalU (E : Finset NontrivialZeros) (x : ℝ) : ℂ :=
  ∑ ρ ∈ E, zeroCoef ρ * (x : ℂ) ^ (-(ρ : ℂ))

def residualU (E : Finset NontrivialZeros) (x : ℝ) : ℂ := U x - exceptionalU E x

def R (x : ℝ) : ℂ := L x - U x - primeSquareCoef * (x : ℂ) ^ (-(1 / 2 : ℂ))

def EL (z : ℂ) : ℂ := ∫ x in Ioi (1 : ℝ), L x * (x : ℂ) ^ (z - 1)

def E2 (z : ℂ) : ℂ := ∫ x in Ioi (1 : ℝ), L x ^ 2 * (x : ℂ) ^ (z - 1)

def singleC (z : ℂ) : ℂ := ∑' ρ : NontrivialZeros, zeroCoef ρ / (z - ρ)

def Rhat (z : ℂ) : ℂ :=
  (1 - z) * Gamma z * Qcont z - EL z - singleC z - primeSquareCoef / (z - 1 / 2)

def regularError (E : Finset NontrivialZeros) (x : ℝ) : ℂ :=
  2 * residualU E x * R x + 2 * primeSquareCoef * (x : ℂ) ^ (-(1 / 2 : ℂ)) * R x + R x ^ 2

def H (E : Finset NontrivialZeros) (s : ℂ) : ℂ :=
  ∫ x in Ioc (0 : ℝ) 1, regularError E x * (x : ℂ) ^ (s - 1)

def W (E : Finset NontrivialZeros) (s : ℂ) : ℂ :=
  E2 s + primeSquareCoef ^ 2 / (s - 1) + 2 * primeSquareCoef * singleC (s - 1 / 2) +
    2 * (∑ ρ ∈ E, zeroCoef ρ * Rhat (s - ρ)) + H E s

def C (s : ℂ) : ℂ := ∑' p : NontrivialZeros × NontrivialZeros,
  zeroCoef p.1 * zeroCoef p.2 / (s - p.1 - p.2)

def collisionAtom (s : ℂ) : ℂ := ∑' p : Phi2HInf.collisionIdx s,
  zeroCoef p.1.1 * zeroCoef p.1.2

def T0c (E : Finset NontrivialZeros) (s : ℂ) : ℂ := (C s + W E s) / Gamma s

def criticalC (s : ℂ) : ℂ := ∑' p : Phi2HInf.CriticalZero × Phi2HInf.CriticalZero,
  zeroCoef (Phi2HInf.criticalVal p.1) * zeroCoef (Phi2HInf.criticalVal p.2) /
    (s - Phi2HInf.criticalVal p.1 - Phi2HInf.criticalVal p.2)

def criticalAtom (τ : ℝ) : ℂ := ∑' p : Phi2HInf.criticalPairIdx τ,
  zeroCoef (Phi2HInf.criticalVal p.1.1) * zeroCoef (Phi2HInf.criticalVal p.1.2)

def exceptionalC (s : ℂ) : ℂ :=
  ∑' p : {p : NontrivialZeros × NontrivialZeros //
      (p.1 : ℂ).re ≠ 1 / 2 ∨ (p.2 : ℂ).re ≠ 1 / 2},
    zeroCoef p.1.1 * zeroCoef p.1.2 / (s - p.1.1 - p.1.2)

end GoldbachBoundaries.T0HInf
