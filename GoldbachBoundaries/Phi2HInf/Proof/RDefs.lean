import GoldbachBoundaries.Phi2HInf.Proof.M1Regularization
import GoldbachBoundaries.PhiR.Proof.M3Boundary

/-! Item 40 §§3–5: finite exceptional subtraction for the higher-fold series.
The recursive finite transform enumerates ordered tuples, with repetitions.
All functions here are explicit; no choice of a meromorphic continuation occurs. -/
noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
namespace GoldbachBoundaries.Phi2HInf
open GoldbachBoundaries Paper2 Phi2Proof PhiRProof

def rCutoff : ℝ := 1 / 2 + (1 - Bsup) / 6
def rMargin : ℝ := (1 - Bsup) / 2
def rAbscissa (r : ℕ) : ℝ := (r : ℝ) - 1 - rMargin

/-- The finite exceptional exponential polynomial, with the explicit-formula minus sign. -/
def exceptionalE (E : Finset NontrivialZeros) (x : ℝ) : ℂ :=
  ∑ ρ ∈ E, -zeroCoef ρ * (x : ℂ) ^ (-(ρ : ℂ))

def residualG (E : Finset NontrivialZeros) (x : ℝ) : ℂ := (hL x : ℂ) - exceptionalE E x

/-- Equation (11). Pointwise Mellin identities below are restricted to Re z > 1. -/
def Gb (E : Finset NontrivialZeros) (z : ℂ) : ℂ :=
  Gamma z * negLogDerivZeta z - e1L z - 1 / (z - 1) -
    ∑ ρ ∈ E, -zeroCoef ρ / (z - ρ)

/-- Applying this operator n times expands over E^n, without an extra factorial. -/
def exceptionalTransform (E : Finset NontrivialZeros) : ℕ → (ℂ → ℂ) → ℂ → ℂ
  | 0, f, z => f z
  | n + 1, f, z => ∑ ρ ∈ E, -zeroCoef ρ * exceptionalTransform E n f (z - ρ)

def PrFun (E : Finset NontrivialZeros) (r : ℕ) (x : ℝ) : ℂ :=
  ∑ k ∈ Finset.Ico 3 (r + 1), (r.choose k : ℂ) * (1 / (x : ℂ)) ^ (r - k) *
    (exceptionalE E x ^ k + (k : ℂ) * exceptionalE E x ^ (k - 1) * residualG E x)

def RrFun (E : Finset NontrivialZeros) (r : ℕ) (x : ℝ) : ℂ :=
  ∑ k ∈ Finset.Ico 3 (r + 1), (r.choose k : ℂ) * (1 / (x : ℂ)) ^ (r - k) *
    ∑ j ∈ Finset.Ico 2 (k + 1), (k.choose j : ℂ) *
      exceptionalE E x ^ (k - j) * residualG E x ^ j

/-- The finite globally meromorphic expression (15). -/
def Pr (E : Finset NontrivialZeros) (r : ℕ) (s : ℂ) : ℂ :=
  ∑ k ∈ Finset.Ico 3 (r + 1), (r.choose k : ℂ) *
    (exceptionalTransform E k (fun z => 1 / z) (s - r + k) +
      (k : ℂ) * exceptionalTransform E (k - 1) (Gb E) (s - r + k))

def Hr (E : Finset NontrivialZeros) (r : ℕ) (s : ℂ) : ℂ :=
  ∫ x in Ioc (0 : ℝ) 1, RrFun E r x * (x : ℂ) ^ (s - 1)

/-- Equation (23), retaining all finite exceptional poles. -/
def Mr (E : Finset NontrivialZeros) (r : ℕ) (s : ℂ) : ℂ :=
  ((cB r : ℂ) * Gamma (s - r + 1) * negLogDerivZeta (s - r + 1) +
    (cA r : ℂ) / (s - r) + ER r s - (cC r : ℂ) * E2L (s - r + 2) -
    (cB r : ℂ) * e1L (s - r + 1) + Pr E r s) * (Gamma s)⁻¹

def phiRRestHInf (E : Finset NontrivialZeros) (r : ℕ) (s : ℂ) : ℂ :=
  Mr E r s + Hr E r s * (Gamma s)⁻¹

def PhiRcHInf (E : Finset NontrivialZeros) (r : ℕ) (s : ℂ) : ℂ :=
  phiRCoef r s * Phi2cHInf (s - r + 2) + phiRRestHInf E r s

end GoldbachBoundaries.Phi2HInf
