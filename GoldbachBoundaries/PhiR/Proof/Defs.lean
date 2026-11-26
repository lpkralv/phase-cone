import GoldbachBoundaries.PhiR.Defs
import GoldbachBoundaries.Phi2.Proof.Defs

/-!
Junk values: Bochner integrals are `0` when not integrable, `x/0 = 0`, `Γ` is junk at its poles. Every lemma that
evaluates these at a point states (or its hypotheses imply) integrability there; the poles of `Γ(s-r+1)` (at
`s = r-1, r-2, …`) and of `1/(s-r)` are where `PhiRc` is a meromorphic, not a pointwise, object.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory

namespace GoldbachBoundaries.PhiRProof

open GoldbachBoundaries GoldbachBoundaries.Phi2Proof

 

/-- `C(r,2) = r(r-1)/2`, the coefficient of `Φ₂`. -/
def cC (r : ℕ) : ℝ := (r : ℝ) * ((r : ℝ) - 1) / 2

/-- `B_r = -r(r-2)`, the coefficient of `M = ψ`. -/
def cB (r : ℕ) : ℝ := -((r : ℝ) * ((r : ℝ) - 2))

/-- `A_r = (r-1)(r-2)/2`, the coefficient of `x^{-r}`. -/
def cA (r : ℕ) : ℝ := ((r : ℝ) - 1) * ((r : ℝ) - 2) / 2

/-! ## The Mellin side -/

/-- `Q_r(t) = FL^r - C(r,2) t^{-(r-2)} FL² - B_r t^{-(r-1)} FL - A_r t^{-r}` (Sol's eq. (10)). Meaningful for `t > 0`
and `r ≥ 2` (natural-number exponents `r - 2`, `r - 1`). -/
def QR (r : ℕ) (t : ℝ) : ℝ :=
  FL t ^ r - cC r * FL t ^ 2 / t ^ (r - 2) - cB r * FL t / t ^ (r - 1) - cA r / t ^ r

/-- `J_r(s) = ∫_0^1 Q_r(t) t^{s-1} dt` (holomorphic on `σ > r - 3/2` under RH). -/
def JR (r : ℕ) (s : ℂ) : ℂ := ∫ t in Ioc (0 : ℝ) 1, (QR r t : ℂ) * (t : ℂ) ^ (s - 1)

/-- `E_r(s) = ∫_1^∞ FL(t)^r t^{s-1} dt` (entire). -/
def ER (r : ℕ) (s : ℂ) : ℂ := ∫ t in Ioi (1 : ℝ), ((FL t ^ r : ℝ) : ℂ) * (t : ℂ) ^ (s - 1)

/-- `K_r(s) = J_r(s) + E_r(s) - C(r,2) E₂(s-r+2) - B_r e₁(s-r+1)` (Sol's eq. (12)). -/
def KR (r : ℕ) (s : ℂ) : ℂ :=
  JR r s + ER r s - (cC r : ℂ) * E2L (s - r + 2) - (cB r : ℂ) * e1L (s - r + 1)

/-! ## The continuation of `Φ_r` to `σ > r - 1` -/

/-- `f₄(s) = C(r,2) Γ(s-r+2)/Γ(s)`, the coefficient of `Φ₂(s-r+2)` (`= C(r,2)/P_{r-2}(s)`). -/
def phiRCoef (r : ℕ) (s : ℂ) : ℂ := (cC r : ℂ) * Gamma (s - r + 2) * (Gamma s)⁻¹

/-- The rest of eq. (12) divided by `Γ(s)`: `(B_r Γ(s-r+1) ψ(s-r+1) + A_r/(s-r) + K_r(s))/Γ(s)`. Meromorphic on
`σ > r - 3/2` under RH (`meromorphicOn_phiRRest`). -/
def phiRRest (r : ℕ) (s : ℂ) : ℂ :=
  ((cB r : ℂ) * Gamma (s - r + 1) * negLogDerivZeta (s - r + 1) + (cA r : ℂ) / (s - r) + KR r s) *
    (Gamma s)⁻¹

/-- The continuation of `Φ_r` to `σ > r - 1`: `f₄(s) Φ₂c(s-r+2) + rest(s)` (junk at the poles, which no statement
reads). -/
def PhiRc (r : ℕ) (s : ℂ) : ℂ := phiRCoef r s * Phi2c (s - r + 2) + phiRRest r s

 

/-- Sol's `R_r` (eq. (13)) before removing the singularity at `s = r`:
`K_r(s)/Γ(s) + A_r (1/(Γ(s)(s-r)) - ζ(s-r+1)/(r-1)!)`. -/
def RRraw (r : ℕ) (s : ℂ) : ℂ :=
  KR r s * (Gamma s)⁻¹ +
    (cA r : ℂ) * ((Gamma s)⁻¹ / (s - r) - riemannZeta (s - r + 1) / ((r - 1).factorial : ℂ))

end GoldbachBoundaries.PhiRProof
