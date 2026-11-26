import GoldbachBoundaries.PhiR.Defs
import GoldbachBoundaries.Paper2.Defs
import GoldbachBoundaries.Phi2HInf.Defs
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-!
# Natural boundaries for Goldbach series in the residue class one

The boundary theorems assert continuation and the natural boundary under ordinary GRH. The stated analytic inputs
are explicit hypotheses.
-/

noncomputable section

open Complex Filter Set
open scoped Topology

namespace GoldbachBoundaries.ResidueClass

/-- The von Mangoldt weight on the residue class `1 mod q`, extended by zero. -/
def mangoldtOne (q n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod q) n

/-- The binary series over ordered pairs with both entries congruent to one modulo `q`.
The term vanishes if either entry is zero. The initial half-plane is `Re s > 2`. -/
def Phi2 (q : ℕ) (s : ℂ) : ℂ :=
  ∑' mn : ℕ × ℕ, (mangoldtOne q mn.1 : ℂ) * (mangoldtOne q mn.2 : ℂ) *
    ((mn.1 + mn.2 : ℕ) : ℂ) ^ (-s)

/-- The series over ordered `r`-tuples with every entry congruent to one modulo `q`.
The term vanishes if any entry is zero. The initial half-plane is `Re s > r`. -/
def PhiR (q r : ℕ) (s : ℂ) : ℂ :=
  ∑' k : Fin r → ℕ, (∏ i, (mangoldtOne q (k i) : ℂ)) * ((∑ i, k i : ℕ) : ℂ) ^ (-s)

variable {q : ℕ} [NeZero q]

/-- The continued L-function of the primitive character inducing `χ`, at its conductor. -/
def primitiveL (χ : DirichletCharacter ℂ q) : ℂ → ℂ :=
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  χ.primitiveCharacter.LFunction

/-- The distinct zeros of the inducing L-function in the open critical strip. -/
def primitiveZeros (χ : DirichletCharacter ℂ q) : Set ℂ :=
  {ρ | primitiveL χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1}

/-- The analytic order of the inducing L-function at `ρ` as a natural number.
In the open critical strip it is the zero multiplicity, with value zero at regular nonzeros. -/
def primitiveMult (χ : DirichletCharacter ℂ q) (ρ : ℂ) : ℕ :=
  analyticOrderNatAt (primitiveL χ) ρ

/-- Ordinary GRH at modulus `q`. Every zero in the open critical strip of the
primitive L-function inducing any character modulo `q` lies on the critical line.
The principal character contributes the Riemann zeta function. -/
def GRH (q : ℕ) [NeZero q] : Prop :=
  ∀ χ : DirichletCharacter ℂ q, ∀ ρ ∈ primitiveZeros χ, ρ.re = 1 / 2

/-- For nonprincipal characters modulo `q`, the analogue of the paper's (Z3).
At sufficiently large absolute heights, the logarithmic derivative of the
inducing primitive L-function on `0 < Re z ≤ 2` differs from the sum of the
simple fractions over strip zeros within one unit of height by
`O_q(log (2 + |Im z|))`. Each fraction is weighted by the zero's multiplicity.
The bound is uniform over the characters and is asserted away from zeros.

Rüppel (2012), Lemma 1 (6), gives the classical estimate and cites
Montgomery–Vaughan, Lemma 12.6, (12.5). The negative-height estimate follows by conjugating
and pairing the characters. The principal case uses `Paper2.Z3`. -/
def LogDerivPrimitiveLocal (q : ℕ) [NeZero q] : Prop :=
  ∃ C T₀ : ℝ, 0 ≤ C ∧ 2 ≤ T₀ ∧
    ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ∀ z : ℂ, 0 < z.re → z.re ≤ 2 → T₀ ≤ |z.im| → primitiveL χ z ≠ 0 →
        ‖deriv (primitiveL χ) z / primitiveL χ z -
          ∑ᶠ ρ ∈ {ρ ∈ primitiveZeros χ | |ρ.im - z.im| ≤ 1},
            (primitiveMult χ ρ : ℂ) / (z - ρ)‖ ≤ C * Real.log (2 + |z.im|)

end GoldbachBoundaries.ResidueClass
