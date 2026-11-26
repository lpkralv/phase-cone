import GoldbachBoundaries.Defs

/-!
# Phi2HInf: the one new named premise for the `Φ₂`/`Φ_r` natural boundary under `(H_∞)`

The `(H_∞)` development of `Φ₂` reuses every classical premise of the RH development as a named `Prop` of
`Paper2/Defs.lean`: `Hinf` (the hypothesis itself), `Z1` (reflection/conjugation symmetry of the zeros, which under RH
was free as `Z1_of_RH` but is a genuine input here), `Z2` (Riemann–von Mangoldt window count), `Z3` (local expansion of
`ζ'/ζ`), and `ZLittlewood` (the gap theorem). See the plan for the exact map.
-/

noncomputable section

open Complex Filter Topology Set Metric

namespace GoldbachBoundaries.Phi2HInf

/--
**(Stir)**, the uniform sectorial Stirling expansion of `Γ` on a vertical strip, in relative-error form
([DLMF 5.11.3], §5.11(i)): for `x₁ ≤ Re z ≤ x₂` and `|Im z|` large,
`Γ(z) = exp((z - ½) Log z − z + ½ log 2π) · (1 + O(1 / |Im z|))`, uniformly.
-/
def StirlingStrip : Prop :=
  ∀ x₁ x₂ : ℝ, x₁ ≤ x₂ → ∃ C T₀ : ℝ, 0 ≤ C ∧
    ∀ z : ℂ, x₁ ≤ z.re → z.re ≤ x₂ → T₀ ≤ |z.im| →
      ‖Complex.Gamma z -
          Complex.exp ((z - 1 / 2) * Complex.log z - z + (1 / 2) * Complex.log (2 * (Real.pi : ℂ)))‖ ≤
        C / |z.im| *
          ‖Complex.exp ((z - 1 / 2) * Complex.log z - z + (1 / 2) * Complex.log (2 * (Real.pi : ℂ)))‖

end GoldbachBoundaries.Phi2HInf
