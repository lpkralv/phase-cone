import GoldbachBoundaries.Paper2.M3.Real
import GoldbachBoundaries.Paper2.M3.Fill.Mcal_eq_formula
import GoldbachBoundaries.Paper2.M3.Fill.analyticAt_Mform_of_eq_T
import GoldbachBoundaries.Paper2.M3.Fill.hasResidue_two_of_codiscrete
import GoldbachBoundaries.Paper2.M3.Fill.integrableOn_Theta_Ioi
import GoldbachBoundaries.Paper2.M3.Fill.integrableOn_hErr_sq_cpow_of_mem
import GoldbachBoundaries.Paper2.M3.Fill.mem_mellinConvSet_of_two_lt
import GoldbachBoundaries.Paper2.M3.Fill.meromorphicOn_Mform
import GoldbachBoundaries.Paper2.M3.Fill.order_residue_of_tendsto_ofReal
import GoldbachBoundaries.Paper2.M3.Fill.tendsto_mul_Theta
import GoldbachBoundaries.Paper2.M3.Fill.tendsto_sub_two_mul_Gamma_T
import GoldbachBoundaries.Paper2.M3.Fill.tendsto_sub_two_mul_Mcal

/-!
# M3: the Mellin transform of `h²` (`nr:lem:hsq`)

Unconditional; (ii) uses the prime number theorem `θ(x) ~ x`, which PNT+ proves sorry-free (`chebyshev_asymptotic`,
`PrimeNumberTheoremAnd/Consequences.lean`, built here).

(i) is paper 1's `TIdentity` library under other names (`Theta = Fw`, `Mcal = Rr`, `Ecal = E2`, `ecal = e1`,
definitionally): `Gamma_mul_T_eq_split` (`Γ(s)T(s) = 1/(s-2) + 2m₁(s-1) + R(s) + E(s)`, `σ > 2`) and
`Gamma_mul_Q_eq_split` at `z = s - 1` (`Γ(z)Q(z) = 1/(z-1) + m₁(z) + e(z)`, `Re z > 1`) eliminate `m₁` and give
`(nr:eq:hsq)` (`Mcal_eq_formula`, a real proof). `differentiable_E2`, `differentiable_e1` are the entireness.

(ii) `tΘ(t) → 1` from `θ(x) ~ x` by Abel summation; then `(s-2)𝓜(s) → 0` as `s ↓ 2`, and `(nr:eq:hsq)` times `s - 2`
gives `(s-2)Γ(s)T(s) → 0 + 2 - 1 = 1`. A meromorphic `f` near `2` equal to `T` off a discrete subset of the right half
of a disc equals `T` on a right half-disc (identity theorem: both are analytic on the connected punctured right
half-disc), so `(x-2)f(x) → 1` along real `x ↓ 2`, which forces a simple pole with residue `1`.

The target `lem_hsq_proof` is at the end of this file (`Mellin.lean` and `Test.lean` use it). `Mform_eq_Mcal` and
`analyticAt_Mform_of_eq_T` relate `Mform F` to `𝓜` on `σ > 2`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M3

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-! ## Real lemmas -/

/-- `Mform F = 𝓜` at a point of `σ > 2` where `F` takes the value of the series `T`. -/
theorem Mform_eq_Mcal {F : ℂ → ℂ} {s : ℂ} (hs : 2 < s.re) (hF : F s = T s) : Mform F s = Mcal s := by
  have hQ : Qcont (s - 1) = Q (s - 1) := TIdentity.Qcont_eq_Q_of_one_lt (by simp; linarith)
  rw [Mcal_eq_formula hs, Mform, hF, hQ]

/-! ## Target: `lem_hsq` -/

/-- `lem_hsq` of `Paper2/Statements.lean`, statement verbatim. -/
theorem lem_hsq_proof :
    (Differentiable ℂ Ecal ∧ Differentiable ℂ ecal ∧
      (∀ s : ℂ, IntegrableOn (fun t : ℝ => ((Theta t ^ 2 : ℝ) : ℂ) * (t : ℂ) ^ (s - 1)) (Ioi (1 : ℝ))) ∧
      (∀ z : ℂ, IntegrableOn (fun t : ℝ => (Theta t : ℂ) * (t : ℂ) ^ (z - 1)) (Ioi (1 : ℝ))) ∧
      ∀ s : ℂ, 2 < s.re →
        IntegrableOn (fun t : ℝ => ((hErr t ^ 2 : ℝ) : ℂ) * (t : ℂ) ^ (s - 1)) (Ioc (0 : ℝ) 1) ∧
        Mcal s = Gamma s * T s - 2 * Gamma (s - 1) * Q (s - 1) + 1 / (s - 2) - Ecal s +
          2 * ecal (s - 1)) ∧
    (Tendsto (fun t : ℝ => t * Theta t) (𝓝[>] 0) (𝓝 1) ∧
      Tendsto (fun x : ℝ => ((x : ℂ) - 2) * Gamma x * T x) (𝓝[>] 2) (𝓝 1) ∧
      ∀ (f : ℂ → ℂ) (r : ℝ), 0 < r → MeromorphicOn f (ball 2 r) →
        f =ᶠ[codiscreteWithin (ball 2 r ∩ halfPlane 2)] T →
        meromorphicOrderAt f 2 = -1 ∧ HasResidue f 2 1) := by
  refine ⟨⟨?_, ?_, integrableOn_Theta_Ioi.1, integrableOn_Theta_Ioi.2, fun s hs =>
    ⟨integrableOn_hErr_sq_cpow_of_mem (mem_mellinConvSet_of_two_lt hs), Mcal_eq_formula hs⟩⟩,
    ⟨tendsto_mul_Theta, tendsto_sub_two_mul_Gamma_T, hasResidue_two_of_codiscrete⟩⟩
  · rw [Ecal_eq_E2]
    exact TIdentity.differentiable_E2
  · rw [ecal_eq_e1]
    exact TIdentity.differentiable_e1

end GoldbachBoundaries.Paper2.M3
