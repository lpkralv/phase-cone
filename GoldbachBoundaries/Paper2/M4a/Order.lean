import GoldbachBoundaries.Paper2.M4a.H2log
import GoldbachBoundaries.Paper2.M4a.Fill.isBigO_integral_param
import GoldbachBoundaries.Paper2.M4a.Fill.isBigO_Jseg_kr_one_b
import GoldbachBoundaries.Paper2.M4a.Fill.isBigO_Jseg_kr_b_one
import GoldbachBoundaries.Paper2.M4a.Fill.isBigO_Jseg_k0_one_one
import GoldbachBoundaries.Paper2.M4a.Fill.exists_ne_zero_of_isBigO_pow

/-!
# M4a: the order of `X_α` for the kernels `k₀` and `k_r` (`cl:rem:order`, now `cl:prop:order`)

`L(s) = s`, `k_r(z, s) = K_s(z)((z - 1)(s - 1 - z))^r`, `k₁ = k₀`. At `α = 1 + b`, `δ = s - α`:
`J_{1b}(α + δ) = δ ∫_0^1 k_r(1 + tδ, α + δ) dt = δ^{r+1} ∫_0^1 t^r ψ₁(tδ, δ) dt` with
`ψ₁(u, δ) = K_{α+δ}(1 + u)(b - 1 + δ - u)^r`, and `J_{b1}(α + δ) = δ^{r+1} ∫_0^1 (1 - t)^r ψ₂(tδ, δ) dt` with
`ψ₂(u, δ) = K_{α+δ}(b + u)(b - 1 + u)^r`. Both `ψ`'s are holomorphic near `0 ∈ ℂ²` (the `Γ` arguments are near `1`,
`b`, `1 + b`, all with positive real part) with `ψ₁(0) = ψ₂(0) = (b - 1)^r/b` (`K_{1+b}(1) = K_{1+b}(b) = Γ(b)/Γ(1 + b)`).
One general lemma (`isBigO_integral_param`) turns "holomorphic at `0`" into "`∫ w(t)ψ(tδ, δ) dt = ψ(0)∫w + O(δ)`";
the paper's route through the symmetry `J_{b1} = J_{1b}` is not needed. At `α = 2` for `k₀`:
`J_{11}(2 + δ) = δ³∫_0^1 t(1 - t) K_{2+δ}(1 + tδ) dt = δ³/6 + O(δ⁴)`.

The constants used below are `J_{1b}/δ^{r+1}` and
`J_{b1}/δ^{r+1}` against `(b-1)^r/(b(r+1))` for `b = 1/2, 1/6, 1/2 + 14.1347…i`, `r = 0, …, 3`, `δ = 10⁻³` and
`10⁻⁴(1 + i)`: relative error `O(|δ|)` in every case; `J_{11}/(δ³/6)` likewise.

The targets `rem_order_kr_coeff_proof`, `rem_order_coeff_proof` are at the end of the file (`H3.lean` uses the second).
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M4a

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-! ## Lemmas

Proved in `Fill/`, one file per lemma (same name, same statement): `isBigO_integral_param`, `isBigO_Jseg_kr_one_b`, `isBigO_Jseg_kr_b_one`, `isBigO_Jseg_k0_one_one`, `exists_ne_zero_of_isBigO_pow`. -/

/-! ## Targets -/

/-- `rem_order_kr_coeff` of `Paper2/Statements.lean`, statement verbatim. -/
theorem rem_order_kr_coeff_proof (hRH : RiemannHypothesis) (r : ℕ) (hr : 1 ≤ r) :
    ∀ b ∈ PoleSetQ \ {1},
      (fun s => Xcoef Aff.idL (kr r) (1 + b) s -
          2 * cP 1 * cP b * (b - 1) ^ r / (b * ((r : ℂ) + 1)) * (s - (1 + b)) ^ (r + 1)) =O[𝓝 (1 + b)]
        fun s => (s - (1 + b)) ^ (r + 2) := by
  have _ := hRH  -- RH (choice 1) is not used: the expansion holds for every `b ∈ Σ ∖ {1}`
  have _ := hr   -- the expansion holds for every `r`; the statement asks `r ≥ 1`
  rintro b ⟨hb, hb1⟩
  have hb1' : Aff.idL.app (1 + b) - 1 ≠ 1 := by rw [app_idL]; simpa using hb1
  have happ : Aff.idL.app (1 + b) - 1 = b := by rw [app_idL]; ring
  rw [Xcoef_of_ne Aff.idL (kr r) hb1', happ]
  refine ((isBigO_Jseg_kr_one_b r hb).add (isBigO_Jseg_kr_b_one r hb)).const_mul_left (cP 1 * cP b)
    |>.congr_left fun s => ?_
  ring

/-- `rem_order_coeff` of `Paper2/Statements.lean`, statement verbatim. -/
theorem rem_order_coeff_proof (hRH : RiemannHypothesis) :
    (∀ b ∈ PoleSetQ \ {1},
      (fun s => Xcoef Aff.idL k0 (1 + b) s - cP 1 * cP b * ((b - 1) / b) * (s - (1 + b)) ^ 2) =O[𝓝 (1 + b)]
        fun s => (s - (1 + b)) ^ 3) ∧
    (fun s => Xcoef Aff.idL k0 2 s - (s - 2) ^ 3 / 6) =O[𝓝 2] fun s => (s - 2) ^ 4 := by
  refine ⟨fun b hb => ?_, ?_⟩
  · have h := rem_order_kr_coeff_proof hRH 1 le_rfl b hb
    rw [kr_one'] at h
    have hb0 : b ≠ 0 := fun h => by
      have := (poleSetQ_re_bounds hb.1).1; rw [h] at this; simp at this
    refine h.congr_left fun s => ?_
    push_cast
    field_simp
    ring
  · have h2 : Aff.idL.app 2 - 1 = 1 := by rw [app_idL]; norm_num
    rw [Xcoef_of_eq Aff.idL k0 h2]
    exact isBigO_Jseg_k0_one_one

end GoldbachBoundaries.Paper2.M4a
