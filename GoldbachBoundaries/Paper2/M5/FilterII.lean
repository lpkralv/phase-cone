import GoldbachBoundaries.Paper2.M5.FilterI
import GoldbachBoundaries.Paper2.M5.Fill.«rectangleIntegral'_eq_sum_of_simplePoles_rect»
import GoldbachBoundaries.Paper2.M5.Fill.filter_rect
import GoldbachBoundaries.Paper2.M5.Fill.filter_rect_limit
import GoldbachBoundaries.Paper2.M5.Fill.summable_zeros_inv_sq
import GoldbachBoundaries.Paper2.M5.Fill.norm_resTerm_le
import GoldbachBoundaries.Paper2.M5.Fill.filter_shift
import GoldbachBoundaries.Paper2.M5.Fill.differentiableOn_Jfil
import GoldbachBoundaries.Paper2.M5.Fill.tendsto_eta_resTerm
import GoldbachBoundaries.Paper2.M5.Fill.tendsto_eta_midTerm
import GoldbachBoundaries.Paper2.M5.Fill.tendsto_eta_Fil
import GoldbachBoundaries.Paper2.M5.Fill.CH_eq_tsum_limTerm
import GoldbachBoundaries.Paper2.M5.Fill.eqOn_DH_H0f_of_T0

/-!
# M5: Theorem F (ii) (`cl:thm:filter`(ii)): the blow-up `η D_H(s₀ + η) → C_H(τ₀)` on the line

The paper's Steps 1-3, made explicit, for `s = s₀ + η`, `s₀ = 1 + iτ₀`, `0 < η ≤ 1/4`.

* **Step 1** (`filter_shift`). `Fil H s` is the integral on `Re z = σ/2 = (1 + η)/2 ∈ (1/2, 1/2 + η)`, the paper's `c`. Move
  it to `Re z = 2/5` (`J`, `Jfil`): the poles of `gH` in between are `1/2` and the zeros `ρ` (`poleSetQ_re_cases`), with
  residues `midTerm` and `resTerm`. There are infinitely many, so the residue theorem is applied to rectangles of height
  `Y'`, the good heights of `cl:lem:Qleft`(ii) (`filter_rect`, through a rectangle form of the residue theorem with
  holomorphy on the rectangle only, `rectangleIntegral'_eq_sum_of_simplePoles_rect`), and `Y' → ∞`
  (`filter_rect_limit`: horizontal sides `→ 0` by `cl:lem:Qleft`(ii) and the kernel's decay).
* **Step 2** (`norm_resTerm_le`). `|η resTerm(s, ρ)| ≤ μ_ρ = C(1 + |γ|)^{-2}` uniformly in `η`, by `cl:lem:Qleft`(iii),
  M1's polynomial decay of `K_s(ρ)` (the paper uses (Z6); polynomial decay suffices), `m(ρ) ≪ log` (M2's `zetaMult_le_log`),
  and `∑_ρ (1 + |γ|)^{-2} < ∞` (`summable_zeros_inv_sq`, (Z2)).
* **Step 3** (`tendsto_eta_Fil`). `η J(s) → 0` (`J` is holomorphic near `s₀`, `differentiableOn_Jfil`), `η midTerm → midLim`
  (`0` for `τ₀ ≠ 0`), and termwise `η resTerm(s, ρ) → limTerm(ρ)` (`tendsto_eta_resTerm`), summed by dominated convergence.
  `∑ limTerm = C_H(τ₀)` is a reindexing (`CH_eq_tsum_limTerm`).

`η ↦ ...` is a function of real `η`, and `𝓝[>] 0` is the paper's `η ↓ 0`. No (Z6): every kernel bound is M1's.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-! ## Lemmas: Step 1

Proved in `Fill/`, one file per lemma (same name, same statement): `rectangleIntegral'_eq_sum_of_simplePoles_rect`, `filter_rect`, `filter_rect_limit`. -/

/-! ## Lemmas: Step 2

Proved in `Fill/`, one file per lemma (same name, same statement): `summable_zeros_inv_sq`, `norm_resTerm_le`, `filter_shift`. -/

/-! ## Lemmas: Step 3

Proved in `Fill/`, one file per lemma (same name, same statement): `differentiableOn_Jfil`, `tendsto_eta_resTerm`, `tendsto_eta_midTerm`, `tendsto_eta_Fil`, `CH_eq_tsum_limTerm`, `eqOn_DH_H0f_of_T0`. -/

/-! ## Target -/

/-- `thm_filter_ii` of `Paper2/Statements.lean`, statement verbatim. -/
theorem thm_filter_ii_proof (hRH : RiemannHypothesis) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6)
    (H : MvPolynomial (Fin 2) ℂ) (hH0 : H ≠ 0) (hHs : ∀ z w, evalH H z w = evalH H w z)
    (hH1 : ∀ w, evalH H 1 w = 0) {τ₀ : ℝ} (hτ0 : τ₀ ≠ 0) (hτ : ∀ ρ ∈ NontrivialZeros, ρ.im ≠ τ₀)
    (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F HH) (hFD : EqOn F (DH H) (halfPlane 2)) :
    Summable (CHterm H τ₀) ∧
      Tendsto (fun η : ℝ => (η : ℂ) * F (1 + τ₀ * I + η)) (𝓝[>] 0) (𝓝 (CH H τ₀)) := by
  have _ := hZ6  -- (Z6) is not used: M1's polynomial `Γ` decay bounds the kernel
  have _ := hH0  -- `H ≠ 0` is not used in (ii)
  have hEq := eqOn_Fil_of_DH hRH H hHs hH1 hF hFD
  obtain ⟨hsum, hlim⟩ := tendsto_eta_Fil hRH hZ1 hZ2 hZ3 H hHs hH1 hτ
  obtain ⟨hCHs, hCH⟩ := CH_eq_tsum_limTerm hRH hZ1 H hsum
  have hmid : midLim H τ₀ = 0 := by
    unfold midLim
    exact ite_eq_right hτ0
  rw [hmid, zero_add, ← hCH] at hlim
  refine ⟨hCHs, hlim.congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with η hη
  have hη' : (0 : ℝ) < η := hη
  have hmem : (1 + τ₀ * I + η : ℂ) ∈ HH := by
    show (1 : ℝ) < (1 + τ₀ * I + η : ℂ).re
    simp only [add_re, one_re, mul_re, ofReal_re, ofReal_im, I_re, I_im, mul_zero, mul_one, sub_zero, add_zero]
    linarith
  rw [hEq hmem]

end GoldbachBoundaries.Paper2.M5
