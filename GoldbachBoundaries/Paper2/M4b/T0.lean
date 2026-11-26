import GoldbachBoundaries.Paper2.M4b.ExG
import GoldbachBoundaries.Paper2.M4b.Fill.hypR_k0
import GoldbachBoundaries.Paper2.M4b.Fill.exists_T0_ne_zero
import GoldbachBoundaries.Paper2.M4b.Fill.filter_series_aux
import GoldbachBoundaries.Paper2.M4b.Fill.im_DH_eq_zero

/-!
# M4b: `T₀` (`cl:prop:T0`) and `D_H` as a double prime series (the first remark after `cl:thm:filter`)

`W₀ = (1 - s)(p+q)^{-s} + s(s+1)pq(p+q)^{-s-2}` and `W_H = ∑ h_{ij}Γ(s+i+j)/Γ(s) p^iq^j(p+q)^{-s-i-j}` are rising
combinations (`Rising.lean`), so (R) for `T₀`, `G₀` and `D_H` (all but reality for complex `H`) is
`rising_summable_eq` and `rising_differentiableOn`, with the kernels `k₀ = krise 2 cW0` and `k_H = krise N (cWH h)` on
the lines used (`W0_k0_rising`, `kH_eq_krise`). `T₀` is holomorphic on `ℍ` by Theorem E(ii) (`thm_mero_ii_proof`,
`𝔟₀ ≡ 0`). Reality of `D_H` for real coefficients is read off the integral `(cl:eq:DH)` on the symmetric line
`c = x/2` (`im_DH_eq_zero`), which avoids proving that the rising-factorial coefficients `h_{ij}` are real.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M4b

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-! ## Lemmas

Proved in `Fill/`, one file per lemma (same name, same statement): `hypR_k0`, `exists_T0_ne_zero`, `filter_series_aux`, `im_DH_eq_zero`. -/

/-! ## Targets -/

/-- `prop_T0` of `Paper2/Statements.lean`, statement verbatim. -/
theorem prop_T0_proof (hRH : RiemannHypothesis) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6) :
    K1 Aff.idL k0 ∧ K2 Aff.idL k0 ∧ K3 Aff.idL k0 ∧ K4 k0 ∧ HypR Aff.idL k0 W0log Q ∧
      HypR Aff.idL k0 W0 P ∧ (∀ s, bracket Aff.idL k0 s = 0) ∧
      (∃ F : ℂ → ℂ, DifferentiableOn ℂ F HH ∧ EqOn F T0 (halfPlane 2)) ∧
      ∃ s : ℂ, 2 < s.re ∧ T0 s ≠ 0 := by
  obtain ⟨hRlog, hRP⟩ := hypR_k0
  obtain ⟨F, hF, hFeq⟩ := thm_mero_ii_proof hRH hZ1 hZ2 hZ3 Aff.idL k0 W0log k0_K1 (k0_K2 hZ6) hRlog
    (fun s _ => k0_bracket s)
  refine ⟨k0_K1, k0_K2 hZ6, k0_K3, K4_kernels.2.2.2, hRlog, hRP, k0_bracket, ⟨F, ?_, ?_⟩,
    exists_T0_ne_zero⟩
  · rwa [idL_HL_eq] at hF
  · rw [idL_RL_eq] at hFeq
    exact hFeq

/-- `filter_series` of `Paper2/Statements.lean`, statement verbatim. -/
theorem filter_series_proof (hRH : RiemannHypothesis) (hZ6 : Z6)
    (H : MvPolynomial (Fin 2) ℂ) (hH0 : H ≠ 0) (hHs : ∀ z w, evalH H z w = evalH H w z)
    (hH1 : ∀ w, evalH H 1 w = 0) (N : ℕ) (h : ℕ → ℕ → ℂ) (hrep : IsRisingRep H N h) :
    (∀ s : ℂ, 2 < s.re →
      Summable fun pq : Nat.Primes × Nat.Primes => ‖WHlog N h s (pq.1 : ℕ) (pq.2 : ℕ)‖) ∧
    (∀ s : ℂ, 2 < s.re → DH H s = Dser (WHlog N h) s) ∧
    DifferentiableOn ℂ (Dser (WHlog N h)) (halfPlane 2) ∧
    ∀ s ∈ Aff.idL.RL ∩ Aff.idL.DL, ∀ c : ℝ, 1 < c → c < (Aff.idL.app s).re - 1 →
      Dser (WHlog N h) s = VerticalIntegral' (fun z => kH H z s * Q z * Q (Aff.idL.app s - z)) c := by
  have _ := hRH  -- RH (choice 1) is not used
  have _ := hZ6  -- (Z6) is not used: the kernels' integrability on lines is M1's polynomial `Γ` decay
  have _ := hH0  -- the paper's conditions on `H` are context (review choice 33)
  have _ := hHs
  have _ := hH1
  exact filter_series_aux hrep

/-- `filter_series_real` of `Paper2/Statements.lean`, statement verbatim. -/
theorem filter_series_real_proof (hRH : RiemannHypothesis) (hZ6 : Z6)
    (H : MvPolynomial (Fin 2) ℂ) (hH0 : H ≠ 0) (hHs : ∀ z w, evalH H z w = evalH H w z)
    (hH1 : ∀ w, evalH H 1 w = 0) (hreal : ∀ m, (H.coeff m).im = 0) (N : ℕ) (h : ℕ → ℕ → ℂ)
    (hrep : IsRisingRep H N h) :
    HypR Aff.idL (kH H) (WHlog N h) Q ∧ ∀ x : ℝ, 2 < x → (DH H x).im = 0 := by
  have _ := hRH  -- RH (choice 1) is not used
  have _ := hZ6  -- (Z6) is not used, as in `filter_series_proof`
  have _ := hH0  -- the paper's conditions on `H` are context (review choice 33)
  have _ := hHs
  have _ := hH1
  obtain ⟨h1, h2, h3, h4⟩ := filter_series_aux hrep
  refine ⟨⟨fun s hs => h1 s (by rw [idL_RL_eq] at hs; exact hs), by rw [idL_RL_eq]; exact h3,
    fun x hx => ?_, h4⟩, im_DH_eq_zero hreal⟩
  have hx' : 2 < x := by
    rw [idL_RL_eq] at hx
    simpa [halfPlane] using hx
  rw [← h2 x (by simpa using hx')]
  exact im_DH_eq_zero hreal x hx'

end GoldbachBoundaries.Paper2.M4b
