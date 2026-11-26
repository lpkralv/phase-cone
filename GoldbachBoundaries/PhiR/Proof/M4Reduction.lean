import GoldbachBoundaries.PhiR.Proof.M2Continuation
import GoldbachBoundaries.PhiR.Fill.PhiR_eq_explicit
import GoldbachBoundaries.PhiR.Fill.exists_RR
import GoldbachBoundaries.PhiR.Fill.RR_bounded_halfStrip

/-!
Lemmas proved in `Fill/`: `PhiR_eq_explicit`, `exists_RR`, `RR_bounded_halfStrip`. Real proof: `Gamma_sub_mul_polyP`.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics

namespace GoldbachBoundaries.PhiRProof

open GoldbachBoundaries GoldbachBoundaries.Phi2Proof

/-- **`Γ(s - j) P_j(s) = Γ(s)`** for `Re s > j` (real proof, induction on `j` with `Γ(z + 1) = z Γ(z)`). -/
theorem Gamma_sub_mul_polyP (j : ℕ) {s : ℂ} (hs : (j : ℝ) < s.re) : Gamma (s - j) * polyP j s = Gamma s := by
  induction j with
  | zero => simp [polyP]
  | succ j ih =>
    have hs' : (j : ℝ) < s.re := by push_cast at hs; linarith
    have hne : s - ((j + 1 : ℕ) : ℂ) ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      push_cast at hs
      linarith
    have hΓ : Gamma (s - (j : ℂ)) = (s - ((j + 1 : ℕ) : ℂ)) * Gamma (s - ((j + 1 : ℕ) : ℂ)) := by
      have h := Complex.Gamma_add_one (s - ((j + 1 : ℕ) : ℂ)) hne
      rw [show s - ((j + 1 : ℕ) : ℂ) + 1 = s - (j : ℂ) by push_cast; ring] at h
      exact h
    rw [polyP, Finset.prod_Icc_succ_top (by omega), ← polyP]
    calc Gamma (s - ((j + 1 : ℕ) : ℂ)) * (polyP j s * (s - ((j + 1 : ℕ) : ℂ)))
        = Gamma (s - (j : ℂ)) * polyP j s := by rw [hΓ]; ring
      _ = Gamma s := ih hs'



theorem PhiR_eq_explicit {r : ℕ} (hr : 2 ≤ r) {s : ℂ} (hs : (r : ℝ) < s.re) :
    PhiR r s = ((r : ℂ) - 1) * ((r : ℂ) - 2) / 2 / ((r - 1).factorial : ℂ) * riemannZeta (s - r + 1) +
      (r : ℂ) * ((r : ℂ) - 2) / polyP (r - 1) s *
        (deriv riemannZeta (s - r + 1) / riemannZeta (s - r + 1)) +
      ((r.choose 2 : ℕ) : ℂ) / polyP (r - 2) s * Phi2 (s - r + 2) + RRraw r s :=
  FillC.PhiR_eq_explicit' hr hs

/-- **The remainder has a holomorphic version on `σ > r - 3/2`** (RH). `RRraw r` is holomorphic on
`σ > r - 3/2` off `s = r` (`differentiableOn_KR`; `1/Γ` entire; `ζ(s-r+1)` is differentiable off `s = r`,
`differentiableAt_riemannZeta`), and bounded near `r`: `1/(Γ(s)(s-r)) - 1/((r-1)!(s-r))` tends to `-Γ'(r)/Γ(r)²`
(derivative of `1/Γ`), and `ζ(w) - 1/(w-1)` tends to Euler's `γ` (`tendsto_riemannZeta_sub_one_div`). Removable
singularity: `Complex.differentiableOn_update_limUnder_of_bddAbove`, `R = update (RRraw r) r (limUnder …)`.
Size 80–150. -/
theorem exists_RR (hRH : RiemannHypothesis) {r : ℕ} (hr : 2 ≤ r) :
    ∃ R : ℂ → ℂ, DifferentiableOn ℂ R (halfPlane ((r : ℝ) - 3 / 2)) ∧
      ∀ s ∈ halfPlane ((r : ℝ) - 3 / 2), s ≠ (r : ℂ) → R s = RRraw r s :=
  FillC.exists_RR' hRH hr



theorem RR_bounded_halfStrip {r : ℕ} (hr : 2 ≤ r) {R : ℂ → ℂ}
    (hR : DifferentiableOn ℂ R (halfPlane ((r : ℝ) - 3 / 2)))
    (hRR : ∀ s ∈ halfPlane ((r : ℝ) - 3 / 2), s ≠ (r : ℂ) → R s = RRraw r s) {a : ℝ}
    (ha : (r : ℝ) - 3 / 2 < a) (T : ℝ) :
    ∃ M : ℝ, ∀ s : ℂ, a ≤ s.re → T ≤ s.im → s.im ≤ T + 1 → ‖R s‖ ≤ M :=
  FillC.RR_bounded_halfStrip' hr hR hRR ha T

end GoldbachBoundaries.PhiRProof
