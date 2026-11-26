import GoldbachBoundaries.Paper2.M5.Tk
import GoldbachBoundaries.Paper2.M5.Fill.exists_factor_H
import GoldbachBoundaries.Paper2.M5.Fill.analyticAt_Afun
import GoldbachBoundaries.Paper2.M5.Fill.norm_gA_le
import GoldbachBoundaries.Paper2.M5.Fill.differentiableOn_FilLine
import GoldbachBoundaries.Paper2.M5.Fill.FilLine_eq_of_le
import GoldbachBoundaries.Paper2.M5.Fill.differentiableOn_Fil

/-!
# M5: Theorem F (i) (`cl:thm:filter`(i)): `D_H` is holomorphic on `ℍ`

The paper's proof of (i), with its `A(z) = (z - 1)Q(z)` made a function (`Afun`, value `1` at `z = 1`) and
`H = (z-1)(w-1)G` (`(cl:eq:HG)`, `exists_factor_H`). The integrand `gA H s z = K_s(z)G(z, s-z)A(z)A(s-z)` is holomorphic on
`{Re z > 1/2, Re(s - z) > 1/2}` under RH (`analyticAt_Afun`), with no removable points to step around, and it is
`O((1 + |Im z|)^{-2})` uniformly on compacts (`norm_gA_le`; M1's polynomial `Γ` decay, so no (Z6)). So `FilLine H c` is
holomorphic on `σ > c + 1/2` (`differentiableOn_FilLine`), independent of `c ∈ (1/2, σ - 1/2)` (`FilLine_eq_of_le`, no
pole in between), and `Fil H s = FilLine H (σ/2) s` is holomorphic on `ℍ` (`differentiableOn_Fil`). On `σ > 2` the line
`σ/2` is `DH`'s and the integrands agree pointwise (`Fil_eq_DH`).

The paper uses `nr:lem:growthQ` ((Z1)-(Z3)) for the growth of `Q` on lines; under RH paper 1's `norm_Qcont_le_log`
suffices, so (i) uses RH only. The paper also writes "(Equivalently, (i) is Theorem `cl:thm:mero`(ii) for `k_H`)"; that
route needs (R) for `k_H` with its reality clause in M4b's formal statement, which fails for complex `H`, so the direct
argument is used.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-! ## Lemmas

Proved in `Fill/`, one file per lemma (same name, same statement): `exists_factor_H`, `analyticAt_Afun`, `norm_gA_le`, `differentiableOn_FilLine`, `FilLine_eq_of_le`, `differentiableOn_Fil`. -/

/-! ## Real lemmas -/

/-- `H = (z - 1)(w - 1) Gpoly H`. -/
lemma evalH_eq_Gpoly (H : MvPolynomial (Fin 2) ℂ) (hHs : ∀ z w, evalH H z w = evalH H w z)
    (hH1 : ∀ w, evalH H 1 w = 0) (z w : ℂ) : evalH H z w = (z - 1) * (w - 1) * evalH (Gpoly H) z w := by
  have h := exists_factor_H H hHs hH1
  unfold Gpoly
  rw [dite_eq_left h]
  exact h.choose_spec z w

/-- Off `z = 1` and `s - z = 1`, `gA` is the integrand `k_H Q Q` (with `Qcont`). -/
lemma gA_eq_gH (H : MvPolynomial (Fin 2) ℂ) (hHs : ∀ z w, evalH H z w = evalH H w z)
    (hH1 : ∀ w, evalH H 1 w = 0) {s z : ℂ} (hz : z ≠ 1) (hsz : s - z ≠ 1) : gA H s z = gH H s z := by
  unfold gA gH kH Afun
  rw [ite_eq_right hz, ite_eq_right hsz, evalH_eq_Gpoly H hHs hH1 z (s - z)]
  ring

/-- **`Fil = D_H` on `σ > 2`**: the same line `σ/2`, and on it (`Re z = σ/2 > 1`, `Re(s - z) = σ/2 > 1`) `gA = gH`
(`gA_eq_gH`) and `Qcont = Q` (paper 1's `Qcont_eq_Q_of_one_lt`). -/
lemma Fil_eq_DH (H : MvPolynomial (Fin 2) ℂ) (hHs : ∀ z w, evalH H z w = evalH H w z)
    (hH1 : ∀ w, evalH H 1 w = 0) : EqOn (Fil H) (DH H) (halfPlane 2) := by
  intro s hs
  have hs' : 2 < s.re := hs
  unfold Fil FilLine DH VerticalIntegral' VerticalIntegral
  congr 3
  funext y
  set z : ℂ := (s.re / 2 : ℝ) + y * I with hz
  have hzre : z.re = s.re / 2 := by simp [hz]
  have hszre : (s - z).re = s.re / 2 := by simp [hz]; ring
  have hz1 : z ≠ 1 := fun h => by rw [h, one_re] at hzre; linarith
  have hsz1 : s - z ≠ 1 := fun h => by rw [h, one_re] at hszre; linarith
  rw [gA_eq_gH H hHs hH1 hz1 hsz1, gH, TIdentity.Qcont_eq_Q_of_one_lt (by rw [hzre]; linarith),
    TIdentity.Qcont_eq_Q_of_one_lt (by rw [hszre]; linarith)]

/-- A holomorphic continuation of `D_H` to `ℍ` is `Fil H` (identity theorem: both are holomorphic on `ℍ` and equal on
`σ > 2`). -/
lemma eqOn_Fil_of_DH (hRH : RiemannHypothesis) (H : MvPolynomial (Fin 2) ℂ)
    (hHs : ∀ z w, evalH H z w = evalH H w z) (hH1 : ∀ w, evalH H 1 w = 0) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F HH) (hFD : EqOn F (DH H) (halfPlane 2)) : EqOn F (Fil H) HH := by
  refine eqOn_HH_of_eqOn_open hF (differentiableOn_Fil hRH H) (isOpen_halfPlane 2) ⟨3, by
    show (2 : ℝ) < (3 : ℂ).re
    norm_num⟩ (fun s hs => ?_) (fun s hs => (hFD hs).trans (Fil_eq_DH H hHs hH1 hs).symm)
  have hs' : (2 : ℝ) < s.re := hs
  show (1 : ℝ) < s.re
  linarith

/-! ## Target -/

/-- `thm_filter_i` of `Paper2/Statements.lean`, statement verbatim. -/
theorem thm_filter_i_proof (hRH : RiemannHypothesis) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6)
    (H : MvPolynomial (Fin 2) ℂ) (hH0 : H ≠ 0) (hHs : ∀ z w, evalH H z w = evalH H w z)
    (hH1 : ∀ w, evalH H 1 w = 0) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F HH ∧ EqOn F (DH H) (halfPlane 2) := by
  have _ := hZ1  -- (Z1)-(Z3) are not used: under RH the growth of `Q` is paper 1's `norm_Qcont_le_log`
  have _ := hZ2
  have _ := hZ3
  have _ := hZ6  -- (Z6) is not used: M1's polynomial `Γ` decay bounds the kernel
  have _ := hH0  -- `H ≠ 0` is not used in (i)
  exact ⟨Fil H, differentiableOn_Fil hRH H, Fil_eq_DH H hHs hH1⟩

end GoldbachBoundaries.Paper2.M5
