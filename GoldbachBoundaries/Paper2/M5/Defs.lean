import GoldbachBoundaries.Paper2.M4b.Skeleton

/-!
# Paper 2, Milestone M5 (Theorems G and F): definitions and small facts

Everything in this file has a real proof.

## Objects for Theorem G (`cl:thm:Tk`)

The induction on `k` is carried by a *package* `TkPack k F H`: a concrete continuation `F` of `T_k` to `σ > k - 1`
and a concrete `H_k`, with every property the next step uses ((i)-(iv) of the theorem in a pointwise form). The step
`k = m → m + 1` is explicit:

* `TkLine F c s = (1/2πi) ∫_{(c)} K_s(w) F(w) Q(s - w) dw`, the line integral of `(cl:eq:Tk)` with `F` the
  continuation of `T_m` and `Q` paper 1's `Qcont`;
* `cPlusK m s ∈ (m - 1/2, min(m, σ - 1))` (the line of `I⁺`, region (b)) and
  `cMinK m s ∈ (max(m - 1/2, σ - 1), min(m, σ - 1/2))` (the line of `I`, region (c)), both midpoints;
* `TkStep m F` glues the series `T_{m+1}` on `σ > m + 1`, `I⁺(s) + r_m K_s(m) Q(s - m)` on `m + 1/2 < σ ≤ m + 1`
  (region (b)), and `I(s) + F(s-1)/(s-1) + r_m K_s(m) Q(s - m)` on `σ ≤ m + 1/2` (region (c)), with `r_m = 1/(m-1)!`;
* `HkStep m F H s = I(s) + H(s-1)/(s-1)` (the paper's `H_k`).

## Objects for Theorem F (`cl:thm:filter`)

* `Gpoly H`: a polynomial `G` with `H = (z - 1)(w - 1)G` (`(cl:eq:HG)`), chosen when it exists (it does when `H` is
  symmetric with `H(1, w) ≡ 0`, `exists_factor_H`).
* `Afun z = (z - 1)Q(z)`, with its removable value `1` at `z = 1` (the paper's `A`); holomorphic on `Re z > 1/2` under
  RH.
* `gA H s z = K_s(z) G(z, s - z) A(z) A(s - z)`, the integrand of `(cl:eq:DH)` written without removable
  singularities, `FilLine H c s` its line integral, and `Fil H s = FilLine H (σ/2) s`: on `σ > 2` it is `D_H` (same
  line as `DH`), and it is the continuation of (i) on `ℍ`.
* `gH H s z = k_H(z, s) Q(z) Q(s - z)` (the integrand with `Qcont`), `Jfil H s` its integral on `Re z = 2/5`
  (the paper's `J` with `c' = 2/5 ∈ (1/3, 1/2)`), `midTerm`, `resTerm` the residues at `1/2` and at a zero `ρ`
  (`(cl:eq:shift)`), and `midLim`, `limTerm` their limits after multiplying by `η` (Step 3).
* `H0f = (z - 1)(w - 1)` (a copy of `Statements.lean`'s `H0`, which this tree cannot import).
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-! ## Theorem G -/

/-- `r_m = 1/(m-1)!`, the residue of `T_m` at `m`. -/
def rK (m : ℕ) : ℂ := 1 / ((m - 1).factorial : ℂ)

/-- `(1/2πi) ∫_{(c)} K_s(w) F(w) Q(s - w) dw` with paper 1's continuation `Qcont` (the line integrals of the proof of
`cl:thm:Tk`, with `F` the continuation of `T_{k-1}`). -/
def TkLine (F : ℂ → ℂ) (c : ℝ) (s : ℂ) : ℂ :=
  VerticalIntegral' (fun w => KerS s w * F w * Qcont (s - w)) c

/-- The line of `I⁺` (region (b) of the proof): the midpoint of `(m - 1/2, min(m, σ - 1))`, non-empty for
`σ > m + 1/2`. -/
def cPlusK (m : ℕ) (s : ℂ) : ℝ := ((m : ℝ) - 1 / 2 + min (m : ℝ) (s.re - 1)) / 2

/-- The line of `I` (region (c)): the midpoint of `(max(m - 1/2, σ - 1), min(m, σ - 1/2))`, non-empty for
`m < σ < m + 1`. -/
def cMinK (m : ℕ) (s : ℂ) : ℝ := (max ((m : ℝ) - 1 / 2) (s.re - 1) + min (m : ℝ) (s.re - 1 / 2)) / 2

/-- The continuation of `T_{m+1}` built from a continuation `F` of `T_m`: the series on `σ > m + 1`; region (b)'s
`I⁺(s) + r_m K_s(m) Q(s - m)` on `m + 1/2 < σ ≤ m + 1`; region (c)'s `I(s) + F(s-1)/(s-1) + r_m K_s(m) Q(s - m)` below. -/
def TkStep (m : ℕ) (F : ℂ → ℂ) (s : ℂ) : ℂ := by
  classical
  exact if ((m + 1 : ℕ) : ℝ) < s.re then Tk (m + 1) s
    else if (m : ℝ) + 1 / 2 < s.re then TkLine F (cPlusK m s) s + rK m * KerS s m * Qcont (s - m)
    else TkLine F (cMinK m s) s + F (s - 1) / (s - 1) + rK m * KerS s m * Qcont (s - m)

/-- The paper's `H_{m+1}(s) = I(s) + H_m(s-1)/(s-1)` on `m < σ < m + 1`. -/
def HkStep (m : ℕ) (F Hm : ℂ → ℂ) (s : ℂ) : ℂ := TkLine F (cMinK m s) s + Hm (s - 1) / (s - 1)

/-- The induction package for `cl:thm:Tk` at level `k`: `F` is meromorphic on `σ > k - 1` and is the series on
`σ > k` ((i)); `H` is holomorphic on the strip and `(iii)` holds pointwise off `Σ_Q`; `F` is analytic on
`σ > k - 1/2` except at `k`, where it has a simple pole with residue `1/(k-1)!` ((ii)); and `(iv)`. -/
def TkPack (k : ℕ) (F H : ℂ → ℂ) : Prop :=
  MeromorphicOn F (halfPlane ((k : ℝ) - 1)) ∧ EqOn F (Tk k) (halfPlane k) ∧
    DifferentiableOn ℂ H {s | (k : ℝ) - 1 < s.re ∧ s.re < k} ∧
    (∀ s : ℂ, (k : ℝ) - 1 < s.re → s.re < k → s - k + 1 ∉ PoleSetQ →
      F s = H s + k * (Gamma (s - k + 1) / Gamma s) * Qcont (s - k + 1)) ∧
    (∀ s : ℂ, (k : ℝ) - 1 / 2 < s.re → s ≠ k → AnalyticAt ℂ F s) ∧
    meromorphicOrderAt F k = -1 ∧ HasResidue F k (1 / (k - 1).factorial) ∧
    ∀ x₁ x₂ : ℝ, (k : ℝ) - 1 / 2 < x₁ → x₁ ≤ x₂ → ∃ N C y₀ : ℝ, ∀ x ∈ Icc x₁ x₂, ∀ y : ℝ,
      y₀ ≤ |y| → ‖F (x + y * I)‖ ≤ C * |y| ^ N

/-- `TkStep` is the series on `σ > m + 1` (its first branch). -/
lemma TkStep_eqOn (m : ℕ) (F : ℂ → ℂ) : EqOn (TkStep m F) (Tk (m + 1)) (halfPlane ((m + 1 : ℕ) : ℝ)) := by
  intro s hs
  have hs' : ((m + 1 : ℕ) : ℝ) < s.re := hs
  unfold TkStep
  exact ite_eq_left_of_eq_true _ _ (eq_true hs')

/-- Copy of `Statements.lean`'s `Tk_one`: `T₁ = Q`. -/
lemma Tk_one' : Tk 1 = Q := by
  funext s
  rw [Tk, Q, ← (Equiv.funUnique (Fin 1) Nat.Primes).symm.tsum_eq]
  congr 1
  funext p
  simp [Equiv.funUnique]

/-! ## Theorem F -/

/-- A polynomial `G` with `H(z, w) = (z - 1)(w - 1) G(z, w)` (eq. `(cl:eq:HG)`), if one exists; `0` otherwise. -/
def Gpoly (H : MvPolynomial (Fin 2) ℂ) : MvPolynomial (Fin 2) ℂ := by
  classical
  exact if h : ∃ G : MvPolynomial (Fin 2) ℂ, ∀ z w, evalH H z w = (z - 1) * (w - 1) * evalH G z w
    then h.choose else 0

/-- `A(z) = (z - 1) Q(z)` with its removable value `A(1) = 1` (the residue of `Q` at `1`). -/
def Afun (z : ℂ) : ℂ := by
  classical
  exact if z = 1 then 1 else (z - 1) * Qcont z

/-- The integrand of `(cl:eq:DH)` without removable singularities: `K_s(z) G(z, s - z) A(z) A(s - z)`. -/
def gA (H : MvPolynomial (Fin 2) ℂ) (s z : ℂ) : ℂ :=
  KerS s z * evalH (Gpoly H) z (s - z) * Afun z * Afun (s - z)

/-- `(1/2πi) ∫_{(c)} gA`. -/
def FilLine (H : MvPolynomial (Fin 2) ℂ) (c : ℝ) (s : ℂ) : ℂ := VerticalIntegral' (gA H s) c

/-- The continuation of `D_H` to `ℍ` (Theorem F(i)): the line `c = σ/2`, which lies in `(1/2, σ - 1/2)` for `σ > 1`
and is the line of `DH` for `σ > 2`. -/
def Fil (H : MvPolynomial (Fin 2) ℂ) (s : ℂ) : ℂ := FilLine H (s.re / 2) s

/-- The integrand `k_H(z, s) Q(z) Q(s - z)` with paper 1's `Qcont`. -/
def gH (H : MvPolynomial (Fin 2) ℂ) (s z : ℂ) : ℂ := kH H z s * Qcont z * Qcont (s - z)

/-- The paper's `J(s) = (1/2πi) ∫_{(c')} g_s`, with `c' = 2/5 ∈ (1/3, 1/2)`. -/
def Jfil (H : MvPolynomial (Fin 2) ℂ) (s : ℂ) : ℂ := VerticalIntegral' (gH H s) (2 / 5)

/-- The residue `R_{1/2} K_s(1/2) H(1/2, s - 1/2) Q(s - 1/2)` of `gH` at `1/2` (`(cl:eq:shift)`). -/
def midTerm (H : MvPolynomial (Fin 2) ℂ) (s : ℂ) : ℂ :=
  Rcoef (1 / 2) * KerS s (1 / 2) * evalH H (1 / 2) (s - 1 / 2) * Qcont (s - 1 / 2)

/-- The residue `R_ρ K_s(ρ) H(ρ, s - ρ) Q(s - ρ)` of `gH` at a zero `ρ` (`(cl:eq:shift)`). -/
def resTerm (H : MvPolynomial (Fin 2) ℂ) (s ρ : ℂ) : ℂ :=
  Rcoef ρ * KerS s ρ * evalH H ρ (s - ρ) * Qcont (s - ρ)

/-- The limit of `η · midTerm(s₀ + η)`, `s₀ = 1 + iτ₀`: `R_{1/2} K_1(1/2) H(1/2,1/2) R_{1/2}` if `τ₀ = 0`, else `0`
(Step 3 and part (iv) of the proof). -/
def midLim (H : MvPolynomial (Fin 2) ℂ) (τ₀ : ℝ) : ℂ := by
  classical
  exact if τ₀ = 0 then Rcoef (1 / 2) * KerS 1 (1 / 2) * evalH H (1 / 2) (1 / 2) * Rcoef (1 / 2) else 0

/-- The limit of `η · resTerm(s₀ + η, ρ)`, `s₀ = 1 + iτ₀`: `R_ρ K_{s₀}(ρ) H(ρ, s₀ - ρ) R_{s₀ - ρ}` if `s₀ - ρ` is a zero,
else `0` (Step 3; valid when `Im ρ ≠ τ₀`). -/
def limTerm (H : MvPolynomial (Fin 2) ℂ) (τ₀ : ℝ) (ρ : ℂ) : ℂ := by
  classical
  exact if 1 + τ₀ * I - ρ ∈ NontrivialZeros then
      Rcoef ρ * KerS (1 + τ₀ * I) ρ * evalH H ρ (1 + τ₀ * I - ρ) * Rcoef (1 + τ₀ * I - ρ)
    else 0

/-- `H₀(z, w) = (z - 1)(w - 1)` (copy of `Statements.lean`'s `H0`). -/
def H0f : MvPolynomial (Fin 2) ℂ := (MvPolynomial.X 0 - 1) * (MvPolynomial.X 1 - 1)

/-- Copy of `Statements.lean`'s `kH_H0`. -/
lemma kH_H0f : kH H0f = k0 := by
  funext z s
  simp [kH, k0, evalH, H0f]
  ring

/-- Copy of `Statements.lean`'s `H0_conditions`. -/
lemma H0f_conditions :
    H0f ≠ 0 ∧ (∀ z w, evalH H0f z w = evalH H0f w z) ∧ ∀ w, evalH H0f 1 w = 0 := by
  refine ⟨?_, fun z w => by simp [evalH, H0f]; ring, fun w => by simp [evalH, H0f]⟩
  intro h
  have := congrArg (MvPolynomial.eval ![(2 : ℂ), 2]) h
  norm_num [H0f] at this

/-- Copy of `Statements.lean`'s `Lambda0_pos`. -/
lemma Lambda0_pos' : 0 < Lambda0 := by
  have : 0 ≤ ∑' ρ, lambda0Term ρ := tsum_nonneg fun ρ => by unfold lambda0Term; positivity
  unfold Lambda0
  have := Real.pi_pos
  positivity

/-- The good heights of `cl:lem:Qleft`(ii): the horizontal lines at `±Y'` miss `Σ_Q` on `1/3 ≤ Re ≤ 1`. -/
def GoodY (Y' : ℝ) : Prop :=
  ∀ x ∈ Icc (1 / 3 : ℝ) 1, (x + Y' * I : ℂ) ∉ PoleSetQ ∧ (x - Y' * I : ℂ) ∉ PoleSetQ

end GoldbachBoundaries.Paper2.M5
