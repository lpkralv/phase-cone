import GoldbachBoundaries.Paper2.Defs
import GoldbachBoundaries.Statements

/-!
# Paper 2, Milestone M1 (Theorem A of paper 2): definitions

M1 closes the unconditional core of paper 2 (Sections 2.2-2.3 and 3.1-3.4):
`nr:lem:Q` (i), (ii), `nr:lem:B` (i)-(iv), `nr:lem:MB`, `nr:lem:growthQ`, `nr:thm:cont`, `nr:thm:residue`,
`nr:cor:1+u` (first and second sentences). With them `intro_thm_A` and `cor_one_add_values` of
`Paper2/Statements.lean` are proved.

Nothing here imports `Paper2/Statements.lean`; the targets in `Skeleton.lean` restate its statements verbatim.

## Objects

* `IcQ Qc c s = (1/2πi) ∫_{(c)} K_s(w) Qc(w) Qc(s - w) dw`, the paper's `I_c(s)` with the continuation `Qc` of `Q`.
* `nu c a s = [Re a > c] + [σ - Re a < c]`, the indicator of `(nr:eq:cont)`.
* `TcQ Qc δ c s = I_c(s) + ∑_{a ∈ F_δ} ν R_a K_s(a) Qc(s - a)`, the right side `𝒯_c(s)` of `(nr:eq:cont)`.
* `AdmC δ c`: `δ, c` as in `nr:thm:cont` (`0 < δ < (1 - B_∞)/2`, `B_∞ + 2δ < c < 1`, `c ≠ Re a` on `F_δ`).
* `RegC δ c`: the region `(nr:eq:region)`.
* `Tcont`: the continuation of `T`, defined pointwise as `𝒯_c(s)` for a chosen admissible `(δ, c)` with
  `s ∈ RegC δ c` (when `B_∞ < 1` and such a choice exists), and as the series `T s` otherwise. The proof
  shows that `𝒯_c(s)` does not depend on the admissible choice off the pinch set (`Tc_indep`), which replaces the
  paper's local patching across the lines `σ = c + Re a` (Step 3) by a two-line contour shift (`Ic_sub_Ic`).

We use paper 1's concrete continuation `Qcont z = ∑ μ(n) (-ζ'/ζ)(nz)` (`SigmaMeromorphic.lean`, unconditional)
throughout; a statement about an arbitrary `Qc` with `IsQCont Qc` is reduced to `Qcont` by `isQCont_eventuallyEq`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M1

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- The paper's `I_c(s) = (1/2πi) ∫_{(c)} K_s(w) Q(w) Q(s - w) dw`, with `Qc` for `Q`. -/
def IcQ (Qc : ℂ → ℂ) (c : ℝ) (s : ℂ) : ℂ :=
  VerticalIntegral' (fun w => KerS s w * Qc w * Qc (s - w)) c

/-- The indicator `[Re a > c] + [σ - Re a < c]` of `(nr:eq:cont)`. -/
def nu (c : ℝ) (a s : ℂ) : ℂ := iverson (c < a.re) + iverson (s.re - a.re < c)

/-- The right side `𝒯_c(s)` of `(nr:eq:cont)`, with `Qc` for `Q`. -/
def TcQ (Qc : ℂ → ℂ) (δ c : ℝ) (s : ℂ) : ℂ :=
  IcQ Qc c s + ∑ᶠ a ∈ Fdelta δ, nu c a s * Rcoef a * KerS s a * Qc (s - a)

/-- `𝒯_c` for paper 1's `Qcont`. -/
abbrev Tc (δ c : ℝ) : ℂ → ℂ := TcQ Qcont δ c

/-- Admissible `(δ, c)`, as in `nr:thm:cont`. -/
def AdmC (δ c : ℝ) : Prop :=
  0 < δ ∧ δ < (1 - Binf) / 2 ∧ Binf + 2 * δ < c ∧ c < 1 ∧ ∀ a ∈ Fdelta δ, c ≠ a.re

/-- The region `(nr:eq:region)`: `σ > c + B_∞ + 2δ` and `σ ≠ c + Re a` for `a ∈ F_δ`. -/
def RegC (δ c : ℝ) : Set ℂ :=
  {s | c + Binf + 2 * δ < s.re ∧ ∀ a ∈ Fdelta δ, s.re ≠ c + a.re}

/-- The continuation of `T` to `σ > 2B_∞`: `𝒯_c(s)` for a chosen admissible `(δ, c)` with `s` in its region, and
the series otherwise (in particular when `B_∞ = 1`, where the region is `σ > 2`). -/
def Tcont (s : ℂ) : ℂ := by
  classical
  exact if h : Binf < 1 ∧ ∃ p : ℝ × ℝ, AdmC p.1 p.2 ∧ s ∈ RegC p.1 p.2 then
    Tc h.2.choose.1 h.2.choose.2 s else T s

/-- The hypothesis of `nr:lem:growthQ` on `H`: `H ≥ 2` and every zero with `|γ| ≥ H - 1` has `β ≤ B_∞ + δ`. -/
def GoodHeight (δ H : ℝ) : Prop :=
  2 ≤ H ∧ ∀ ρ ∈ NontrivialZeros, H - 1 ≤ |ρ.im| → ρ.re ≤ Binf + δ

/-- The real proof that `Tcont` is the chosen `𝒯_c` where a choice exists. -/
lemma Tcont_eq_choose {s : ℂ} (h : Binf < 1 ∧ ∃ p : ℝ × ℝ, AdmC p.1 p.2 ∧ s ∈ RegC p.1 p.2) :
    Tcont s = Tc h.2.choose.1 h.2.choose.2 s := by
  unfold Tcont
  rw [dite_eq_left h]

lemma Tcont_eq_T_of_not {s : ℂ} (h : ¬ (Binf < 1 ∧ ∃ p : ℝ × ℝ, AdmC p.1 p.2 ∧ s ∈ RegC p.1 p.2)) :
    Tcont s = T s := by
  unfold Tcont
  rw [dite_eq_right h]

end GoldbachBoundaries.Paper2.M1
