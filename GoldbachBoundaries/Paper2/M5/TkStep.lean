import GoldbachBoundaries.Paper2.M5.TkLine
import GoldbachBoundaries.Paper2.M5.Fill.differentiableOn_TkPlus_TkMin
import GoldbachBoundaries.Paper2.M5.Fill.TkStep_eq_upper
import GoldbachBoundaries.Paper2.M5.Fill.TkStep_eq_strip
import GoldbachBoundaries.Paper2.M5.Fill.meromorphicOn_TkStep
import GoldbachBoundaries.Paper2.M5.Fill.TkStep_pole_facts
import GoldbachBoundaries.Paper2.M5.Fill.TkStep_strip_formula
import GoldbachBoundaries.Paper2.M5.Fill.TkStep_growth
import GoldbachBoundaries.Paper2.M5.Fill.tkPack_one
import GoldbachBoundaries.Paper2.M5.Fill.eventuallyEq_of_tkPack

/-!
# M5: the induction step of `cl:thm:Tk` (Theorem G)

From a package `TkPack m F H` (`m ≥ 1`) the explicit `TkStep m F`, `HkStep m F H` form a package at level `m + 1`
(`tkPack_succ`), so every `k ≥ 1` has one (`exists_tkPack`, induction from `tkPack_one`: `F = Qcont`, `H = 0`).

The three regions of the paper's proof, with `k = m + 1`:

* (a) `σ > m + 1`: `T_{m+1}(s) = (1/2πi)∫_{(c)} K_s(w) T_m(w) Q(s - w) dw` for `c ∈ (m, σ - 1)` (`Tk_succ_eq_verticalIntegral'`);
  moving the line across `w = m` (`TkLine_step_pole`) and inside `(m - 1/2, m)` (`TkLine_eq_of_no_pole`) gives region (b)'s
  formula on `σ > m + 1` as well (`TkStep_eq_upper`).
* (b) `σ > m + 1/2`: `TkStep = I⁺ + r_m K_s(m) Q(s - m)` exactly; its only pole is `s = m + 1`, residue
  `r_m Γ(m)Γ(1)/Γ(m+1) = 1/m!` (`TkStep_pole_facts`).
* (c) `m < σ < m + 1`: `TkStep = I + F(s-1)/(s-1) + r_m K_s(m) Q(s - m)` exactly (`TkStep_eq_strip`; on `σ > m + 1/2` by
  `TkLine_step_sub_one`), which is meromorphic (`F` is, on `σ > m - 1`) and gives (iii) with
  `H_{m+1}(s) = I(s) + H_m(s-1)/(s-1)` and the coefficient `r_mΓ(m) + m = m + 1` (`TkStep_strip_formula`).

The growth (iv) is region (b)'s formula with a fixed line (`TkStep_growth`, through `norm_TkLine_le`, so (Z6)).
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-! ## Lemmas

Proved in `Fill/`, one file per lemma (same name, same statement): `differentiableOn_TkPlus_TkMin`, `TkStep_eq_upper`, `TkStep_eq_strip`, `meromorphicOn_TkStep`, `TkStep_pole_facts`, `TkStep_strip_formula`, `TkStep_growth`, `tkPack_one`, `eventuallyEq_of_tkPack`. -/

/-! ## Real lemmas: the induction -/

/-- The induction step. -/
lemma tkPack_succ (hRH : RiemannHypothesis) (hZ6 : Z6) {m : ℕ} (hm : 1 ≤ m) {F H : ℂ → ℂ}
    (hP : TkPack m F H) : TkPack (m + 1) (TkStep m F) (HkStep m F H) :=
  ⟨meromorphicOn_TkStep hRH hm hP, TkStep_eqOn m F, (TkStep_strip_formula hRH hm hP).1,
    (TkStep_strip_formula hRH hm hP).2, (TkStep_pole_facts hRH hm hP).1, (TkStep_pole_facts hRH hm hP).2.1,
    (TkStep_pole_facts hRH hm hP).2.2, TkStep_growth hRH hZ6 hm hP⟩

/-- Every level `k ≥ 1` has a package. -/
lemma exists_tkPack (hRH : RiemannHypothesis) (hZ6 : Z6) :
    ∀ k : ℕ, 1 ≤ k → ∃ F H : ℂ → ℂ, TkPack k F H := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact ⟨Qcont, 0, tkPack_one hRH⟩
  | succ m hm ih =>
    obtain ⟨F, H, hP⟩ := ih
    exact ⟨_, _, tkPack_succ hRH hZ6 hm hP⟩

end GoldbachBoundaries.Paper2.M5
