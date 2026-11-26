import GoldbachBoundaries.Paper2.M1.Assembly

/-!
# Paper 2, Milestone M2 (Theorem B of paper 2): definitions

M2 closes the statements of `Paper2/Statements.lean` behind Theorem B (Sections 3.5-3.6, 3.9 and
`nr:lem:Q`(iii)): `lem_Q_iii`, `lem_rigidity`, `lem_rigidity_converse`, `thm_single`,
`thm_single_infinite`, `cor_LW`, `lem_far`, `lem_far_abs`, `prop_Lambda`, `thm_boundary`. With them
`rem_dichotomy_i` of `Paper2/Statements.lean` is proved.

Nothing here imports `Paper2/Statements.lean`; the targets restate its statements verbatim. Layout (acyclic, in
dependency order): `QCount` (`lem_Q_iii_proof`), `Rigidity` (`lem_rigidity_proof`, `lem_rigidity_converse_proof`),
`Single` (`thm_single_proof`, `thm_single_infinite_proof`), `LW` (`cor_LW_proof`), `Far` (`lem_far_proof`,
`lem_far_abs_proof`), `Lambda` (`prop_Lambda_proof`), `Skeleton` (`thm_boundary_proof`, and the index). A target
that a later file needs is proved in its own file, so a filler of a later lemma can import it.

## Objects

* `SH H = {a ∈ Σ_Q ∖ {1} : Re a > 1 - B, |Im a| ≤ H}`, the set `𝒮_H` of the proof of `nr:thm:boundary`.
* `NearBad H Y`: the points `u` (`0 < Re u ≤ 1`, `|Im u| ≤ Y`) having an ordered pair `(a, b) ≠ (1, u), (u, 1)` in
  `Σ_Q²` with `a + b = 1 + u` and `|Im a| ≤ H` (the paper's *near-bad* pairs, as a set of points `u`).
* `rigPairs z`: the pairs `(ρ, q)` of the converse of `nr:lem:rigidity` whose zero `ζ*` is `z`.
* `pairOf q w = (q w / (2 q Re w), q)`: the pair `(ρ, q)` recovered from `ρ' = w` (`k = 2q Re ρ'`, `ρ = qρ'/k`).
* `qOfDen d`: the recipe `q = d` (`d` odd), `q = d/2` (`d` even) of `nr:lem:rigidity`.
* `LambdaSet y ε`: the set of `prop_Lambda`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M2

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- `𝒮_H = {a ∈ Σ_Q ∖ {1} : Re a > 1 - B, |Im a| ≤ H}` (proof of `nr:thm:boundary`). -/
def SH (H : ℝ) : Set ℂ := {a | a ∈ PoleSetQ ∧ a ≠ 1 ∧ 1 - Bsup < a.re ∧ |a.im| ≤ H}

/-- The points `u` with `0 < Re u ≤ 1`, `|Im u| ≤ Y` that have a competing pair below height `H`: an ordered pair
`(a, b) ∈ Σ_Q²`, `a + b = 1 + u`, other than `(1, u)`, `(u, 1)`, with `|Im a| ≤ H`. A good pair `(ρ, q)` is
*near-bad* in the paper exactly when `ρ/q ∈ NearBad H Y`. -/
def NearBad (H Y : ℝ) : Set ℂ :=
  {u | 0 < u.re ∧ u.re ≤ 1 ∧ |u.im| ≤ Y ∧
    ∃ p ∈ pinchPairs (1 + u), p ≠ (1, u) ∧ p ≠ (u, 1) ∧ |p.1.im| ≤ H}

/-- The pairs `(ρ, q)` of `nr:lem:rigidity` (converse) with `ζ* = z`: `ρ = 1/2 + iγ` a zero, `γ > 0`, `q` prime, and a
representation `(ρ', k) ≠ (ρ, q)` of `ρ/q` with `zetaStar ρ' k q = z`. The same set as in `lem_rigidity_converse`. -/
def rigPairs (z : ℂ) : Set (ℂ × ℕ) :=
  {p : ℂ × ℕ | p.1 ∈ NontrivialZeros ∧ p.1.re = 1 / 2 ∧ 0 < p.1.im ∧ p.2.Prime ∧
    ∃ ρ' : ℂ, ∃ k : ℕ, IsRep (p.1 / (p.2 : ℂ)) ρ' k ∧ (ρ', k) ≠ p ∧ zetaStar ρ' k p.2 = z}

/-- The pair `(ρ, q)` recovered from `q` and `ρ' = w`: `k = 2q Re w`, `ρ = q w / k`. -/
def pairOf (q : ℕ) (w : ℂ) : ℂ × ℕ := ((q : ℂ) * w / ((2 * q * w.re : ℝ) : ℂ), q)

/-- The recipe of `nr:lem:rigidity`: `q = d` if `d` is odd, `q = d/2` if `d` is even. -/
def qOfDen (d : ℕ) : ℕ := if Odd d then d else d / 2

/-- The set of `prop_Lambda`: points `s₀ = 1 + ρ/q` (`ρ` a zero on the critical line, `q` prime) in
`Δ(1 + iy, ε)` with `𝓡(s₀) ≠ 0`. -/
def LambdaSet (y ε : ℝ) : Set ℂ :=
  {s₀ : ℂ | ∃ ρ ∈ NontrivialZeros, ρ.re = 1 / 2 ∧ ∃ q : ℕ, q.Prime ∧ s₀ = 1 + ρ / (q : ℂ) ∧
    s₀ ∈ ball (1 + (y : ℂ) * I) ε ∧ pairSum s₀ ≠ 0}

/-- Paper 1's `Qcont` is a continuation of `Q` in the sense of `IsQCont` (the proof of `exists_isQCont` in
`Paper2/Statements.lean`, which this file may not import). -/
lemma isQCont_Qcont : IsQCont Qcont := by
  refine ⟨fun z hz => meromorphicAt_Qcont hz, fun z hz => ?_, fun z hz => ?_⟩
  · have hz' : 1 < z.re := hz
    show Qcont z = Q z
    rw [Q_eq_tsum_moebius_zeta hz']
    simp only [Qcont, sigmaTerm, negLogDerivZeta, neg_div]
  · have h0 : 0 < z.re := hz.1
    have h := analyticAt_Qcont_sub_sum h0 ∅
      (fun n _ hmu => regular_of_not_mem_poleSetQ h0 hz.2 hmu)
    simpa using h

/-- A set that contains finite subsets of every size is infinite. -/
lemma infinite_of_forall_le_ncard {α : Type*} {s : Set α}
    (h : ∀ N : ℕ, ∃ t ⊆ s, t.Finite ∧ N ≤ t.ncard) : s.Infinite := by
  intro hs
  obtain ⟨t, hts, -, hN⟩ := h (s.ncard + 1)
  have := Set.ncard_le_ncard hts hs
  omega

end GoldbachBoundaries.Paper2.M2
