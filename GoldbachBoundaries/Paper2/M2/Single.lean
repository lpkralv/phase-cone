import GoldbachBoundaries.Paper2.M2.Rigidity
import GoldbachBoundaries.Paper2.M2.Fill.Nzero_le_mul_log
import GoldbachBoundaries.Paper2.M2.Fill.Rcoef_div_of_isSingleRep
import GoldbachBoundaries.Paper2.M2.Fill.eventually_four_mul_log_le
import GoldbachBoundaries.Paper2.M2.Fill.eventually_le_sq_div_log_sq
import GoldbachBoundaries.Paper2.M2.Fill.ncard_lineZeros_window_ge
import GoldbachBoundaries.Paper2.M2.Fill.ncard_notGood_le
import GoldbachBoundaries.Paper2.M2.Fill.ncard_primes_window_ge
import GoldbachBoundaries.Paper2.M2.Fill.ncard_zeros_le_Nzero
import GoldbachBoundaries.Paper2.M2.Fill.singlePairs_bounds
import GoldbachBoundaries.Paper2.M2.Fill.singlePairs_finite_ncard_ge
import GoldbachBoundaries.Paper2.M2.Fill.singlePairs_injOn

/-!
# M2: single-representation points on the critical line (`nr:thm:single`)

The count of `𝓟(X) = singlePairs A₀ y ε X`: at least `A₀X/2` distinct zeros `1/2 + iγ` with `X/M < γ ≤ X`
((Z4) through the witnesses `A₀, t₀`, and (Z2) for `N(X/M) ≤ (X/M) log X`), each with at least `c₁ X/log²X` primes
`q` such that `γ/q ∈ J` ((Z5) on `(x, (1+θ)x)`, `x = γ/(y + ε/2)`, `θ = ε/(y - ε/2)`). The pairs that are not good map
to zeros `ζ*` with `0 < Im ζ* < 2X` with fibres of size at most `2` (`lem_rigidity_proof`,
`lem_rigidity_converse_proof`), so there are at most `2N(2X) ≤ 4X log(2X)` of them ((Z2)).

All asymptotic statements are `∀ᶠ X in atTop`; the target chooses `X₀` from their conjunction
(`Filter.eventually_atTop`). The targets `thm_single_proof`, `thm_single_infinite_proof` are at the end of this
file (`LW.lean` and `Lambda.lean` use them).

**Integrated layout.** The eleven lemmas this file stated with `sorry` (`ncard_zeros_le_Nzero`, `Nzero_le_mul_log`,
`ncard_lineZeros_window_ge`, `ncard_primes_window_ge`, `singlePairs_finite_ncard_ge`, `ncard_notGood_le`,
`Rcoef_div_of_isSingleRep`, `singlePairs_bounds`, `singlePairs_injOn`, `eventually_four_mul_log_le`,
`eventually_le_sq_div_log_sq`) are proved in `Fill/<name>.lean`, statements unchanged, each with its sketch as
docstring; the fill files import `Rigidity.lean` (and each other where needed), and this file imports them. The proofs
of the group B lemmas are the `<name>B` lemmas of `Fill/BCommon.lean`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M2

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-! ## Targets -/

/-- `thm_single` of `Paper2/Statements.lean`, statement verbatim. -/
theorem thm_single_proof (hZ1 : Z1) (hZ2 : Z2) (hZ5 : Z5) {A₀ t₀ : ℝ} (hA₀ : 0 < A₀)
    (hN0 : ∀ t ≥ t₀, A₀ * t ≤ (N0 t : ℝ)) {y ε : ℝ} (hy : 0 < y) (hε : 0 < ε) (hεy : ε < y) :
    ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → 3 ≤ X →
      (singlePairs A₀ y ε X).Finite ∧
      c₂ * X ^ 2 / Real.log X ^ 2 ≤ ((singlePairs A₀ y ε X).ncard : ℝ) ∧
      (({p | p ∈ singlePairs A₀ y ε X ∧ ¬ IsSingleRep p.1 p.2}.ncard : ℕ) : ℝ) ≤
        4 * X * Real.log (2 * X) ∧
      c₂ / 2 * X ^ 2 / Real.log X ^ 2 ≤
        (({p | p ∈ singlePairs A₀ y ε X ∧ IsSingleRep p.1 p.2}.ncard : ℕ) : ℝ) ∧
      (∀ p ∈ singlePairs A₀ y ε X, IsSingleRep p.1 p.2 →
        ‖p.1 / (p.2 : ℂ) - y * I‖ < ε ∧ (p.1 / (p.2 : ℂ)).re = 1 / (2 * p.2) ∧
        Rcoef (p.1 / (p.2 : ℂ)) = (zetaMult p.1 : ℂ) / p.2 ∧ Rcoef (p.1 / (p.2 : ℂ)) ≠ 0 ∧
        ‖2 * Rcoef (p.1 / (p.2 : ℂ)) / (p.1 / (p.2 : ℂ))‖ = 2 * zetaMult p.1 / ‖p.1‖ ∧
        2 / (X + 1) ≤ 2 * zetaMult p.1 / ‖p.1‖) ∧
      InjOn (fun p : ℂ × ℕ => p.1 / (p.2 : ℂ)) (singlePairs A₀ y ε X) := by
  obtain ⟨c₂, hc₂, hP⟩ := singlePairs_finite_ncard_ge hZ2 hZ5 hA₀ hN0 hy hε hεy
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.mp
    (hP.and ((ncard_notGood_le hZ1 hZ2 A₀ y ε).and
      ((singlePairs_bounds hA₀ hy hε hεy).and (eventually_four_mul_log_le hc₂))))
  refine ⟨c₂, hc₂, X₀, fun X hX _ => ?_⟩
  obtain ⟨⟨hfin, hcard⟩, hbad, hb, h4⟩ := hX₀ X hX
  have hsplit := Set.ncard_inter_add_ncard_sdiff_eq_ncard (singlePairs A₀ y ε X)
    {p : ℂ × ℕ | IsSingleRep p.1 p.2} hfin
  have hsplit' : (({p | p ∈ singlePairs A₀ y ε X ∧ IsSingleRep p.1 p.2}.ncard : ℕ) : ℝ) +
      (({p | p ∈ singlePairs A₀ y ε X ∧ ¬ IsSingleRep p.1 p.2}.ncard : ℕ) : ℝ) =
        ((singlePairs A₀ y ε X).ncard : ℝ) := by
    exact_mod_cast hsplit
  have hhalf : c₂ / 2 * X ^ 2 / Real.log X ^ 2 = (c₂ * X ^ 2 / Real.log X ^ 2) / 2 := by ring
  refine ⟨hfin, hcard, hbad, by linarith, fun p hp hs => ?_, singlePairs_injOn A₀ y ε X⟩
  obtain ⟨h1, h2, h3⟩ := hb p hp
  have hq : p.2.Prime := hp.2.2.2.2.1
  obtain ⟨hR, hn⟩ := Rcoef_div_of_isSingleRep hp.1 hq hs
  refine ⟨h1, h2, hR, ?_, hn, h3⟩
  rw [hR]
  have hm : zetaMult p.1 ≠ 0 := by
    have := one_le_zetaMult hp.1
    omega
  exact div_ne_zero (by exact_mod_cast hm) (by exact_mod_cast hq.ne_zero)

/-- `thm_single_infinite` of `Paper2/Statements.lean`, statement verbatim. -/
theorem thm_single_infinite_proof (hZ1 : Z1) (hZ2 : Z2) (hZ4 : Z4) (hZ5 : Z5) {y ε : ℝ} (hy : 0 < y)
    (hε : 0 < ε) (hεy : ε < y) :
    {u : ℂ | ∃ ρ ∈ NontrivialZeros, ρ.re = 1 / 2 ∧ ∃ q : ℕ, q.Prime ∧ IsSingleRep ρ q ∧
      u = ρ / (q : ℂ) ∧ ‖u - y * I‖ < ε}.Infinite := by
  obtain ⟨A₀, hA₀, t₀, hN0⟩ := hZ4
  obtain ⟨c₂, hc₂, X₀, hX₀⟩ := thm_single_proof hZ1 hZ2 hZ5 hA₀ hN0 hy hε hεy
  apply infinite_of_forall_le_ncard
  intro N
  obtain ⟨X, hXN, hXge⟩ :=
    ((eventually_le_sq_div_log_sq hc₂ (N : ℝ)).and (Filter.eventually_ge_atTop (max X₀ 3))).exists
  obtain ⟨hfin, -, -, hgood, hb, hinj⟩ := hX₀ X (le_of_max_le_left hXge) (le_of_max_le_right hXge)
  set G := {p | p ∈ singlePairs A₀ y ε X ∧ IsSingleRep p.1 p.2} with hG
  have hGsub : G ⊆ singlePairs A₀ y ε X := fun p hp => hp.1
  refine ⟨(fun p : ℂ × ℕ => p.1 / (p.2 : ℂ)) '' G, ?_, (hfin.subset hGsub).image _, ?_⟩
  · rintro u ⟨p, hp, rfl⟩
    exact ⟨p.1, hp.1.1, hp.1.2.1, p.2, hp.1.2.2.2.2.1, hp.2, rfl, (hb p hp.1 hp.2).1⟩
  · rw [(hinj.mono hGsub).ncard_image]
    have : (N : ℝ) ≤ (G.ncard : ℝ) := hXN.trans hgood
    exact_mod_cast this

end GoldbachBoundaries.Paper2.M2
