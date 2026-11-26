import GoldbachBoundaries.Paper2.M4a.Coeff
import GoldbachBoundaries.Paper2.M4a.Fill.segment_subset_Str
import GoldbachBoundaries.Paper2.M4a.Fill.differentiableOn_Jseg
import GoldbachBoundaries.Paper2.M4a.Fill.hasDerivAt_Jseg_of_app_eq

/-!
# M4a: the segment integrals `J_{ab}` and the coefficients `X_α` (`cl:lem:J`)

`J_{ab}(s) = (L(s) - a - b) ∫_0^1 k(a + t(L(s) - a - b), s) dt` (`Jseg`, by definition). The points of `Σ` have real
parts in `(0, 1]` without RH (M1's `poleSetQ_re_bounds`), so for `s ∈ ℍ_L` both ends `a`, `L(s) - b` lie in the convex
strip `Str(s)`. Holomorphy is differentiation under the integral (paper 1's
`ThmA.differentiableOn_intervalIntegral_of_continuousOn`), once for `D_L` under (K1) and once for `ℍ_L` under (H2a)
(`differentiableOn_Jseg`, stated for any open `U ⊆ ℍ_L`). At a point `α` with `L(α) = a + b` the factor `L(s) - a - b`
vanishes and `J'_{ab}(α) = ℓ · ∫_0^1 k(a, α) dt = ℓ k(a, α)` (product rule).

`X_α` (`lem_J_ii`): under RH a pinch `α` has `b = L(α) - 1 ∈ Σ` (`Catalogue.lean`), so `α ∈ D_L` (`Re L(α) ≤ 2`), and
the two (or one) `J`'s at `α` give `X'_α(α) = ℓc₁c_b(k(1,α) + k(b,α)) = ℓc₁c_b𝔟(α)`.

The targets `lem_J_i_proof`, `lem_J_ii_proof` are at the end of the file.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M4a

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-! ## Lemmas

Proved in `Fill/`, one file per lemma (same name, same statement): `segment_subset_Str`, `differentiableOn_Jseg`, `hasDerivAt_Jseg_of_app_eq`. -/

/-! ## Real lemmas -/

/-- Under RH a pinch `α` has `L(α) - 1 ∈ Σ`, and lies in `D_L` (`Re L(α) = 1 + Re b ≤ 2`). -/
lemma catalogueL_facts (hRH : RiemannHypothesis) (A : Aff) {α : ℂ} (hα : α ∈ catalogueL A) :
    α ∈ A.DL ∧ A.app α - 1 ∈ PoleSetQ := by
  obtain ⟨hH, hP⟩ := hα
  have hb := sub_one_mem_poleSetQ_of_mem_pinch hRH hP hH
  refine ⟨⟨hH, ?_⟩, hb⟩
  have h1 := (poleSetQ_re_bounds hb).2.1
  have e : (A.app α).re = (A.app α - 1).re + 1 := by simp
  linarith

/-! ## Targets -/

/-- `lem_J_i` of `Paper2/Statements.lean`, statement verbatim. -/
theorem lem_J_i_proof (A : Aff) (k : ℂ → ℂ → ℂ) (hK1 : K1 A k) {a b : ℂ} (ha : a ∈ PoleSetQ)
    (hb : b ∈ PoleSetQ) :
    (∀ s ∈ A.DL, segment ℝ a (A.app s - b) ⊆ A.Str s) ∧
    DifferentiableOn ℂ (Jseg A k a b) A.DL ∧
    (H2a A k → (∀ s ∈ A.HL, segment ℝ a (A.app s - b) ⊆ A.Str s) ∧
      DifferentiableOn ℂ (Jseg A k a b) A.HL) ∧
    ∀ α ∈ A.DL, A.app α = a + b → Jseg A k a b α = 0 ∧ HasDerivAt (Jseg A k a b) (A.ell * k a α) α := by
  refine ⟨fun s hs => segment_subset_Str A ha hb hs.1,
    differentiableOn_Jseg A k (isOpen_DL A) (DL_subset_HL A) hK1 ha hb,
    fun hH2a => ⟨fun s hs => segment_subset_Str A ha hb hs,
      differentiableOn_Jseg A k (isOpen_HL A) subset_rfl hH2a ha hb⟩,
    fun α hα h => ⟨by simp [Jseg, h], hasDerivAt_Jseg_of_app_eq A k hK1 ha hb hα h⟩⟩

/-- `lem_J_ii` of `Paper2/Statements.lean`, statement verbatim. -/
theorem lem_J_ii_proof (hRH : RiemannHypothesis) (A : Aff) (k : ℂ → ℂ → ℂ) (hK1 : K1 A k) {α : ℂ}
    (hα : α ∈ catalogueL A) :
    α ∈ A.DL ∧ DifferentiableOn ℂ (Xcoef A k α) A.DL ∧ Xcoef A k α α = 0 ∧
    (A.app α - 1 ≠ 1 →
      HasDerivAt (Xcoef A k α) (A.ell * cP 1 * cP (A.app α - 1) * bracket A k α) α) ∧
    (A.app α - 1 = 1 →
      HasDerivAt (Xcoef A k α) (A.ell * k 1 α) α ∧ (A.ell : ℂ) * k 1 α = A.ell * bracket A k α / 2) := by
  obtain ⟨hDL, hb⟩ := catalogueL_facts hRH A hα
  have h1 := one_mem_poleSetQ
  have e1 : A.app α = 1 + (A.app α - 1) := by ring
  have e2 : A.app α = (A.app α - 1) + 1 := by ring
  obtain ⟨-, hd1b, -, hp1b⟩ := lem_J_i_proof A k hK1 h1 hb
  obtain ⟨-, hdb1, -, hpb1⟩ := lem_J_i_proof A k hK1 hb h1
  obtain ⟨z1b, d1b⟩ := hp1b α hDL e1
  obtain ⟨zb1, db1⟩ := hpb1 α hDL e2
  by_cases hb1 : A.app α - 1 = 1
  · rw [Xcoef_of_eq A k hb1]
    have hb1' := hb1
    rw [hb1] at hd1b z1b d1b
    refine ⟨hDL, hd1b, z1b, fun h => absurd hb1' h, fun _ => ⟨d1b, ?_⟩⟩
    simp only [bracket, hb1']
    ring
  · rw [Xcoef_of_ne A k hb1]
    refine ⟨hDL, ((hd1b.add hdb1).const_mul _), by simp [z1b, zb1], fun _ => ?_, fun h => absurd h hb1⟩
    have := (d1b.add db1).const_mul (cP 1 * cP (A.app α - 1))
    convert this using 1
    simp only [bracket]
    ring

end GoldbachBoundaries.Paper2.M4a
