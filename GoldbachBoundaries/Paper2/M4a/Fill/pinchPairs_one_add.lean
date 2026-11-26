import GoldbachBoundaries.Paper2.M4a.Defs
import GoldbachBoundaries.SigmaFinite
import GoldbachBoundaries.Density

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
namespace GoldbachBoundaries.Paper2.M4a
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

private lemma A_re_le_half (hRH : RiemannHypothesis) {a : ℂ} (ha : a ∈ PoleSetQ) (h : a ≠ 1) :
    a.re ≤ 1 / 2 := by
  by_contra hn
  have : a ∈ PoleSetQ ∩ halfPlane (1 / 2) := ⟨ha, lt_of_not_ge hn⟩
  rw [(lem_Sigma_iv_proof hRH).1] at this
  exact h (mem_singleton_iff.mp this)

private lemma A_one_of_sum (hRH : RiemannHypothesis) {a b : ℂ}
    (ha : a ∈ PoleSetQ) (hb : b ∈ PoleSetQ) (h : 1 < (a + b).re) : a = 1 ∨ b = 1 := by
  by_contra hn
  push Not at hn
  have := A_re_le_half hRH ha hn.1
  have := A_re_le_half hRH hb hn.2
  simp only [add_re] at h
  linarith


/-- **The pairs at `1 + b`** (RH). `⊇`: `1 ∈ Σ` and `1 + b = b + 1`. `⊆`: a pair `(a', b')` with `a' + b' = 1 + b` has
`Re(a' + b') = 1 + Re b > 1` (M1's `poleSetQ_re_bounds`: `Re b > 0`), so as in `sub_one_mem_poleSetQ_of_mem_pinch` one
of `a', b'` is `1`, and the other is `b` (cancel). (For `b = 1` both pairs are `(1, 1)`.) Size: 60–120 lines. -/
theorem pinchPairs_one_add (hRH : RiemannHypothesis) {b : ℂ} (hb : b ∈ PoleSetQ) :
    pinchPairs (1 + b) = {(1, b), (b, 1)} := by
  ext ⟨a, c⟩
  constructor
  · rintro ⟨ha, hc, heq⟩
    have hre : 1 < (a + c).re := by
      rw [heq, add_re, one_re]
      have := (poleSetQ_re_bounds hb).1
      linarith
    rcases A_one_of_sum hRH ha hc hre with rfl | rfl
    · have : c = b := add_left_cancel heq
      subst c
      simp
    · have : a = b := by linear_combination heq
      subst a
      simp
  · intro hp
    simp only [mem_insert_iff, mem_singleton_iff, Prod.mk.injEq] at hp
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨one_mem_poleSetQ, hb, rfl⟩
    · exact ⟨hb, one_mem_poleSetQ, add_comm _ _⟩

end GoldbachBoundaries.Paper2.M4a
