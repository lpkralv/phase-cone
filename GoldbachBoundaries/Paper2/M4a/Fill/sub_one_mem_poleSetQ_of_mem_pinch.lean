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


/-- **A pinch with real part above `1` is `1 + b`** (RH). Write `w = a' + b'`, `a', b' ∈ Σ`. If neither is `1`, both
have real part `≤ 1/2` (`lem_Sigma_iv hRH`: `Σ ∩ {Re > 1/2} = {1}`), so `Re w ≤ 1`, a contradiction. So `a' = 1`
(then `w - 1 = b'`) or `b' = 1` (then `w - 1 = a'`). Size: 40–80 lines. -/
theorem sub_one_mem_poleSetQ_of_mem_pinch (hRH : RiemannHypothesis) {w : ℂ} (hw : w ∈ Pinch)
    (hre : 1 < w.re) : w - 1 ∈ PoleSetQ := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hw
  rcases A_one_of_sum hRH ha hb hre with rfl | rfl
  · simpa using hb
  · simpa using ha

end GoldbachBoundaries.Paper2.M4a
