import GoldbachBoundaries.Paper2.M4b.Rising
import GoldbachBoundaries.Paper2.M4b.Fill.Fmero_strip_facts
import GoldbachBoundaries.Paper2.M4b.Fill.Fmero_upper_facts

/-! Filler for `order_Fmero_nonneg` (M4b, group C2). -/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M4b

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **No pole when `𝔟 ≡ 0`** (RH, (K1), (K2), (R); proof of (ii)). `ℍ_L ⊆ stripL ∪ upperL ∪ R_L` (`HL_subset`). On
`stripL ⊆ D_L` the right side of `Fmero_strip_facts` is false (`𝔟 = 0`), so the order is `≥ 0`. On `upperL ∪ R_L` away
from `s₂`, `Fmero` is analytic (`Fmero_upper_facts`). At `s₂ ∈ D_L` (`Re L = 2`), `L(s₂) - 1 = 1` gives
`𝔟(s₂) = 2k(1,s₂)`, so `k(1,s₂) = 0` and the order is `≥ 0` (`Fmero_upper_facts`). Size: 50–100 lines. -/
theorem order_Fmero_nonneg (hRH : RiemannHypothesis) (A : Aff) (k : ℂ → ℂ → ℂ) (W : ℂ → ℕ → ℕ → ℂ)
    (hK1 : K1 A k) (hK2 : K2 A k) (hR : HypR A k W Q) (hb : ∀ s ∈ A.DL, bracket A k s = 0) :
    ∀ s ∈ A.HL, 0 ≤ meromorphicOrderAt (Fmero A k W) s := by
  intro s hs
  rcases HL_subset A hs with (hst | hup) | hRL
  · obtain ⟨-, hiff⟩ := (Fmero_strip_facts hRH A k W hK1 hK2).1 s hst
    refine not_lt.mp fun h => ?_
    obtain ⟨-, -, -, hne⟩ := hiff.mp h
    exact hne (hb s (stripL_subset_DL A hst))
  all_goals
    by_cases h2 : A.app s = 2
    · have hDL : s ∈ A.DL := by
        show 1 < (A.app s).re ∧ (A.app s).re < 3
        rw [h2]; norm_num
      have hk : k 1 s = 0 := by
        have h := hb s hDL
        rw [bracket, show A.app s - 1 = 1 by rw [h2]; norm_num] at h
        linear_combination h / 2
      exact ((Fmero_upper_facts hRH A k W hK1 hK2 hR).1 s h2).2.2 hk
    · first
        | exact ((Fmero_upper_facts hRH A k W hK1 hK2 hR).2 s (Or.inl hup) h2).meromorphicOrderAt_nonneg
        | exact ((Fmero_upper_facts hRH A k W hK1 hK2 hR).2 s (Or.inr hRL) h2).meromorphicOrderAt_nonneg

end GoldbachBoundaries.Paper2.M4b
