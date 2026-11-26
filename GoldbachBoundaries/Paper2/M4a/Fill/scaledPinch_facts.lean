import GoldbachBoundaries.Paper2.M4a.Restrict

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
namespace GoldbachBoundaries.Paper2.M4a
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **Facts about a scaled-zero pinch** (no RH). `b = ρ/n` is in `Σ` (`n` squarefree). `Re b = Re ρ/n ∈ (0, 1)`, so
`Re L(α) = 1 + Re b ∈ (1, 2)`: `α ∈ ℍ_L`, `α ∈ D_L`, `α` is not on the line, and `b ≠ 1`. `L(α) = 1 + b ∈ Pinch`
(`1 ∈ Σ`), so `α ∈ 𝒞_L`, and `α ∈ scaledZeroPinches A` by definition. Size: 40–80 lines. -/
theorem scaledPinch_facts (A : Aff) {α ρ : ℂ} {n : ℕ} (hρ : ρ ∈ NontrivialZeros) (hn : 1 ≤ n)
    (hsq : Squarefree n) (h : A.app α = 1 + ρ / (n : ℂ)) :
    α ∈ catalogueL A ∧ α ∈ A.DL ∧ α ∉ A.lineL ∧ ρ / (n : ℂ) ∈ PoleSetQ ∧ ρ / (n : ℂ) ≠ 1 ∧
      A.app α - 1 = ρ / (n : ℂ) ∧ α ∈ scaledZeroPinches A := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hb : ρ / (n : ℂ) ∈ PoleSetQ := Or.inr ⟨n, hn, hsq, ρ, hρ, rfl⟩
  have hp : 0 < (ρ / (n : ℂ)).re := (poleSetQ_re_bounds hb).1
  have hlt : (ρ / (n : ℂ)).re < 1 := by
    rw [Complex.div_natCast_re]
    exact (div_le_self hρ.2.1.le hnR).trans_lt hρ.2.2
  have hre : (A.app α).re = 1 + (ρ / (n : ℂ)).re := by rw [h, add_re, one_re]
  have hH : α ∈ A.HL := by change 1 < (A.app α).re; linarith
  refine ⟨⟨hH, 1, one_mem_poleSetQ, ρ / (n : ℂ), hb, h⟩, ?_, ?_, hb, ?_, ?_, ?_⟩
  · change 1 < (A.app α).re ∧ (A.app α).re < 3
    constructor <;> linarith
  · change ¬ (A.app α).re = 1
    linarith
  · intro heq
    have := congrArg Complex.re heq
    simp only [one_re] at this
    linarith
  · rw [h]; ring
  · exact ⟨ρ, hρ, n, hn, hsq, h⟩

end GoldbachBoundaries.Paper2.M4a
