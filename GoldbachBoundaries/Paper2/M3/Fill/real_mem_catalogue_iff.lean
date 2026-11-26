import GoldbachBoundaries.Paper2.M3.AConst
import GoldbachBoundaries.Paper2.M3.Defs

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
namespace GoldbachBoundaries.Paper2.M3
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- A zero in the open strip cannot be real. -/
private lemma A1_im_ne_zero {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) : ρ.im ≠ 0 := by
  intro hi
  have he : (ρ.re : ℂ) = ρ := Complex.ext (by simp) (by simp [hi])
  exact riemannZeta_ne_zero_of_mem_Ioo ⟨hρ.2.1, hρ.2.2⟩ (he.symm ▸ hρ.1)


/-- **Real catalogue points in `(1, 2)`** (unconditional). `2 ∉ (1, 2)`. A point `1 + ρ/n` (`n ≥ 1`) is real only if
`Im ρ = 0`, and then `ρ = Re ρ ∈ (0, 1)` is a real zero, excluded by `riemannZeta_ne_zero_of_mem_Ioo` (paper 1). So
`(x : ℂ) ∈ 𝒞` iff `x = 1 + 1/k`, `k ≥ 2` squarefree (unfold `catalogue`, compare imaginary parts). Size: 40–80
lines. -/
theorem real_mem_catalogue_iff {x : ℝ} (hx : x ∈ Ioo (1 : ℝ) 2) :
    (x : ℂ) ∈ catalogue ↔ ∃ k : ℕ, 2 ≤ k ∧ Squarefree k ∧ (x : ℂ) = 1 + 1 / (k : ℂ) := by
  constructor
  · intro h
    rcases h with (h | h) | h
    · have he : (x : ℂ) = 2 := h
      have := congrArg Complex.re he
      simp only [ofReal_re, re_ofNat] at this
      linarith [hx.2]
    · exact h
    · obtain ⟨n, hn, _, ρ, hρ, he⟩ := h
      have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
      have he' : ρ = ((x : ℂ) - 1) * n := by
        apply (div_eq_iff hn0).mp
        linear_combination -he
      have hi := congrArg Complex.im he'
      simp at hi
      exact False.elim (A1_im_ne_zero hρ hi)
  · intro h
    exact Or.inl (Or.inr h)

end GoldbachBoundaries.Paper2.M3
