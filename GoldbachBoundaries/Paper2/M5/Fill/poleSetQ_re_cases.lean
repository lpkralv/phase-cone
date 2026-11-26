import GoldbachBoundaries.Paper2.M5.Defs

/-! Filler group Q: `poleSetQ_re_cases` (`General.lean`). -/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **The points of `Σ_Q` under RH, by real part.** `1`; `1/2` (`k = 2`); `1/k`, `k ≥ 3`, with real part `≤ 1/3`;
`ρ/n` with `Re ρ = 1/2` (RH): `n = 1` is a zero on the line, `n ≥ 2` has real part `1/(2n) ≤ 1/4`. -/
theorem poleSetQ_re_cases (hRH : RiemannHypothesis) {a : ℂ} (ha : a ∈ PoleSetQ) :
    a = 1 ∨ (a.re = 1 / 2 ∧ (a = 1 / 2 ∨ a ∈ NontrivialZeros)) ∨ a.re ≤ 1 / 3 := by
  rcases ha with (ha | ⟨k, hk, -, rfl⟩) | ⟨n, hn, -, ρ, hρ, rfl⟩
  · exact Or.inl ha
  · rcases eq_or_lt_of_le hk with h2 | h3
    · subst h2
      right; left
      refine ⟨?_, Or.inl ?_⟩
      · rw [re_one_div_natCast]; norm_num
      · norm_num
    · right; right
      rw [re_one_div_natCast]
      have hk' : (3 : ℝ) ≤ k := by exact_mod_cast h3
      exact one_div_le_one_div_of_le (by norm_num) hk'
  · have hre := sigmaFinite_re_eq_half hRH hρ
    rcases eq_or_lt_of_le hn with h1 | h2
    · subst h1
      right; left
      simp only [Nat.cast_one, div_one]
      exact ⟨hre, Or.inr hρ⟩
    · right; right
      rw [Complex.div_natCast_re, hre]
      have hn' : (2 : ℝ) ≤ n := by exact_mod_cast h2
      rw [div_le_iff₀ (by linarith)]
      nlinarith

end GoldbachBoundaries.Paper2.M5
