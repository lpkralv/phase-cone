import GoldbachBoundaries.ResidueClass.Zeros

/-! # Off-line zeros of the inducing primitive family -/

noncomputable section

open Complex Set

namespace GoldbachBoundaries.ResidueClass

variable {q : ℕ} [NeZero q]

/-- All distinct off-line strip zeros of the inducing family, including real
zeros and the zeros of zeta from the principal character. -/
def OffLineZeros (q : ℕ) [NeZero q] : Set ℂ :=
  {ρ | (∃ χ : DirichletCharacter ℂ q, ρ ∈ primitiveZeros χ) ∧ ρ.re ≠ 1 / 2}

theorem exists_high_critical (hE : (OffLineZeros q).Finite) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ (χ : DirichletCharacter ℂ q) ρ,
      ρ ∈ primitiveZeros χ → T ≤ |ρ.im| → ρ.re = 1 / 2 := by
  obtain ⟨T, hT⟩ := (hE.image (fun ρ : ℂ ↦ |ρ.im|)).bddAbove
  refine ⟨max T 0 + 1, by positivity, fun χ ρ hρ hh ↦ ?_⟩
  by_contra h
  have := hT (mem_image_of_mem (fun ρ : ℂ ↦ |ρ.im|)
    (show ρ ∈ OffLineZeros q from ⟨⟨χ, hρ⟩, h⟩))
  linarith [le_max_left T 0]

theorem OffLineZeros.re_pos {ρ : ℂ} (hρ : ρ ∈ OffLineZeros q) : 0 < ρ.re := by
  obtain ⟨χ, hχ⟩ := hρ.1
  exact hχ.2.1

theorem OffLineZeros.re_lt_one {ρ : ℂ} (hρ : ρ ∈ OffLineZeros q) : ρ.re < 1 := by
  obtain ⟨χ, hχ⟩ := hρ.1
  exact hχ.2.2

/-- Choose a contour to the left of every strip zero and far enough left that
the Mellin remainder from its product with an exceptional zero crosses one. -/
theorem exists_exception_strip (hE : (OffLineZeros q).Finite) :
    ∃ B δ : ℝ, 1 / 2 ≤ B ∧ B < 1 ∧ 0 < δ ∧ δ < 1 / 2 ∧ B + δ < 1 ∧
      ∀ ρ ∈ OffLineZeros q, δ < ρ.re ∧ ρ.re ≤ B := by
  classical
  let S := insert (1 / 2 : ℝ) (Complex.re '' OffLineZeros q)
  have hS : S.Finite := (hE.image _).insert _
  have hS₀ : S.Nonempty := ⟨1 / 2, mem_insert _ _⟩
  have hb (x : ℝ) (hx : x ∈ S) : 0 < x ∧ x < 1 := by
    rcases hx with rfl | ⟨ρ, hρ, rfl⟩
    · norm_num
    · exact ⟨OffLineZeros.re_pos hρ, OffLineZeros.re_lt_one hρ⟩
  let B := sSup S
  let a := sInf S
  have hB₀ : 1 / 2 ≤ B := le_csSup hS.bddAbove (mem_insert _ _)
  have ha₀ : 0 < a := (hb a (hS₀.csInf_mem hS)).1
  have hB₁ : B < 1 := (hb B (hS₀.csSup_mem hS)).2
  let δ := min a (1 - B) / 2
  have hδ : 0 < δ := div_pos (lt_min ha₀ (sub_pos.mpr hB₁)) (by norm_num)
  have hδa : δ < a := by
    dsimp [δ]
    linarith [min_le_left a (1 - B)]
  have hδB : δ < 1 - B := by
    dsimp [δ]
    linarith [min_le_right a (1 - B)]
  refine ⟨B, δ, hB₀, hB₁, hδ, by linarith, by linarith, fun ρ hρ ↦ ?_⟩
  have hm : ρ.re ∈ S := mem_insert_of_mem _ (mem_image_of_mem _ hρ)
  exact ⟨hδa.trans_le (csInf_le hS.bddBelow hm), le_csSup hS.bddAbove hm⟩

/-- The positive-sign coefficient, so the explicit zero residue is its negative. -/
def exceptionalWeight (q : ℕ) [NeZero q] (ρ : ℂ) : ℂ :=
  (q.totient : ℂ)⁻¹ * (totalMult q ρ : ℂ) * Gamma ρ

/-- The sum of the exceptional zero contributions with the residue sign removed. -/
def exceptionalTerm (q : ℕ) [NeZero q] (E : Finset ℂ) (x : ℝ) : ℂ :=
  ∑ ρ ∈ E, exceptionalWeight q ρ * (x : ℂ) ^ (-ρ)

end GoldbachBoundaries.ResidueClass
