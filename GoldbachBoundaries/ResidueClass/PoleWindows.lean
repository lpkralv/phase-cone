import GoldbachBoundaries.ResidueClass.Correction

/-! # Finiteness of the correction's boundary poles in bounded windows -/

noncomputable section

open Complex Set

namespace GoldbachBoundaries.ResidueClass

variable {q : ℕ} [NeZero q]

/-- Pole ordinates of the correction in a closed bounded interval form a finite set. -/
theorem finite_W_poles_line_Icc (a b : ℝ) :
    {t : ℝ | t ∈ Icc a b ∧ meromorphicOrderAt (W q) (1 + t * I) < 0}.Finite := by
  let z (t : ℝ) : ℂ := 1 + (t : ℂ) * I
  have hz : Function.Injective z := fun x y h ↦ by simpa [z] using congrArg Complex.im h
  let S := z '' Icc a b
  have hS : IsCompact S := isCompact_Icc.image (show Continuous z by dsimp [z]; fun_prop)
  have hW : MeromorphicOn (W q) S := fun w _ ↦ meromorphic_W q w
  refine (((MeromorphicOn.divisor (W q) S).finiteSupport hS).preimage hz.injOn).subset ?_
  intro t ht
  have ht' : z t ∈ S := ⟨t, ht.1, rfl⟩
  have hneg : meromorphicOrderAt (W q) (z t) < 0 := ht.2
  change MeromorphicOn.divisor (W q) S (z t) ≠ 0
  rw [MeromorphicOn.divisor_apply hW ht']
  cases h : meromorphicOrderAt (W q) (z t) with
  | top => simp [h] at hneg
  | coe n =>
    rw [h] at hneg
    have hn : n < 0 := by exact_mod_cast hneg
    simpa [h] using hn.ne

end GoldbachBoundaries.ResidueClass
