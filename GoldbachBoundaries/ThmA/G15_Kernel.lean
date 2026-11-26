import GoldbachBoundaries.ThmA.G14_Geometry

/-!
# G15. Parametric integrals, the kernel, `X_α`, the branch `P_v`, and `P` along `s - 𝒮`

Paper: `lem:kernel`, Section 2.3 (`E`, `P_v`, eq. `jumpP`), `lem:Sigma`(iii) (replaced: `P` along a
segment is defined by an explicit integral of `Q`, `Defs.lean`), `thm:local` (values of `X'_α(α)`).

**Integrated layout.** The 8 lemmas this file stated with `sorry`
(`differentiableOn_intervalIntegral_of_continuousOn`, `J_spec`, `X_deriv_spec`, `exists_Eaux`,
`Pv_spec`, `Qcont_pole_split`, `PsegA_split`, `analyticAt_N1A`) are proved in `Fill/<name>.lean`,
statements unchanged, each with its sketch as docstring. This file keeps only the definitions and
real proofs that do not use them; `X_differentiableOn` moved to `Fill/J_spec.lean`, `Mon_analyticOn`
moved to `Fill/J_spec.lean`, `MSpan_analyticOn` moved to `Fill/J_spec.lean`, `Eaux_spec` moved to
`Fill/exists_Eaux.lean`. `Assembly.lean` imports all of it.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory
open scoped Interval

namespace GoldbachBoundaries.ThmA

/-! ### Real proofs -/

theorem J_self (a b : ℂ) : J a b (a + b) = 0 := by
  simp [J, segInt]

theorem X_self (α : ℂ) : X α α = 0 := by
  unfold X
  split_ifs with h
  · subst h; simp only [J, segInt]; norm_num
  · simp [J, segInt]

theorem Mon_mem_MSpan {α : ℂ} (hα : α ∈ catalogue) : Mon α ∈ MSpan :=
  AddSubgroup.subset_closure ⟨α, hα, rfl⟩

/-- `N₁` depends on the anchor function only through its value at `s - w_b`. -/
theorem N1A_congr {κ b : ℝ} {A A' : ℂ → ℂ} {s : ℂ} (h : A (s - wb κ b) = A' (s - wb κ b)) :
    N1A κ b A s = N1A κ b A' s := by
  simp only [N1A, PsegA, h]

end GoldbachBoundaries.ThmA
