import GoldbachBoundaries.Paper2.M4b.Rising

/-!
# Filler group C2 (poles and the boundary): shared helpers

General facts about `HasResidue` and `meromorphicOrderAt` used by `mero_mul_Qcont_app`, `Fmero_strip_facts`,
`Fmero_upper_facts`, `order_Fmero_nonneg` and `exists_pole_near_line`.
-/

noncomputable section

open Complex Filter Topology Set Metric

namespace GoldbachBoundaries.Paper2.M4b.FillC2

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- Multiplying by a function continuous at the pole multiplies the residue by its value there. -/
lemma hasResidue_mul_left {f g : ℂ → ℂ} {a c : ℂ} (hf : HasResidue f a c) (hg : ContinuousAt g a) :
    HasResidue (fun s => g s * f s) a (g a * c) := by
  have h := (hg.tendsto.mono_left nhdsWithin_le_nhds).mul hf
  refine h.congr' (Eventually.of_forall fun s => ?_)
  ring

/-- For a meromorphic function with a `HasResidue`, a pole is the same as a non-zero residue. -/
lemma order_neg_iff_of_hasResidue {f : ℂ → ℂ} {a c : ℂ} (hm : MeromorphicAt f a) (hf : HasResidue f a c) :
    meromorphicOrderAt f a < 0 ↔ c ≠ 0 := by
  constructor
  · intro ho hc
    have hge := hf.neg_one_le_meromorphicOrderAt hm
    have heq : meromorphicOrderAt f a = ((-1 : ℤ) : WithTop ℤ) := by
      cases h : meromorphicOrderAt f a with
      | top => rw [h] at ho; exact absurd ho (not_lt.mpr le_top)
      | coe n =>
        rw [h] at ho hge
        have h1 : (-1 : ℤ) ≤ n := by exact_mod_cast hge
        have h2 : n < 0 := by exact_mod_cast ho
        have : n = -1 := by omega
        rw [this]
    have hsub : MeromorphicAt (fun s : ℂ => s - a) a :=
      (analyticAt_id.sub analyticAt_const).meromorphicAt
    have hprod : MeromorphicAt ((fun s : ℂ => s - a) * f) a := hsub.mul hm
    have h0 : meromorphicOrderAt ((fun s : ℂ => s - a) * f) a = 0 := by
      rw [meromorphicOrderAt_mul hsub hm, meromorphicOrderAt_id_sub_const, heq]
      rfl
    obtain ⟨c', hc', hlim⟩ := (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero hprod).2 h0
    have : c' = c := tendsto_nhds_unique hlim hf
    exact hc' (this.trans hc)
  · intro hc
    rw [hf.meromorphicOrderAt_eq_neg_one hm hc]
    decide

/-- `s ↦ Qcont(L(s) - 1)` at a point `α` with `L(α) - 1 = b ∈ Σ_Q`: meromorphic, with residue `R_b/ℓ`. -/
lemma Qcont_app_facts (A : Aff) {α b : ℂ} (hb : b ∈ PoleSetQ) (hα : A.app α = 1 + b) :
    MeromorphicAt (fun s => Qcont (A.app s - 1)) α ∧
      HasResidue (fun s => Qcont (A.app s - 1)) α (Rcoef b / A.ell) := by
  have hl : (A.ell : ℂ) ≠ 0 := by exact_mod_cast A.ell_pos.ne'
  have hfun : (fun s => Qcont (A.app s - 1)) = fun s => Qcont ((A.ell : ℂ) * s + ((A.ell0 : ℂ) - 1)) := by
    funext s; simp only [Aff.app]; ring_nf
  have hb0 : 0 < b.re := (M1.poleSetQ_re_bounds hb).1
  refine ⟨?_, ?_⟩
  · have hm : MeromorphicAt Qcont (A.app α - 1) := by
      rw [hα, add_sub_cancel_left]; exact meromorphicAt_Qcont hb0
    have ha : AnalyticAt ℂ (fun s => A.app s - 1) α := by
      unfold Aff.app; fun_prop
    exact MeromorphicAt.comp_analyticAt (g := fun s => A.app s - 1) hm ha
  · have h1 := (M1.hasResidue_Qcont_Rcoef hb).comp_add_const ((A.ell0 : ℂ) - 1)
    have h2 := h1.comp_const_mul hl
    rw [hfun]
    have hpt : (b - ((A.ell0 : ℂ) - 1)) / (A.ell : ℂ) = α := by
      have : (A.ell : ℂ) * α + A.ell0 = 1 + b := hα
      field_simp
      linear_combination -this
    rw [hpt] at h2
    simpa [add_comm, add_left_comm, add_assoc] using h2

/-- An analytic function plus `g(s)Q(L(s)-1)` at a point `α` with `L(α) - 1 = b ∈ Σ_Q`, `g` analytic: meromorphic,
residue `g(α)R_b/ℓ`. -/
lemma add_mul_Qcont_app_facts (A : Aff) {h g : ℂ → ℂ} {α b : ℂ} (hh : AnalyticAt ℂ h α) (hg : AnalyticAt ℂ g α)
    (hb : b ∈ PoleSetQ) (hα : A.app α = 1 + b) :
    MeromorphicAt (fun s => h s + g s * Qcont (A.app s - 1)) α ∧
      HasResidue (fun s => h s + g s * Qcont (A.app s - 1)) α (g α * Rcoef b / A.ell) := by
  obtain ⟨hm, hr⟩ := Qcont_app_facts A hb hα
  refine ⟨hh.meromorphicAt.add (hg.meromorphicAt.mul hm), ?_⟩
  have h2 := (hasResidue_mul_left hr hg.continuousAt).add_analyticAt hh
  rw [mul_div_assoc]
  refine h2.congr (Eventually.of_forall fun s => ?_)
  simp [add_comm]

end GoldbachBoundaries.Paper2.M4b.FillC2
