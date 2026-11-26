import GoldbachBoundaries.Paper2.M4b.Rising
import GoldbachBoundaries.Paper2.M4b.Fill.Ilog_eq_of_no_pole

/-!
# M4b filler C1: shared helpers for the continuation `Fmero`

Facts about the lines `cMinus`, `cPlus`, and a two-sided form of `Ilog_eq_of_no_pole` (both lines left of `1`, and on
the same side of `L(s) - 1`). They live in the sub-namespace `FillC1`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M4b.FillC1

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1 GoldbachBoundaries.Paper2.M4b

lemma cPlus_le_left (A : Aff) (s : ℂ) : cPlus A s ≤ 3 / 4 := min_le_left _ _

lemma cPlus_le_right (A : Aff) (s : ℂ) : cPlus A s ≤ ((A.app s).re - 1 / 2) / 2 := min_le_right _ _

lemma half_lt_cPlus (A : Aff) {s : ℂ} (hs : 3 / 2 < (A.app s).re) : 1 / 2 < cPlus A s :=
  lt_min (by norm_num) (by linarith)

/-- Two lines left of `1`, on the same side of `L(s) - 1`, give the same integral (`Ilog_eq_of_no_pole`). -/
lemma Ilog_eq_of_lines (hRH : RiemannHypothesis) (A : Aff) (k : ℂ → ℂ → ℂ) (hK1 : K1 A k) (hK2 : K2 A k)
    {s : ℂ} (hs : s ∈ A.DL) {a b : ℝ} (ha : 1 / 2 < a) (hb : 1 / 2 < b) (ha' : a + 1 / 2 < (A.app s).re)
    (hb' : b + 1 / 2 < (A.app s).re) (ha1 : a < 1) (hb1 : b < 1)
    (hside : (a < (A.app s).re - 1 ∧ b < (A.app s).re - 1) ∨
      ((A.app s).re - 1 < a ∧ (A.app s).re - 1 < b)) :
    Ilog A k a s = Ilog A k b s := by
  rcases le_total a b with hab | hab
  · refine (Ilog_eq_of_no_pole hRH A k hK1 hK2 hs ha hab hb' (fun h => by linarith [h.2]) ?_).symm
    rintro ⟨h1, h2⟩
    rcases hside with h | h <;> linarith [h.1, h.2]
  · refine Ilog_eq_of_no_pole hRH A k hK1 hK2 hs hb hab ha' (fun h => by linarith [h.2]) ?_
    rintro ⟨h1, h2⟩
    rcases hside with h | h <;> linarith [h.1, h.2]

/-- `t ↦ k(1, t)` is holomorphic on `D_L` ((K1): `1 ∈ Str(t)`). -/
lemma analyticOnNhd_k_one (A : Aff) (k : ℂ → ℂ → ℂ) (hK1 : K1 A k) :
    AnalyticOnNhd ℂ (fun t => k 1 t) A.DL := by
  refine DifferentiableOn.analyticOnNhd (fun s hs => ?_) (M4a.isOpen_DL A)
  have hd := M4a.FillE.differentiableAt_of_K1 hK1 hs (M4a.FillE.one_mem_Str hs).1
    (M4a.FillE.one_mem_Str hs).2
  have hc : DifferentiableAt ℂ (fun t : ℂ => ((1 : ℂ), t)) s := by fun_prop
  exact (DifferentiableAt.comp (g := fun p : ℂ × ℂ => k p.1 p.2) (f := fun t : ℂ => ((1 : ℂ), t)) s hd
    hc).differentiableWithinAt

/-- `t ↦ Qcont(L(t) - 1)` is meromorphic on `ℍ_L`. -/
lemma meromorphicAt_Qcont_app (A : Aff) {s : ℂ} (hs : s ∈ A.HL) :
    MeromorphicAt (fun t => Qcont (A.app t - 1)) s := by
  have hs' : 1 < (A.app s).re := hs
  have hpos : 0 < (A.app s - 1).re := by rw [sub_re, one_re]; linarith
  have hg : AnalyticAt ℂ (fun t => A.app t - 1) s := by unfold Aff.app; fun_prop
  exact MeromorphicAt.comp_analyticAt (f := Qcont) (g := fun t => A.app t - 1) (x := s)
    (meromorphicAt_Qcont hpos) hg

end GoldbachBoundaries.Paper2.M4b.FillC1
