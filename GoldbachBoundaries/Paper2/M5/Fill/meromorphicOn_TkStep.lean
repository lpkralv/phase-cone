import GoldbachBoundaries.Paper2.M5.Fill.TkStep_eq_strip
import GoldbachBoundaries.Paper2.M5.Fill.differentiableOn_TkPlus_TkMin

/-!
# M5 filler T3: `meromorphicOn_TkStep`

`{σ > m}` is covered by the open sets `{σ > m + 1/2}` and `{m < σ < m + 1}`; on each, `TkStep` equals a meromorphic
expression (`TkStep_eq_upper`, `TkStep_eq_strip`). As M4b's `meromorphicOn_Fmero`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

theorem meromorphicOn_TkStep (hRH : RiemannHypothesis) {m : ℕ} (hm : 1 ≤ m) {F H : ℂ → ℂ}
    (hP : TkPack m F H) :
    MeromorphicOn (TkStep m F) (halfPlane (((m + 1 : ℕ) : ℝ) - 1)) := by
  intro s hs
  have hs' : (m : ℝ) < s.re := by
    have : ((m + 1 : ℕ) : ℝ) - 1 < s.re := hs
    push_cast at this; linarith
  obtain ⟨hIp, hIm⟩ := differentiableOn_TkPlus_TkMin hRH hm hP
  have hg : MeromorphicAt (fun t => rK m * KerS t m * Qcont (t - m)) s :=
    (FillT3.analyticAt_rK_KerS hs').meromorphicAt.mul (FillT3.meromorphicAt_Qcont_sub hs')
  by_cases hmid : (m : ℝ) + 1 / 2 < s.re
  · have hU : IsOpen {t : ℂ | (m : ℝ) + 1 / 2 < t.re} := isOpen_lt continuous_const Complex.continuous_re
    have hn : {t : ℂ | (m : ℝ) + 1 / 2 < t.re} ∈ 𝓝 s := hU.mem_nhds hmid
    have hev : (fun t => TkLine F (cPlusK m t) t + rK m * KerS t m * Qcont (t - m)) =ᶠ[𝓝 s] TkStep m F := by
      filter_upwards [hn] with t ht
      exact (TkStep_eq_upper hRH hm hP t ht).symm
    have hmer : MeromorphicAt (fun t => TkLine F (cPlusK m t) t + rK m * KerS t m * Qcont (t - m)) s :=
      (hIp.analyticAt hn).meromorphicAt.add hg
    exact hmer.congr (hev.filter_mono nhdsWithin_le_nhds)
  · have hs2 : s.re < (m : ℝ) + 1 := by linarith [not_lt.mp hmid]
    have hU : IsOpen {t : ℂ | (m : ℝ) < t.re ∧ t.re < m + 1} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt Complex.continuous_re continuous_const)
    have hn : {t : ℂ | (m : ℝ) < t.re ∧ t.re < m + 1} ∈ 𝓝 s := hU.mem_nhds ⟨hs', hs2⟩
    have hev : (fun t => TkLine F (cMinK m t) t + F (t - 1) / (t - 1) + rK m * KerS t m * Qcont (t - m))
        =ᶠ[𝓝 s] TkStep m F := by
      filter_upwards [hn] with t ht
      exact (TkStep_eq_strip hRH hm hP t ht.1 ht.2).symm
    have hF1 : MeromorphicAt (fun t => F (t - 1)) s := by
      have hre : (m : ℝ) - 1 < (s - 1).re := by simp; linarith
      exact MeromorphicAt.comp_analyticAt (g := fun t : ℂ => t - 1) (hP.1 (s - 1) hre) (by fun_prop)
    have hdiv : MeromorphicAt (fun t => F (t - 1) / (t - 1)) s :=
      hF1.div (analyticAt_id.sub analyticAt_const).meromorphicAt
    have hmer : MeromorphicAt
        (fun t => TkLine F (cMinK m t) t + F (t - 1) / (t - 1) + rK m * KerS t m * Qcont (t - m)) s :=
      ((hIm.analyticAt hn).meromorphicAt.add hdiv).add hg
    exact hmer.congr (hev.filter_mono nhdsWithin_le_nhds)

end GoldbachBoundaries.Paper2.M5
