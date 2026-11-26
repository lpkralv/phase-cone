import GoldbachBoundaries.Paper2.M5.Fill.meromorphicOn_TkStep

/-!
# M5 filler T3: `TkStep_pole_facts`

On the open `σ > m + 1/2`, `TkStep = I⁺ + g(s)Qcont(s - m)` with `g(s) = r_m K_s(m)` analytic (`TkStep_eq_upper`,
`differentiableOn_TkPlus_TkMin`). Off `m + 1` everything is analytic (`analyticAt_Qcont_of_RH`); at `m + 1` the residue
is `g(m + 1)·R_1 = Γ(1)/Γ(m + 1) = 1/m!` (`hasResidue_Qcont_one` shifted, `FillT3.rK_mul_KerS`), and the order is `-1`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- On `σ > m + 1/2`, `TkStep` is locally `I⁺ + g·Qcont(· - m)` with `I⁺`, `g` analytic. -/
lemma FillT3.upper_local (hRH : RiemannHypothesis) {m : ℕ} (hm : 1 ≤ m) {F H : ℂ → ℂ} (hP : TkPack m F H)
    {s : ℂ} (hs : (m : ℝ) + 1 / 2 < s.re) :
    TkStep m F =ᶠ[𝓝 s] (fun t => TkLine F (cPlusK m t) t + rK m * KerS t m * Qcont (t - m)) ∧
      AnalyticAt ℂ (fun t => TkLine F (cPlusK m t) t) s ∧ AnalyticAt ℂ (fun t => rK m * KerS t m) s := by
  have hU : IsOpen {t : ℂ | (m : ℝ) + 1 / 2 < t.re} := isOpen_lt continuous_const Complex.continuous_re
  have hn : {t : ℂ | (m : ℝ) + 1 / 2 < t.re} ∈ 𝓝 s := hU.mem_nhds hs
  refine ⟨Filter.mem_of_superset hn fun t ht => TkStep_eq_upper hRH hm hP t ht,
    (differentiableOn_TkPlus_TkMin hRH hm hP).1.analyticAt hn, FillT3.analyticAt_rK_KerS (by linarith)⟩

theorem TkStep_pole_facts (hRH : RiemannHypothesis) {m : ℕ} (hm : 1 ≤ m) {F H : ℂ → ℂ} (hP : TkPack m F H) :
    (∀ s : ℂ, ((m + 1 : ℕ) : ℝ) - 1 / 2 < s.re → s ≠ ((m + 1 : ℕ) : ℂ) → AnalyticAt ℂ (TkStep m F) s) ∧
      meromorphicOrderAt (TkStep m F) ((m + 1 : ℕ) : ℂ) = -1 ∧
      HasResidue (TkStep m F) ((m + 1 : ℕ) : ℂ) (1 / ((m + 1 - 1).factorial : ℂ)) := by
  -- the residue at `m + 1`
  set α : ℂ := ((m + 1 : ℕ) : ℂ) with hα
  have hαre : α.re = (m : ℝ) + 1 := by rw [hα]; push_cast; simp
  have hαs : (m : ℝ) + 1 / 2 < α.re := by rw [hαre]; linarith
  obtain ⟨hev, hI, hg⟩ := FillT3.upper_local hRH hm hP hαs
  have hgval : rK m * KerS α m = 1 / ((m + 1 - 1).factorial : ℂ) := by
    rw [FillT3.rK_mul_KerS hm, hα, show m + 1 - 1 = m by omega]
    have h1 : ((m + 1 : ℕ) : ℂ) - m = 1 := by push_cast; ring
    rw [h1, Complex.Gamma_one, Nat.cast_succ, Complex.Gamma_nat_eq_factorial]
  have hQ : HasResidue (fun t => Qcont (t - m)) α 1 := by
    have h := hasResidue_Qcont_one.comp_sub_const (m : ℂ)
    have h1 : (1 : ℂ) + m = α := by rw [hα]; push_cast; ring
    rwa [h1] at h
  have hres0 : HasResidue (fun t => TkLine F (cPlusK m t) t + rK m * KerS t m * Qcont (t - m)) α
      (1 / ((m + 1 - 1).factorial : ℂ)) := by
    have h2 := (M4b.FillC2.hasResidue_mul_left hQ hg.continuousAt).add_analyticAt hI
    rw [mul_one, hgval] at h2
    refine h2.congr (Eventually.of_forall fun t => ?_)
    simp only
    ring
  have hres : HasResidue (TkStep m F) α (1 / ((m + 1 - 1).factorial : ℂ)) :=
    hres0.congr (hev.filter_mono nhdsWithin_le_nhds).symm
  have hmer : MeromorphicAt (TkStep m F) α := by
    refine meromorphicOn_TkStep hRH hm hP α ?_
    show ((m + 1 : ℕ) : ℝ) - 1 < α.re
    rw [hαre]; push_cast; linarith
  have hne : (1 / ((m + 1 - 1).factorial : ℂ)) ≠ 0 := by
    have : ((m + 1 - 1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    exact one_div_ne_zero this
  refine ⟨fun s hs hsα => ?_, hres.meromorphicOrderAt_eq_neg_one hmer hne, hres⟩
  have hs' : (m : ℝ) + 1 / 2 < s.re := by push_cast at hs; linarith
  obtain ⟨hev', hI', hg'⟩ := FillT3.upper_local hRH hm hP hs'
  have hre : 1 / 2 < (s - m).re := by simp; linarith
  have hne1 : s - m ≠ 1 := fun h => hsα (by rw [hα]; push_cast; linear_combination h)
  have hQa : AnalyticAt ℂ Qcont (s - m) := TIdentity.analyticAt_Qcont_of_RH hRH hre hne1
  have hap : AnalyticAt ℂ (fun t : ℂ => t - m) s := by fun_prop
  exact (hI'.add (hg'.mul (hQa.comp_of_eq hap rfl))).congr hev'.symm

end GoldbachBoundaries.Paper2.M5
