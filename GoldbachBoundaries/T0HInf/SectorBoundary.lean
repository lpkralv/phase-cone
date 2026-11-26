import GoldbachBoundaries.T0HInf.SectorBridge
import GoldbachBoundaries.T0HInf.Regularization
import GoldbachBoundaries.T0HInf.CriticalCatalogue

/-! The T₀ natural-boundary proof with the sector cone supplying both nonzero atoms. -/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory

namespace GoldbachBoundaries.T0HInf

open GoldbachBoundaries Paper2 Phi2Proof
open _root_.GoldbachBoundaries.Phi2HInf
  (StirlingStrip offLineZeros criticalPairIdx criticalVal finite_exceptional_critical
    exists_large_critical_pair)

private theorem exists_interior_pole_near_of_sector (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3)
    (hL : ZLittlewood) (hStir : StirlingStrip) {E : Finset NontrivialZeros} (hE : IsCutoff E)
    (hinf : Phi2HInf.rightZeros.Infinite) (y : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ s ∈ HH, dist s (1 + (y : ℂ) * I) < ε ∧ meromorphicOrderAt (T0c E) s = -1 := by
  let z : ℂ := 1 + (y : ℂ) * I
  let Y := |y| + 1
  have hY : 0 < Y := by dsimp [Y]; positivity
  obtain ⟨X, hXY, hX⟩ := collisionAtom_ne_zero_of_large_of_sector hH hZ1 hZ2 hStir hY
  let D : Set ℂ := {s | |s.im| ≤ Y ∧ ∃ p : Phi2HInf.collisionIdx s,
    |(p.1.1 : ℂ).im| ≤ X ∨ |(p.1.2 : ℂ).im| ≤ X}
  have hD : D.Finite := Phi2HInf.finite_low_collision X Y
  let V := (D \ {z})ᶜ ∩ {s : ℂ | |s.im| < Y}
  have hV : IsOpen V := ((hD.sdiff (t := {z})).isClosed.isOpen_compl).inter
    (isOpen_lt continuous_im.abs continuous_const)
  have hzV : z ∈ V := ⟨by simp, by simp [z, Y]⟩
  obtain ⟨d, hd, hdV⟩ := Metric.isOpen_iff.mp hV z hzV
  have hzW : z ∈ halfPlane crossingAbscissa := by
    change crossingAbscissa < z.re
    simpa [z] using (cutoff_bounds hH).2.2.2.2
  have hW := meromorphicOn_W hH hZ1 hZ2 hZ3 hStir hE z hzW
  obtain ⟨r, hr, hrA⟩ := Metric.mem_nhdsWithin_iff.mp hW.eventually_analyticAt
  obtain ⟨s, hs, hsd, hrep⟩ := Phi2HInf.exists_right_pair_near hH hZ1 hL hinf y
    (lt_min hε (lt_min hd hr))
  have hsV := hdV (show s ∈ ball z d from
    hsd.trans_le ((min_le_right ε (min d r)).trans (min_le_left d r)))
  have hsne : s ≠ z := by
    intro he
    have : 1 < s.re := hs
    simp [he, z] at this
  have hsD : s ∉ D := fun he => hsV.1 ⟨he, hsne⟩
  have hatom : collisionAtom s ≠ 0 := hX s hsV.2.le hrep (by
    intro p
    constructor <;> by_contra h
    · exact hsD ⟨hsV.2.le, p, Or.inl (not_lt.mp h)⟩
    · exact hsD ⟨hsV.2.le, p, Or.inr (not_lt.mp h)⟩)
  have hWA : AnalyticAt ℂ (W E) s := hrA ⟨
    hsd.trans_le ((min_le_right ε (min d r)).trans (min_le_right d r)), hsne⟩
  have hΓ : ContinuousAt (fun z : ℂ => 1 / Gamma z) s := by
    simpa only [one_div] using differentiable_one_div_Gamma.continuous.continuousAt (x := s)
  have hres : HasResidue (T0c E) s (collisionAtom s / Gamma s) := by
    have h := ((hasResidue_C hH hZ1 hZ2 hs).add_analyticAt hWA).mul_continuousAt' hΓ
    convert! h using 1
    · ext w
      simp only [T0c, one_div, div_eq_mul_inv, one_mul]
    · simp only [one_div, div_eq_mul_inv, one_mul]
  have hmer := (t0_hinf_continuation hH hZ1 hZ2 hZ3 hStir hE).1 s hs
  exact ⟨s, hs, hsd.trans_le (min_le_left _ _), hres.meromorphicOrderAt_eq_neg_one hmer
    (div_ne_zero hatom (Gamma_ne_zero_of_re_pos (by have : 1 < s.re := hs; linarith)))⟩

private theorem exists_tau_criticalAtom_ne_zero_of_sector (hZ1 : Z1) (hZ2 : Z2) (hL : ZLittlewood)
    (hStir : StirlingStrip) (hfin : offLineZeros.Finite) (y : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ τ : ℝ, τ ≠ y ∧ |τ - y| < ε ∧ criticalAtom τ ≠ 0 := by
  set Y : ℝ := |y| + ε with hYdef
  have hY : 0 < Y := by positivity
  obtain ⟨H, hYH, hH⟩ := criticalAtom_ne_zero_of_large_of_sector hZ1 hZ2 hStir hY
  set E := {τ : ℝ | |τ| ≤ Y ∧ ∃ p : criticalPairIdx τ, |(criticalVal p.1.1).im| ≤ H ∨ |(criticalVal p.1.2).im| ≤ H}
  have hE : (E ∪ {0, y}).Finite := (finite_exceptional_critical H Y).union (by simp)
  obtain ⟨a', b', hab', hsub⟩ :=
    exists_Ioo_subset_diff_finite (a := y - ε) (b := y + ε) (by linarith) hE
  obtain ⟨τ, hτ, p, hp1, hp2⟩ := exists_large_critical_pair hZ1 hL hfin H hab'
  have hτ' := hsub hτ
  have hτI : τ ∈ Ioo (y - ε) (y + ε) := hτ'.1
  have hτE : τ ∉ E ∪ {0, y} := hτ'.2
  have hτy : τ ≠ y := fun h => hτE (Or.inr (by simp [h]))
  have hτ0 : τ ≠ 0 := fun h => hτE (Or.inr (by simp [h]))
  have habs : |τ - y| < ε := abs_sub_lt_iff.mpr ⟨by linarith [hτI.2], by linarith [hτI.1]⟩
  have hτY : |τ| ≤ Y := by
    rw [hYdef]
    have := abs_sub_abs_le_abs_sub τ y
    linarith
  refine ⟨τ, hτy, habs, hH τ hτY ⟨p⟩ fun q => ?_⟩
  by_contra hq
  apply hτE
  refine Or.inl ⟨hτY, q, ?_⟩
  rcases not_and_or.mp hq with h | h
  · exact Or.inl (not_lt.mp h)
  · exact Or.inr (not_lt.mp h)

private theorem criticalC_natural_boundary_of_sector (hZ1 : Z1) (hZ2 : Z2) (hL : ZLittlewood)
    (hStir : StirlingStrip) (hfin : offLineZeros.Finite) :
    IsNaturalBoundary criticalC HH lineOne := by
  intro s hs
  have hre : s.re = 1 := hs
  have heq : s = 1 + (s.im : ℂ) * I := by
    apply Complex.ext <;> simp [hre]
  rw [heq]
  apply M5.noMeromorphicExtensionAt_of_line_blowup
    (differentiableOn_criticalC hZ1 hZ2)
  intro ε hε
  obtain ⟨τ, hne, hlt, hAtom⟩ := exists_tau_criticalAtom_ne_zero_of_sector hZ1 hZ2 hL hStir hfin s.im hε
  exact ⟨τ, hne, hlt, criticalAtom τ, hAtom, tendsto_eta_criticalC hZ1 hZ2 τ⟩

private theorem boundary_infinite_case_of_sector (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3)
    (hL : ZLittlewood) (hStir : StirlingStrip) (hinf : Phi2HInf.rightZeros.Infinite)
    (F : ℂ → ℂ) (hF : MeromorphicOn F HH)
    (hFT : F =ᶠ[codiscreteWithin (halfPlane 2)] T0) : IsNaturalBoundary F HH lineOne := by
  obtain ⟨E, hE⟩ := exists_cutoff hH
  obtain ⟨hm, heq⟩ := t0_hinf_continuation hH hZ1 hZ2 hZ3 hStir hE
  intro z hz
  have hzre : z.re = 1 := hz
  have hzeq : z = 1 + (z.im : ℂ) * I := by apply Complex.ext <;> simp [hzre]
  apply noMeromorphicExtensionAt_of_poles_in_every_ball (isOpen_halfPlane 1)
  intro ε hε
  obtain ⟨s, hs, hdist, hord⟩ :=
    exists_interior_pole_near_of_sector hH hZ1 hZ2 hZ3 hL hStir hE hinf z.im hε
  refine ⟨s, hs, ?_, ?_, ?_⟩
  · intro he
    have hre : 1 < s.re := hs
    rw [he, hzre] at hre
    exact lt_irrefl _ hre
  · simpa only [mem_ball, ← hzeq] using hdist
  · rw [meromorphicOrderAt_congr
      (eventuallyEq_nhdsNE_of_agree_halfPlane_two' hF hm heq hFT hs), hord]
    decide

private theorem boundary_finite_case_of_sector (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3)
    (hL : ZLittlewood) (hStir : StirlingStrip) (hfin : Phi2HInf.rightZeros.Finite)
    (F : ℂ → ℂ) (hF : MeromorphicOn F HH)
    (hFT : F =ᶠ[codiscreteWithin (halfPlane 2)] T0) : IsNaturalBoundary F HH lineOne := by
  obtain ⟨E, hE⟩ := exists_cutoff hH
  obtain ⟨hm, heq⟩ := t0_hinf_continuation hH hZ1 hZ2 hZ3 hStir hE
  let a : ℝ := max crossingAbscissa 0
  have ha : a < 1 := max_lt (cutoff_bounds hH).2.2.2.2 zero_lt_one
  have hW := meromorphicOn_W hH hZ1 hZ2 hZ3 hStir hE
  have hX := meromorphicOn_exceptionalC hZ1 hZ2 (Phi2HInf.finite_offLineZeros hZ1 hfin)
  let D : ℂ → ℂ := fun s => (W E s + exceptionalC s) / Gamma s
  have hD : MeromorphicOn D (halfPlane a) := by
    intro s hs
    have hc : s ∈ halfPlane crossingAbscissa := by
      change crossingAbscissa < s.re
      change a < s.re at hs
      exact (le_max_left _ _).trans_lt hs
    have h := ((hW s hc).add (hX s (mem_univ _))).mul
      (differentiable_one_div_Gamma.analyticAt s).meromorphicAt
    convert h using 1
    ext z
    simp [D, div_eq_mul_inv]
  have hagree : F =ᶠ[codiscreteWithin HH] fun s => D s + (1 / Gamma s) * criticalC s := by
    have h := eventuallyEq_codiscreteWithin_of_nhdsNE fun s hs =>
      eventuallyEq_nhdsNE_of_agree_halfPlane_two' hF hm heq hFT hs
    filter_upwards [h, Filter.self_mem_codiscreteWithin HH] with s hs hsH
    rw [hs, T0c, critical_decomposition hH hZ1 hZ2 hsH]
    dsimp [D]
    ring
  intro z hz
  apply (PhiRProof.FillC.noMeromorphicExtensionAt_iff_of_eq_add_mul'
    (isOpen_halfPlane a) (show z ∈ halfPlane a by
      change a < z.re
      have : z.re = 1 := hz
      linarith)
    hD
    (fun s _ => by simpa only [one_div] using differentiable_one_div_Gamma.analyticAt s)
    (fun s hs => one_div_ne_zero (Gamma_ne_zero_of_re_pos (by
      have : a < s.re := hs
      have : 0 ≤ a := le_max_right _ _
      linarith))) hagree).mpr
  exact criticalC_natural_boundary_of_sector hZ1 hZ2 hL hStir (Phi2HInf.finite_offLineZeros hZ1 hfin) z hz

/-- Exhaust the finite/infinite dichotomy, without RH or HypF. -/
private theorem t0_hinf_boundary_of_sector (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3)
    (hL : ZLittlewood) (hStir : StirlingStrip) (F : ℂ → ℂ) (hF : MeromorphicOn F HH)
    (hFT : F =ᶠ[codiscreteWithin (halfPlane 2)] T0) : IsNaturalBoundary F HH lineOne := by
  by_cases hfin : Phi2HInf.rightZeros.Finite
  · exact boundary_finite_case_of_sector hH hZ1 hZ2 hZ3 hL hStir hfin F hF hFT
  · exact boundary_infinite_case_of_sector hH hZ1 hZ2 hZ3 hL hStir hfin F hF hFT

/-- The T₀ continuation and natural boundary via the polynomial sector cone. -/
theorem t0_hinf_natural_boundary_of_sector (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3)
    (hL : ZLittlewood) (hStir : StirlingStrip) :
    (∃ F : ℂ → ℂ, MeromorphicOn F HH ∧ EqOn F T0 (halfPlane 2)) ∧
    (∀ F : ℂ → ℂ, MeromorphicOn F HH → F =ᶠ[codiscreteWithin (halfPlane 2)] T0 →
      IsNaturalBoundary F HH lineOne) := by
  obtain ⟨E, hE⟩ := exists_cutoff hH
  exact ⟨⟨T0c E, t0_hinf_continuation hH hZ1 hZ2 hZ3 hStir hE⟩,
    t0_hinf_boundary_of_sector hH hZ1 hZ2 hZ3 hL hStir⟩

#print axioms exists_interior_pole_near_of_sector
#print axioms exists_tau_criticalAtom_ne_zero_of_sector
#print axioms criticalC_natural_boundary_of_sector
#print axioms boundary_infinite_case_of_sector
#print axioms boundary_finite_case_of_sector
#print axioms t0_hinf_boundary_of_sector
#print axioms t0_hinf_natural_boundary_of_sector

end GoldbachBoundaries.T0HInf
