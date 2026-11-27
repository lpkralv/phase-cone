import GoldbachBoundaries.ResidueClass.Zeros
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.NumberTheory.LSeries.ZetaZeros

/-! # Finiteness of bounded windows and the Jensen reduction -/

noncomputable section

open Complex Filter Metric Set
open scoped Topology

namespace GoldbachBoundaries.ResidueClass

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

/-- Any compact set contains only finitely many zeros of the inducing L-function. -/
theorem finite_primitiveL_zeros_inter {K : Set ℂ} (hK : IsCompact K) :
    (K ∩ (primitiveL χ ⁻¹' {0})).Finite := by
  classical
  rcases eq_or_ne χ 1 with rfl | hχ
  · rw [primitiveL_one]
    exact hK.inter_riemannZetaZeros_finite
  · let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    have ha : AnalyticOnNhd ℂ (primitiveL χ) univ :=
      fun z _ ↦
        (DirichletCharacter.differentiable_LFunction (primitiveCharacter_ne_one χ hχ)).analyticAt z
    have hcd := ha.preimage_zero_mem_codiscrete (x := 2)
      (primitiveL_ne_zero_of_one_le_re χ (by norm_num))
    rw [Set.preimage_compl] at hcd
    have h := compl_mem_codiscrete_iff.mp hcd
    exact (hK.inter_right h.1).finite (h.2.mono inter_subset_right)

/-- Distinct strip zeros with ordinate in the closed interval `[a,b]`. -/
def zeroWindow (a b : ℝ) : Set ℂ := {ρ ∈ primitiveZeros χ | ρ.im ∈ Icc a b}

theorem finite_zeroWindow (a b : ℝ) : (zeroWindow χ a b).Finite := by
  have hK : IsCompact ((equivRealProdCLM : ℂ → ℝ × ℝ) ⁻¹' (Icc 0 1 ×ˢ Icc a b)) :=
    equivRealProdCLM.toHomeomorph.isCompact_preimage.mpr (isCompact_Icc.prod isCompact_Icc)
  refine (finite_primitiveL_zeros_inter χ hK).subset ?_
  intro ρ hρ
  exact ⟨⟨⟨hρ.1.2.1.le, hρ.1.2.2.le⟩, hρ.2⟩, hρ.1.1⟩

/-- There are finitely many distinct aggregate ordinates in any bounded interval. -/
theorem finite_Ordinates_inter (a b : ℝ) : (Ordinates q ∩ Icc a b).Finite := by
  classical
  refine (Set.finite_iUnion (fun χ : DirichletCharacter ℂ q ↦
    (finite_zeroWindow χ a b).image Complex.im)).subset ?_
  intro t ht
  obtain ⟨χ, hχ⟩ := mem_Ordinates_iff.mp ht.1
  exact mem_iUnion.mpr ⟨χ, criticalPoint t, ⟨hχ, by simpa [criticalPoint_im] using ht.2⟩,
    criticalPoint_im t⟩

/-- A critical-line point within half a unit of ordinate `V` lies in the smaller Jensen disk. -/
theorem criticalPoint_mem_jensen_disk {t V : ℝ} (h : |t - V| ≤ 1 / 2) :
    criticalPoint t ∈ closedBall (2 + (V : ℂ) * I) (8 / 5) := by
  rw [mem_closedBall, dist_eq_norm, Complex.norm_def, Real.sqrt_le_iff]
  constructor
  · norm_num
  · rw [normSq_apply]
    have hre : (criticalPoint t - (2 + (V : ℂ) * I)).re = -(3 / 2 : ℝ) := by
      norm_num [sub_re, add_re, criticalPoint_re]
    have him : (criticalPoint t - (2 + (V : ℂ) * I)).im = t - V := by
      simp [sub_im, add_im, criticalPoint_im]
    rw [hre, him]
    obtain ⟨hl, hu⟩ := abs_le.mp h
    nlinarith [mul_nonneg (sub_nonneg.mpr hu) (show 0 ≤ 1 / 2 + (t - V) by linarith)]

open scoped Classical in
/-- The entire function used in Jensen's inequality. For the principal
character its pole at one is removed using Mathlib's regularization. -/
def jensenFunction : ℂ → ℂ :=
  if χ = 1 then DirichletCharacter.LFunctionTrivChar₁ 1 else primitiveL χ

theorem differentiable_jensenFunction : Differentiable ℂ (jensenFunction χ) := by
  classical
  unfold jensenFunction
  split_ifs with hχ
  · exact DirichletCharacter.differentiable_LFunctionTrivChar₁ 1
  · let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    exact DirichletCharacter.differentiable_LFunction (primitiveCharacter_ne_one χ hχ)

theorem analyticOrderAt_jensenFunction {z : ℂ} (hz : z ≠ 1) :
    analyticOrderAt (jensenFunction χ) z = analyticOrderAt (primitiveL χ) z := by
  classical
  by_cases hχ : χ = 1
  · subst χ
    simp only [jensenFunction, ite_true, primitiveL_one]
    have heq : DirichletCharacter.LFunctionTrivChar₁ 1 =ᶠ[𝓝 z]
        fun w ↦ (w - 1) * riemannZeta w := by
      filter_upwards [isOpen_ne.mem_nhds hz] with w hw
      rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hw,
        DirichletCharacter.LFunctionTrivChar, DirichletCharacter.LFunction_modOne_eq]
    have hsub : AnalyticAt ℂ (fun w : ℂ ↦ w - 1) z := by fun_prop
    rw [analyticOrderAt_congr heq, ← Pi.mul_def,
      analyticOrderAt_mul hsub (analyticOn_riemannZeta z hz),
      hsub.analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr hz), zero_add]
  · simp [jensenFunction, hχ]

theorem jensenFunction_ne_zero_of_one_lt_re {z : ℂ} (hz : 1 < z.re) :
    jensenFunction χ z ≠ 0 := by
  have hz₁ : z ≠ 1 := by
    intro h
    simp [h] at hz
  have horder : analyticOrderAt (primitiveL χ) z = 0 :=
    (analyticOnNhd_primitiveL χ z hz₁).analyticOrderAt_eq_zero.mpr
      (primitiveL_ne_zero_of_one_le_re χ hz.le)
  exact ((differentiable_jensenFunction χ).analyticAt z).analyticOrderAt_eq_zero.mp
    ((analyticOrderAt_jensenFunction χ hz₁).trans horder)

/-- A bounded window restricted to critical-line zeros. -/
def criticalWindow (a b : ℝ) : Set ℂ :=
  zeroWindow χ a b ∩ {ρ | ρ.re = 1 / 2}

theorem criticalWindow_eq_zeroWindow {a b : ℝ}
    (h : ∀ ρ ∈ zeroWindow χ a b, ρ.re = 1 / 2) :
    criticalWindow χ a b = zeroWindow χ a b :=
  inter_eq_left.mpr h

/-- Jensen bounds the multiplicity in a window of length one in terms of a
bound on the outer circle and the value at the centre. -/
theorem critical_window_mass_le_jensen (V M : ℝ) (hM : 1 ≤ M)
    (hbound : ∀ z ∈ sphere (2 + (V : ℂ) * I) (7 / 4), ‖jensenFunction χ z‖ ≤ M) :
    (∑ᶠ ρ ∈ criticalWindow χ (V - 1 / 2) (V + 1 / 2), (primitiveMult χ ρ : ℝ)) ≤
      Real.log (M / ‖jensenFunction χ (2 + (V : ℂ) * I)‖) / Real.log (35 / 32) := by
  classical
  let c : ℂ := 2 + (V : ℂ) * I
  let disk := closedBall c (8 / 5)
  let divs := MeromorphicOn.divisor (jensenFunction χ) disk
  have ha : ∀ S : Set ℂ, AnalyticOnNhd ℂ (jensenFunction χ) S :=
    fun _ z _ ↦ (differentiable_jensenFunction χ).analyticAt z
  have hcentre : jensenFunction χ c ≠ 0 :=
    jensenFunction_ne_zero_of_one_lt_re χ (by norm_num [c, add_re])
  have hJ := (ha (closedBall c |(7 / 4 : ℝ)|)).sum_divisor_le
    (r := (8 / 5 : ℝ)) (R := (7 / 4 : ℝ)) (by norm_num) (by norm_num) hM hcentre
    (by simpa [c, abs_of_pos (by norm_num : (0 : ℝ) < 7 / 4)] using hbound)
  have hJ' : (∑ᶠ z, divs z) ≤ Real.log (M / ‖jensenFunction χ c‖) / Real.log (35 / 32) := by
    rw [abs_of_nonneg (by norm_num : 0 ≤ (8 / 5 : ℝ)),
      show (7 / 4 : ℝ) / (8 / 5) = 35 / 32 by norm_num] at hJ
    exact hJ
  have hfin := divs.finiteSupport (isCompact_closedBall c (8 / 5))
  have hcast : (↑(∑ᶠ z, divs z) : ℝ) = ∑ᶠ z, (divs z : ℝ) :=
    map_finsum (Int.castRingHom ℝ) hfin
  rw [hcast] at hJ'
  refine le_trans ?_ hJ'
  rw [finsum_mem_def]
  refine finsum_le_finsum ?_ (hfin.subset fun z hz ↦ ?_) fun z ↦ ?_
  · exact ((finite_zeroWindow χ (V - 1 / 2) (V + 1 / 2)).subset
      (inter_subset_left : criticalWindow χ _ _ ⊆ _)).subset (by
      intro z hz
      by_contra hn
      exact hz (Set.indicator_of_notMem hn _))
  · intro hz'
    apply hz
    simp [hz']
  · by_cases hz : z ∈ criticalWindow χ (V - 1 / 2) (V + 1 / 2)
    · rw [Set.indicator_of_mem hz]
      have hz₁ : z ≠ 1 := by
        intro h
        have hlt := hz.1.1.2.2
        simp [h] at hlt
      have hz' : criticalPoint z.im = z :=
        Complex.ext (by rw [criticalPoint_re, show z.re = 1 / 2 from hz.2]) (criticalPoint_im _)
      have hzd : z ∈ disk := by
        rw [← hz']
        exact criticalPoint_mem_jensen_disk (abs_le.mpr ⟨by linarith [hz.1.2.1], by linarith [hz.1.2.2]⟩)
      have hd : divs z = (primitiveMult χ z : ℤ) := by
        dsimp [divs]
        rw [MeromorphicOn.AnalyticOnNhd.divisor_apply (ha disk) hzd, analyticOrderAt_jensenFunction χ hz₁,
          ← Nat.cast_analyticOrderNatAt (analyticOrderAt_primitiveL_ne_top χ hz₁)]
        rfl
      simp [hd]
    · rw [Set.indicator_of_notMem hz]
      have hz_nonneg : (0 : ℤ) ≤ divs z :=
        MeromorphicOn.AnalyticOnNhd.divisor_nonneg (ha disk) z
      have hreal : (↑(0 : ℤ) : ℝ) ≤ (divs z : ℝ) := by exact_mod_cast hz_nonneg
      simpa only [Int.cast_zero] using hreal

theorem primitive_window_mass_le_jensen (hGRH : GRH q) (V M : ℝ) (hM : 1 ≤ M)
    (hbound : ∀ z ∈ sphere (2 + (V : ℂ) * I) (7 / 4), ‖jensenFunction χ z‖ ≤ M) :
    (∑ᶠ ρ ∈ zeroWindow χ (V - 1 / 2) (V + 1 / 2), (primitiveMult χ ρ : ℝ)) ≤
      Real.log (M / ‖jensenFunction χ (2 + (V : ℂ) * I)‖) / Real.log (35 / 32) := by
  rw [← criticalWindow_eq_zeroWindow χ (fun ρ hρ ↦ hGRH χ ρ hρ.1)]
  exact critical_window_mass_le_jensen χ V M hM hbound

end GoldbachBoundaries.ResidueClass
