import GoldbachBoundaries.Paper2.M5.Fill.F2Common
import GoldbachBoundaries.Paper2.M5.Fill.«rectangleIntegral'_eq_sum_of_simplePoles_rect»

/-!
# Fill: `filter_rect`

The residue theorem for `gH` on the rectangle `[2/5, (1 + η)/2] × [-Y', Y']` of good height `Y'`, through
`rectangleIntegral'_eq_sum_of_simplePoles_rect` with `S = {1/2} ∪ {zeros with |γ| < Y'}`. Off `S` the closed rectangle
misses `Σ_Q` (`poleSetQ_re_cases`, and `GoodY` for the horizontal sides); `Qcont(s - z)` and `k_H(z, s)` are holomorphic
there (`Re(s - z) ∈ (1/2, 1)`). At each pole the principal part comes from M4b's `isBigO_mul_sub_residue`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- `Γ` is differentiable on `Re z > 0`. -/
lemma filterRect_differentiableAt_Gamma {z : ℂ} (hz : 0 < z.re) : DifferentiableAt ℂ Gamma z :=
  differentiableAt_Gamma _ fun m h => by
    have := congrArg Complex.re h
    simp at this
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith

/-- `z ↦ k_H(z, s) Q(s - z)` is differentiable at `z` when `Re z > 0` and `1/2 < Re(s - z) < 1` (RH). -/
lemma filterRect_differentiableAt_kHQ (hRH : RiemannHypothesis) (H : MvPolynomial (Fin 2) ℂ) {s z : ℂ}
    (hz : 0 < z.re) (h1 : 1 / 2 < (s - z).re) (h2 : (s - z).re < 1) :
    DifferentiableAt ℂ (fun z => kH H z s * Qcont (s - z)) z := by
  have hsz1 : s - z ≠ 1 := fun h => by rw [h, one_re] at h2; exact lt_irrefl _ h2
  have hG1 : DifferentiableAt ℂ Gamma z := filterRect_differentiableAt_Gamma hz
  have hG2 : DifferentiableAt ℂ (fun z => Gamma (s - z)) z :=
    (filterRect_differentiableAt_Gamma (by linarith)).comp z
      ((differentiableAt_const s).sub differentiableAt_id)
  have hE : DifferentiableAt ℂ (fun z => evalH H z (s - z)) z :=
    differentiable_evalH H differentiable_id ((differentiable_const s).sub differentiable_id) z
  have hQ : DifferentiableAt ℂ (fun z => Qcont (s - z)) z :=
    (TIdentity.analyticAt_Qcont_of_RH hRH h1 hsz1).differentiableAt.comp z
      ((differentiableAt_const s).sub differentiableAt_id)
  have : (fun z => kH H z s * Qcont (s - z)) =
      fun z => Gamma z * Gamma (s - z) / Gamma s * evalH H z (s - z) * Qcont (s - z) := by
    funext z; simp [kH, KerS]
  rw [this]
  exact (((hG1.mul hG2).div_const _).mul hE).mul hQ

/-- The open set where `z ↦ k_H(z, s) Q(s - z)` is holomorphic. -/
lemma filterRect_isOpen (s : ℂ) :
    IsOpen {z : ℂ | 0 < z.re ∧ 1 / 2 < (s - z).re ∧ (s - z).re < 1} := by
  have hc : Continuous fun z : ℂ => (s - z).re := continuous_re.comp (continuous_const.sub continuous_id)
  exact (isOpen_lt continuous_const continuous_re).inter
    ((isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const))

lemma filterRect_analyticAt_kHQ (hRH : RiemannHypothesis) (H : MvPolynomial (Fin 2) ℂ) {s z : ℂ}
    (hz : 0 < z.re) (h1 : 1 / 2 < (s - z).re) (h2 : (s - z).re < 1) :
    AnalyticAt ℂ (fun z => kH H z s * Qcont (s - z)) z := by
  refine DifferentiableOn.analyticAt (s := {z : ℂ | 0 < z.re ∧ 1 / 2 < (s - z).re ∧ (s - z).re < 1})
    (fun w hw => (filterRect_differentiableAt_kHQ hRH H hw.1 hw.2.1 hw.2.2).differentiableWithinAt)
    ((filterRect_isOpen s).mem_nhds ⟨hz, h1, h2⟩)

lemma filterRect_half_mem : (1 / 2 : ℂ) ∈ PoleSetQ :=
  Or.inl (Or.inr ⟨2, le_rfl, Nat.squarefree_two, by norm_num⟩)

lemma filterRect_zero_mem {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) : ρ ∈ PoleSetQ :=
  Or.inr ⟨1, le_rfl, squarefree_one, ρ, hρ, by simp⟩

/-- `filter_rect` of `FilterII.lean`, statement verbatim. -/
theorem filter_rect (hRH : RiemannHypothesis) (H : MvPolynomial (Fin 2) ℂ) {τ₀ η Y' : ℝ} (hη : 0 < η)
    (hη' : η ≤ 1 / 4) (hY' : 0 < Y') (hgood : GoodY Y') :
    {ρ : ℂ | ρ ∈ NontrivialZeros ∧ |ρ.im| < Y'}.Finite ∧
      RectangleIntegral' (gH H (1 + τ₀ * I + η)) (((2 / 5 : ℝ) : ℂ) - I * Y') ((((1 + η) / 2 : ℝ) : ℂ) + I * Y') =
        midTerm H (1 + τ₀ * I + η) +
          ∑ᶠ ρ ∈ {ρ : ℂ | ρ ∈ NontrivialZeros ∧ |ρ.im| < Y'}, resTerm H (1 + τ₀ * I + η) ρ := by
  classical
  set s : ℂ := 1 + τ₀ * I + η with hs
  set Z : Set ℂ := {ρ : ℂ | ρ ∈ NontrivialZeros ∧ |ρ.im| < Y'} with hZ
  have hZfin : Z.Finite := (finite_zeros_abs_im_le Y').subset fun ρ hρ => ⟨hρ.1, hρ.2.le⟩
  refine ⟨hZfin, ?_⟩
  have hsre : s.re = 1 + η := by simp [hs]
  have hre : ∀ ρ ∈ NontrivialZeros, ρ.re = 1 / 2 := fun ρ hρ => sigmaFinite_re_eq_half hRH hρ
  have hhalf : (1 / 2 : ℂ) ∉ hZfin.toFinset := by
    rw [Set.Finite.mem_toFinset]
    intro h
    exact riemannZeta_one_half_ne_zero h.1.1
  set S : Finset ℂ := insert (1 / 2) hZfin.toFinset with hSdef
  set A : ℂ → ℂ := fun p => if p = 1 / 2 then midTerm H s else resTerm H s p with hA
  -- every point of `S` has real part `1/2`
  have hSre : ∀ p ∈ S, p.re = 1 / 2 ∧ (p = 1 / 2 ∨ p ∈ Z) := by
    intro p hp
    rcases Finset.mem_insert.mp hp with h | h
    · subst h; norm_num
    · rw [Set.Finite.mem_toFinset] at h
      exact ⟨hre p h.1, Or.inr h⟩
  have hSmem : ∀ p ∈ S, p ∈ PoleSetQ := by
    intro p hp
    rcases (hSre p hp).2 with h | h
    · rw [h]; exact filterRect_half_mem
    · exact filterRect_zero_mem h.1
  -- the real part of `s - z` for `Re z = 1/2`
  have hsz : ∀ z : ℂ, (s - z).re = 1 + η - z.re := fun z => by rw [sub_re, hsre]
  -- the hypotheses of the rectangle residue theorem
  have hσ : (2 / 5 : ℝ) ≤ (1 + η) / 2 := by linarith
  have hS : ∀ p ∈ S, (2 / 5 : ℝ) < p.re ∧ p.re < (1 + η) / 2 ∧ |p.im| < Y' := by
    intro p hp
    obtain ⟨hpr, hp'⟩ := hSre p hp
    refine ⟨by rw [hpr]; norm_num, by rw [hpr]; linarith, ?_⟩
    rcases hp' with h | h
    · rw [h]; simpa using hY'
    · exact h.2
  have hf : DifferentiableOn ℂ (gH H s) (Icc (2 / 5 : ℝ) ((1 + η) / 2) ×ℂ Icc (-Y') Y' \ (S : Set ℂ)) := by
    rintro z ⟨hzR, hzS⟩
    rw [mem_reProdIm] at hzR
    obtain ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩ := hzR
    have hz0 : 0 < z.re := by linarith
    have hzP : z ∉ PoleSetQ := by
      intro hzP
      rcases poleSetQ_re_cases hRH hzP with h1 | ⟨-, h12 | hzero⟩ | hle
      · rw [h1, one_re] at hx2; linarith
      · exact hzS (by rw [h12]; exact Finset.mem_coe.mpr (Finset.mem_insert_self _ _))
      · by_cases hlt : |z.im| < Y'
        · exact hzS (Finset.mem_coe.mpr (Finset.mem_insert_of_mem
            ((Set.Finite.mem_toFinset hZfin).mpr ⟨hzero, hlt⟩)))
        · have habs : |z.im| = Y' := le_antisymm (abs_le.mpr ⟨hy1, hy2⟩) (not_lt.mp hlt)
          have hzre := hre z hzero
          have hg := hgood (1 / 2) ⟨by norm_num, by norm_num⟩
          rcases (abs_eq hY'.le).mp habs with him | him
          · apply hg.1
            have : z = ((1 / 2 : ℝ) : ℂ) + Y' * I := by
              apply Complex.ext <;> simp [hzre, him]
            rw [← this]; exact hzP
          · apply hg.2
            have : z = ((1 / 2 : ℝ) : ℂ) - Y' * I := by
              apply Complex.ext <;> simp [hzre, him]
            rw [← this]; exact hzP
      · linarith
    have h1 : 1 / 2 < (s - z).re := by rw [hsz]; linarith
    have h2 : (s - z).re < 1 := by rw [hsz]; linarith
    have hQ : DifferentiableAt ℂ Qcont z :=
      (M2.isQCont_Qcont.2.2 z ⟨hz0, hzP⟩).differentiableAt
    have := (filterRect_differentiableAt_kHQ hRH H hz0 h1 h2).fun_mul hQ
    have heq : (fun z => kH H z s * Qcont (s - z) * Qcont z) = gH H s := by
      funext w; simp only [gH]; ring
    rw [heq] at this
    exact this.differentiableWithinAt
  have hpole : ∀ p ∈ S, (gH H s - fun z => A p / (z - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
    intro p hp
    have hpr := (hSre p hp).1
    have hp0 : 0 < p.re := by rw [hpr]; norm_num
    have h1 : 1 / 2 < (s - p).re := by rw [hsz, hpr]; linarith
    have h2 : (s - p).re < 1 := by rw [hsz, hpr]; linarith
    have hmer : MeromorphicAt Qcont p := M2.isQCont_Qcont.1 p hp0
    have hB := M4b.isBigO_mul_sub_residue hmer (meromorphicOrderAt_Qcont_ge hp0)
      (hasResidue_Qcont_Rcoef (hSmem p hp)) (filterRect_analyticAt_kHQ hRH H hp0 h1 h2)
    have hAp : A p = kH H p s * Qcont (s - p) * Rcoef p := by
      simp only [hA]
      split_ifs with h
      · rw [h]; simp only [midTerm, kH]; ring
      · simp only [resTerm, kH]; ring
    convert hB using 1
    funext z
    simp only [Pi.sub_apply, gH, hAp]
    ring
  have hrect := rectangleIntegral'_eq_sum_of_simplePoles_rect (σ := 2 / 5) (σ' := (1 + η) / 2) (T := Y')
    (f := gH H s) S A hσ hY'.le hS hf hpole
  rw [hrect, hSdef, Finset.sum_insert hhalf, finsum_mem_eq_finite_toFinset_sum _ hZfin]
  congr 1
  · simp [hA]
  · refine Finset.sum_congr rfl fun p hp => ?_
    have : p ≠ 1 / 2 := fun h => hhalf (h ▸ hp)
    simp only [hA, this, ite_false]

end GoldbachBoundaries.Paper2.M5
