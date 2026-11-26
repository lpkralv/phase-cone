import GoldbachBoundaries.Paper2.M5.FilterIII
import GoldbachBoundaries.Paper2.M5.Fill.F3Common

/-!
# Fill, group F3: `Lambda0_eq_limit`

`midLim H₀ 0 = R_{1/2} K_1(1/2) H₀(1/2, 1/2) R_{1/2} = (-1/2)·π·(1/4)·(-1/2) = π/16` (`Rcoef_inv`, `Γ(1/2)² = π` through
`Gamma_mul_Gamma_one_sub`). For a zero `ρ` (RH) `1 - ρ = ρ̄` is a zero with `m(ρ̄) = m(ρ)` ((Z1)), `R_ρ = -m(ρ)`, so
`limTerm H₀ 0 ρ = m(ρ)²|Γ(ρ)|²|ρ - 1|²` (real). The zeros split by the sign of `γ ≠ 0`; the upper half is the index type
of `lambda0Term` (inclusion) and the lower half is its image under conjugation, which preserves the term. So
`∑_Z = 2 ∑_{γ > 0}`, and summability of `lambda0Term` is the restriction of `hsum`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- `midLim H₀ 0 = π/16`. -/
lemma F3_midLim_H0f : midLim H0f 0 = (Real.pi / 16 : ℝ) := by
  have hR : Rcoef (1 / 2) = -1 / 2 := by
    have h := Rcoef_inv (k := 2) (le_refl 2) Nat.squarefree_two
    rw [mu, ArithmeticFunction.moebius_apply_prime Nat.prime_two] at h
    simpa using h
  have hK : KerS 1 (1 / 2) = Real.pi := by
    have h := Complex.Gamma_mul_Gamma_one_sub (1 / 2)
    have hs : Complex.sin (↑Real.pi * (1 / 2)) = 1 := by
      rw [show (↑Real.pi * (1 / 2) : ℂ) = ↑Real.pi / 2 by ring, Complex.sin_pi_div_two]
    rw [hs, div_one] at h
    unfold KerS
    rw [Complex.Gamma_one, div_one]
    exact h
  simp only [midLim, ite_true, hR, hK]
  simp [evalH, H0f]
  ring

theorem Lambda0_eq_limit (hRH : RiemannHypothesis) (hZ1 : Z1)
    (hsum : Summable (fun ρ : NontrivialZeros => limTerm H0f 0 ρ)) :
    Summable lambda0Term ∧ midLim H0f 0 + ∑' ρ : NontrivialZeros, limTerm H0f 0 ρ = (Lambda0 : ℂ) := by
  set f : NontrivialZeros → ℝ := fun ρ =>
    (zetaMult (ρ : ℂ) : ℝ) ^ 2 * ‖Gamma (ρ : ℂ)‖ ^ 2 * ‖(ρ : ℂ) - 1‖ ^ 2 with hf
  -- `1 - ρ = ρ̄` under RH
  have hconj : ∀ ρ : NontrivialZeros, (1 + ((0 : ℝ) : ℂ) * I - ρ : ℂ) = conj (ρ : ℂ) := by
    intro ρ
    have hre := F3_re_zero hRH ρ.2
    apply Complex.ext <;> norm_num [hre]
  have hterm : ∀ ρ : NontrivialZeros, limTerm H0f 0 ρ = (f ρ : ℂ) := by
    intro ρ
    have hρ := ρ.2
    have hcz : conj (ρ : ℂ) ∈ NontrivialZeros := conj_mem_nontrivialZeros hρ
    have hm : zetaMult (conj (ρ : ℂ)) = zetaMult (ρ : ℂ) := (hZ1 _ hρ).1.2
    unfold limTerm
    rw [hconj ρ]
    simp only [hcz, ite_true]
    unfold KerS
    have hc1 : (1 : ℂ) - ρ = conj (ρ : ℂ) := by simpa using hconj ρ
    rw [show (1 + ((0 : ℝ) : ℂ) * I : ℂ) = 1 by simp, hc1, Complex.Gamma_one, div_one,
      F3_Rcoef_zero hRH hρ, F3_Rcoef_zero hRH hcz, hm, Complex.Gamma_conj]
    have hev : evalH H0f (ρ : ℂ) (conj (ρ : ℂ)) = ((ρ : ℂ) - 1) * conj ((ρ : ℂ) - 1) := by
      simp [evalH, H0f]
    rw [hev, hf]
    have h1 : Gamma (ρ : ℂ) * conj (Gamma (ρ : ℂ)) = ((‖Gamma (ρ : ℂ)‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have h2 : ((ρ : ℂ) - 1) * conj ((ρ : ℂ) - 1) = ((‖(ρ : ℂ) - 1‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    calc -(zetaMult (ρ : ℂ) : ℂ) * (Gamma (ρ : ℂ) * conj (Gamma (ρ : ℂ))) *
          (((ρ : ℂ) - 1) * conj ((ρ : ℂ) - 1)) * -(zetaMult (ρ : ℂ) : ℂ)
        = (zetaMult (ρ : ℂ) : ℂ) ^ 2 * (Gamma (ρ : ℂ) * conj (Gamma (ρ : ℂ))) *
          (((ρ : ℂ) - 1) * conj ((ρ : ℂ) - 1)) := by ring
      _ = _ := by rw [h1, h2]; push_cast; ring
  have hfs : Summable f := by
    have : Summable (fun ρ : NontrivialZeros => (f ρ : ℂ)) := by
      simpa only [hterm] using hsum
    exact Complex.summable_ofReal.mp this
  -- the two halves
  set ι₁ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ 0 < ρ.im} → NontrivialZeros := fun ρ => ⟨ρ.1, ρ.2.1⟩ with hι₁
  set ι₂ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ 0 < ρ.im} → NontrivialZeros :=
    fun ρ => ⟨conj ρ.1, conj_mem_nontrivialZeros ρ.2.1⟩ with hι₂
  have hinj₁ : Function.Injective ι₁ := by
    intro a b h
    apply Subtype.ext
    simpa [hι₁] using congrArg Subtype.val h
  have hinj₂ : Function.Injective ι₂ := by
    intro a b h
    apply Subtype.ext
    have := congrArg (starRingEnd ℂ) (congrArg Subtype.val h)
    simpa [hι₂] using this
  have hf₁ : ∀ p, f (ι₁ p) = lambda0Term p := fun p => rfl
  have hf₂ : ∀ p, f (ι₂ p) = lambda0Term p := by
    intro p
    have hm : zetaMult (conj (p : ℂ)) = zetaMult (p : ℂ) := (hZ1 _ p.2.1).1.2
    simp only [hf, hι₂, lambda0Term, hm, Complex.Gamma_conj, Complex.norm_conj]
    rw [show conj (p : ℂ) - 1 = conj ((p : ℂ) - 1) by simp, Complex.norm_conj]
  have hL : Summable lambda0Term := by
    have := hfs.comp_injective hinj₁
    exact this.congr hf₁
  set A : Set NontrivialZeros := {ρ | 0 < (ρ : ℂ).im} with hA
  have hsplit : ∑' ρ, f ρ = ∑' ρ, A.indicator f ρ + ∑' ρ, Aᶜ.indicator f ρ := by
    rw [← (hfs.indicator A).tsum_add (hfs.indicator Aᶜ)]
    congr 1
    funext ρ
    exact (Set.indicator_self_add_compl_apply A f ρ).symm
  have hup : ∑' ρ, A.indicator f ρ = ∑' p, lambda0Term p := by
    rw [← hinj₁.tsum_eq]
    · refine tsum_congr fun p => ?_
      rw [Set.indicator_of_mem (show ι₁ p ∈ A from p.2.2), hf₁]
    · intro ρ hρ
      by_cases h : ρ ∈ A
      · exact ⟨⟨ρ.1, ρ.2, h⟩, rfl⟩
      · exact absurd (Set.indicator_of_notMem h f) hρ
  have hdown : ∑' ρ, Aᶜ.indicator f ρ = ∑' p, lambda0Term p := by
    rw [← hinj₂.tsum_eq]
    · refine tsum_congr fun p => ?_
      have hnot : ι₂ p ∈ Aᶜ := by
        show ¬ (0 < (conj (p : ℂ)).im)
        simp only [conj_im, neg_pos, not_lt]
        exact p.2.2.le
      rw [Set.indicator_of_mem hnot, hf₂]
    · intro ρ hρ
      by_cases h : ρ ∈ Aᶜ
      · have hne : (ρ : ℂ).im ≠ 0 := im_ne_zero_of_mem_nontrivialZeros ρ.2
        have hneg : (ρ : ℂ).im < 0 := lt_of_le_of_ne (not_lt.mp h) hne
        refine ⟨⟨conj (ρ : ℂ), conj_mem_nontrivialZeros ρ.2, by simpa using hneg⟩, ?_⟩
        apply Subtype.ext
        simp [hι₂]
      · exact absurd (Set.indicator_of_notMem h f) hρ
  refine ⟨hL, ?_⟩
  rw [F3_midLim_H0f, tsum_congr hterm, ← Complex.ofReal_tsum, hsplit, hup, hdown, Lambda0]
  push_cast
  ring

end GoldbachBoundaries.Paper2.M5
