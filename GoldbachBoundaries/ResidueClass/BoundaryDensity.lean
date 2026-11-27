import GoldbachBoundaries.ResidueClass.WeightedCone
import GoldbachBoundaries.Phi2.Proof.M5Boundary

/-! # Density of nonzero binary residues from zeta ordinates -/

noncomputable section

open Complex ComplexConjugate Set

namespace GoldbachBoundaries.ResidueClass

variable {q : ℕ} [NeZero q]

private theorem exists_represented_in_Ioo {T : ℝ}
    (hline : ∀ ρ ∈ NontrivialZeros, T ≤ |ρ.im| → ρ.re = 1 / 2)
    (hGap : Paper2.ZLittlewood)
    {a b : ℝ} (hab : a < b) : ∃ τ ∈ Ioo a b, Nonempty (pairFibre q τ) := by
  obtain ⟨Y, hY⟩ := Paper2.M5.exists_ordinate_in_interval hGap (sub_pos.mpr hab)
  obtain ⟨ρ, hρ, hYρ⟩ := exists_nontrivialZero_im_gt (max (Y - a) (max T (T - a)))
  obtain ⟨ρ', hρ', hLo, hHi⟩ := hY (ρ.im + a) (by linarith [le_max_left (Y - a) (max T (T - a))])
  have hC := mem_Ordinates_of_zetaZero (q := q) (conj_mem_nontrivialZeros hρ)
    (hline _ (conj_mem_nontrivialZeros hρ) (by
      simp only [conj_im, abs_neg]
      linarith [le_abs_self ρ.im, (le_max_left T (T - a)).trans (le_max_right (Y - a) _)]))
  have hC' := mem_Ordinates_of_zetaZero (q := q) hρ' (hline _ hρ' (by
    linarith [le_abs_self ρ'.im, (le_max_right T (T - a)).trans (le_max_right (Y - a) _)]))
  refine ⟨ρ'.im - ρ.im, ⟨by linarith, by linarith⟩,
    ⟨⟨(⟨ρ'.im, hC'⟩, ⟨-ρ.im, by simpa using hC⟩), ?_⟩⟩⟩
  change ρ'.im + -ρ.im = ρ'.im - ρ.im
  ring

private theorem finite_low_sums (Y U : ℝ) (hY : 0 ≤ Y) :
    {τ : ℝ | |τ| ≤ Y ∧ ∃ p : pairFibre q τ,
      |(p.1.1 : ℝ)| ≤ U ∨ |(p.1.2 : ℝ)| ≤ U}.Finite := by
  let W := Ordinates q ∩ Icc (-(U + Y)) (U + Y)
  have hW : W.Finite := finite_Ordinates_inter _ _
  refine ((hW.prod hW).image (fun p : ℝ × ℝ ↦ p.1 + p.2)).subset ?_
  rintro τ ⟨hτ, p, hp⟩
  have hs : (p.1.1 : ℝ) + p.1.2 = τ := p.2
  have hbounds : |(p.1.1 : ℝ)| ≤ U + Y ∧ |(p.1.2 : ℝ)| ≤ U + Y := by
    rcases hp with hp | hp
    · refine ⟨by linarith, ?_⟩
      have h : |τ - (p.1.1 : ℝ)| ≤ |τ| + |(p.1.1 : ℝ)| := by
        simpa [sub_eq_add_neg] using abs_add_le τ (-(p.1.1 : ℝ))
      have he : τ - (p.1.1 : ℝ) = p.1.2 := by linarith
      rw [he] at h
      linarith
    · refine ⟨?_, by linarith⟩
      have h : |τ - (p.1.2 : ℝ)| ≤ |τ| + |(p.1.2 : ℝ)| := by
        simpa [sub_eq_add_neg] using abs_add_le τ (-(p.1.2 : ℝ))
      have he : τ - (p.1.2 : ℝ) = p.1.1 := by linarith
      rw [he] at h
      linarith
  exact ⟨((p.1.1 : ℝ), (p.1.2 : ℝ)),
    ⟨⟨p.1.1.prop, abs_le.mp hbounds.1⟩, ⟨p.1.2.prop, abs_le.mp hbounds.2⟩⟩, hs⟩

/-- Nonzero summed residues occur arbitrarily close to each ordinate and
can be chosen outside any prescribed finite subset of the line. -/
theorem exists_nearby_pairResidue_ne_zero_of_high_critical {T : ℝ}
    (hline : ∀ ρ ∈ NontrivialZeros, T ≤ |ρ.im| → ρ.re = 1 / 2) (hGap : Paper2.ZLittlewood)
    (hStir : Phi2HInf.StirlingStrip) (y : ℝ) {ε : ℝ} (hε : 0 < ε)
    {E : Set ℝ} (hE : E.Finite) :
    ∃ τ : ℝ, τ ≠ y ∧ |τ - y| < ε ∧ τ ∉ E ∧ pairResidue q τ ≠ 0 := by
  let Y := |y| + ε
  have hY : 0 < Y := by positivity
  obtain ⟨U, hU, hCone⟩ := exists_pairResidue_ne_zero_unconditional (q := q) hStir hY
  let low := {τ : ℝ | |τ| ≤ Y ∧ ∃ p : pairFibre q τ,
    |(p.1.1 : ℝ)| ≤ U ∨ |(p.1.2 : ℝ)| ≤ U}
  have hl : low.Finite := finite_low_sums Y U hY.le
  have hfin : (low ∪ (E ∪ {y})).Finite := hl.union (hE.union (finite_singleton _))
  obtain ⟨a, b, hab, hAB⟩ := Phi2Proof.exists_Ioo_subset_diff_finite
    (a := y - ε) (b := y + ε) (by linarith) hfin
  obtain ⟨τ, hτ, hp⟩ := exists_represented_in_Ioo (q := q) hline hGap hab
  have hm := hAB hτ
  have hn : τ ∉ low ∪ (E ∪ {y}) := hm.2
  have hnear : |τ - y| < ε := abs_lt.mpr ⟨by linarith [hm.1.1], by linarith [hm.1.2]⟩
  have htY : |τ| ≤ Y := by
    have h := abs_sub_abs_le_abs_sub τ y
    dsimp [Y]
    linarith
  refine ⟨τ, fun he ↦ hn (.inr (.inr he)), hnear, fun he ↦ hn (.inr (.inl he)),
    hCone τ htY hp fun p ↦ ?_⟩
  exact not_or.mp (fun h ↦ hn (.inl ⟨htY, p, h⟩)) |>.imp lt_of_not_ge lt_of_not_ge

theorem exists_nearby_pairResidue_ne_zero (hGRH : GRH q) (hGap : Paper2.ZLittlewood)
    (hStir : Phi2HInf.StirlingStrip) (y : ℝ) {ε : ℝ} (hε : 0 < ε)
    {E : Set ℝ} (hE : E.Finite) :
    ∃ τ : ℝ, τ ≠ y ∧ |τ - y| < ε ∧ τ ∉ E ∧ pairResidue q τ ≠ 0 :=
  exists_nearby_pairResidue_ne_zero_of_high_critical (T := 0) (fun ρ hρ _ ↦ hGRH 1 ρ ((primitiveZeros_one (q := q)).symm ▸ hρ))
    hGap hStir y hε hE

end GoldbachBoundaries.ResidueClass
