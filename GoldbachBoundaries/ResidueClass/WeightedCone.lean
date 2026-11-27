import GoldbachBoundaries.ResidueClass.RadialLimit
import GoldbachBoundaries.Phi2HInf.Fill.sum_bKer_ne_zero_hinf

/-! # Noncancellation of the large critical pairs -/

noncomputable section

open Complex Set Filter

namespace GoldbachBoundaries.ResidueClass

variable {q : ℕ} [NeZero q] {τ : ℝ}

private def negativeHeight (p : pairFibre q τ) : ℝ :=
  -(min (p.1.1 : ℝ) (p.1.2 : ℝ))

private def pairMultiplicity (p : pairFibre q τ) : ℕ :=
  ordinateWeight q p.1.1 * ordinateWeight q p.1.2

private theorem fibre_sum (p : pairFibre q τ) :
    (p.1.1 : ℝ) + (p.1.2 : ℝ) = τ := p.2

private theorem left_injective : Function.Injective
    (fun p : pairFibre q τ ↦ (p.1.1 : ℝ)) := by
  intro a b h
  apply Subtype.ext
  exact Prod.ext (Subtype.ext h) (Subtype.ext (by linarith [fibre_sum a, fibre_sum b]))

private theorem right_injective : Function.Injective
    (fun p : pairFibre q τ ↦ (p.1.2 : ℝ)) := by
  intro a b h
  apply Subtype.ext
  exact Prod.ext (Subtype.ext (by linarith [fibre_sum a, fibre_sum b])) (Subtype.ext h)

private theorem window_weight_le {C : ℝ}
    (hMass : ∀ V : ℝ,
      (∑ᶠ t ∈ Ordinates q ∩ Icc (V - 1 / 2) (V + 1 / 2), (ordinateWeight q t : ℝ)) ≤
        C * Real.log (|V| + 4))
    (t : Ordinates q) :
    (ordinateWeight q t : ℝ) ≤ C * Real.log (|(t : ℝ)| + 4) := by
  classical
  let S := Ordinates q ∩ Icc ((t : ℝ) - 1 / 2) ((t : ℝ) + 1 / 2)
  let hS := finite_Ordinates_inter (q := q) ((t : ℝ) - 1 / 2) ((t : ℝ) + 1 / 2)
  have ht : (t : ℝ) ∈ S := ⟨t.prop, by constructor <;> linarith⟩
  have hm := hMass (t : ℝ)
  rw [finsum_mem_eq_finite_toFinset_sum _ hS] at hm
  exact (Finset.single_le_sum (f := fun t ↦ (ordinateWeight q t : ℝ))
    (fun _ _ ↦ Nat.cast_nonneg _) (hS.mem_toFinset.mpr ht)).trans hm

/-- Both orderings together contribute at most a constant times the squared
logarithm to any unit bin. -/
private theorem pair_bin_bound {Y : ℝ} (hY : 0 < Y) :
    ∃ K : ℝ, ∀ τ : ℝ, |τ| ≤ Y → ∀ v : ℝ, 0 ≤ v →
      (∑ᶠ p ∈ {p : pairFibre q τ | negativeHeight p ∈ Ico v (v + 1)},
        (pairMultiplicity p : ℝ)) ≤ K * Real.log (v + Y + 4) ^ 2 := by
  classical
  obtain ⟨C, hC, hMass⟩ := exists_ordinate_window_mass_bound_unconditional q
  refine ⟨8 * C ^ 2, fun τ hτ v hv ↦ ?_⟩
  let L := Real.log (v + Y + 4)
  have hL : 0 ≤ L := Real.log_nonneg (by linarith)
  let S := {p : pairFibre q τ | negativeHeight p ∈ Ico v (v + 1)}
  let T := Ordinates q ∩ Icc (-v - 1) (-v)
  have hT : T.Finite := finite_Ordinates_inter _ _
  have hTmass : (∑ᶠ t ∈ T, (ordinateWeight q t : ℝ)) ≤ 2 * C * L := by
    have h := hMass (-v - 1 / 2)
    rw [show -v - 1 / 2 - 1 / 2 = -v - 1 by ring,
      show -v - 1 / 2 + 1 / 2 = -v by ring,
      abs_of_nonpos (by linarith : -v - 1 / 2 ≤ 0)] at h
    refine h.trans ?_
    have hb : -(-v - 1 / 2) + 4 ≤ (v + Y + 4) ^ 2 := by nlinarith
    have he := Real.log_le_log (show 0 < -(-v - 1 / 2) + 4 by linarith) hb
    rw [Real.log_pow] at he
    calc
      _ ≤ C * (2 * L) := mul_le_mul_of_nonneg_left (by simpa [L] using he) hC
      _ = _ := by ring
  have hOriented (U : Set (pairFibre q τ)) (g : pairFibre q τ → ℝ)
      (hg : Function.Injective g) (hsub : g '' U ⊆ T)
      (hweight : ∀ p ∈ U, (pairMultiplicity p : ℝ) ≤ (2 * C * L) * (ordinateWeight q (g p) : ℝ)) :
      U.Finite ∧ (∑ᶠ p ∈ U, (pairMultiplicity p : ℝ)) ≤ 4 * C^2 * L^2 := by
    have hImg := hT.subset hsub
    have hU : U.Finite := Set.Finite.of_finite_image hImg hg.injOn
    refine ⟨hU, ?_⟩
    have hsum : (∑ᶠ p ∈ U, (ordinateWeight q (g p) : ℝ)) ≤ 2 * C * L := by
      rw [← finsum_mem_image (f := fun t ↦ (ordinateWeight q t : ℝ)) hg.injOn]
      refine le_trans ?_ hTmass
      rw [finsum_mem_eq_finite_toFinset_sum _ hImg, finsum_mem_eq_finite_toFinset_sum _ hT]
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (fun t ht ↦ hT.mem_toFinset.mpr (hsub (hImg.mem_toFinset.mp ht)))
        (fun _ _ _ ↦ Nat.cast_nonneg _)
    calc
      _ ≤ ∑ᶠ p ∈ U, (2 * C * L) * (ordinateWeight q (g p) : ℝ) := by
        rw [finsum_mem_eq_finite_toFinset_sum _ hU, finsum_mem_eq_finite_toFinset_sum _ hU]
        exact Finset.sum_le_sum fun p hp ↦ hweight p (hU.mem_toFinset.mp hp)
      _ = (2 * C * L) * ∑ᶠ p ∈ U, (ordinateWeight q (g p) : ℝ) := by
        rw [finsum_mem_eq_finite_toFinset_sum _ hU, finsum_mem_eq_finite_toFinset_sum _ hU,
          Finset.mul_sum]
      _ ≤ (2 * C * L) * (2 * C * L) := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = _ := by ring
  have hother (a b : Ordinates q) (hab : (a : ℝ) + b = τ) (ha : (a : ℝ) ∈ Icc (-v - 1) (-v)) :
      (ordinateWeight q b : ℝ) ≤ 2 * C * L := by
    have hb : |(b : ℝ)| ≤ v + Y + 1 := by
      rw [abs_le] at hτ ⊢
      constructor <;> linarith [ha.1, ha.2]
    have hb' : |(b : ℝ)| + 4 ≤ (v + Y + 4) ^ 2 := by nlinarith
    have hh := Real.log_le_log (show 0 < |(b : ℝ)| + 4 by positivity) hb'
    rw [Real.log_pow] at hh
    calc
      _ ≤ C * Real.log (|(b : ℝ)| + 4) := window_weight_le hMass b
      _ ≤ C * (2 * L) := mul_le_mul_of_nonneg_left (by simpa [L] using hh) hC
      _ = _ := by ring
  let S₁ := S ∩ {p | (p.1.1 : ℝ) ≤ p.1.2}
  let S₂ := S ∩ {p | (p.1.2 : ℝ) < p.1.1}
  have hmem₁ (p : pairFibre q τ) (hp : p ∈ S₁) : (p.1.1 : ℝ) ∈ T := by
    have hp' : negativeHeight p ∈ Ico v (v + 1) := hp.1
    have he : min (p.1.1 : ℝ) (p.1.2 : ℝ) = p.1.1 := min_eq_left hp.2
    rw [negativeHeight, he] at hp'
    exact ⟨p.1.1.prop, by constructor <;> linarith [hp'.1, hp'.2]⟩
  have hmem₂ (p : pairFibre q τ) (hp : p ∈ S₂) : (p.1.2 : ℝ) ∈ T := by
    have hp' : negativeHeight p ∈ Ico v (v + 1) := hp.1
    have he : min (p.1.1 : ℝ) (p.1.2 : ℝ) = p.1.2 := min_eq_right hp.2.le
    rw [negativeHeight, he] at hp'
    exact ⟨p.1.2.prop, by constructor <;> linarith [hp'.1, hp'.2]⟩
  obtain ⟨hS₁, hB₁⟩ := hOriented S₁ _ left_injective
    (by rintro _ ⟨p, hp, rfl⟩; exact hmem₁ p hp) (fun p hp ↦ by
      rw [pairMultiplicity, Nat.cast_mul, mul_comm (ordinateWeight q p.1.1 : ℝ)]
      exact mul_le_mul_of_nonneg_right (hother _ _ (fibre_sum p) (hmem₁ p hp).2) (Nat.cast_nonneg _))
  obtain ⟨hS₂, hB₂⟩ := hOriented S₂ _ right_injective
    (by rintro _ ⟨p, hp, rfl⟩; exact hmem₂ p hp) (fun p hp ↦ by
      rw [pairMultiplicity, Nat.cast_mul]
      exact mul_le_mul_of_nonneg_right (hother _ _ (by rw [add_comm]; exact fibre_sum p)
        (hmem₂ p hp).2) (Nat.cast_nonneg _))
  have he : S₁ ∪ S₂ = S := by
    ext p
    simp only [S₁, S₂, mem_union, mem_inter_iff, mem_ofPred_eq]
    exact ⟨fun h ↦ h.elim And.left And.left, fun hp ↦
      (le_or_gt (p.1.1 : ℝ) p.1.2).imp (And.intro hp) (And.intro hp)⟩
  have hd : Disjoint S₁ S₂ := by
    apply Set.disjoint_left.mpr
    intro p hp hp'
    exact (show (p.1.2 : ℝ) < p.1.1 from hp'.2).not_ge (show (p.1.1 : ℝ) ≤ p.1.2 from hp.2)
  change (∑ᶠ p ∈ S, (pairMultiplicity p : ℝ)) ≤ _
  rw [← he, finsum_mem_union hd hS₁ hS₂]
  linarith

private theorem fibre_orientations (p : pairFibre q τ) :
    let u := negativeHeight p
    ((p.1.1 : ℝ) = -u ∧ (p.1.2 : ℝ) = u + τ) ∨
      ((p.1.1 : ℝ) = u + τ ∧ (p.1.2 : ℝ) = -u) := by
  rcases le_or_gt (p.1.1 : ℝ) p.1.2 with h | h
  · left
    dsimp [negativeHeight]
    rw [min_eq_left h]
    constructor <;> linarith [fibre_sum p]
  · right
    dsimp [negativeHeight]
    rw [min_eq_right h.le]
    constructor <;> linarith [fibre_sum p]

private theorem finite_fibre_height (a b : ℝ) :
    {p : pairFibre q τ | negativeHeight p ∈ Icc a b}.Finite := by
  let T := Ordinates q ∩ Icc (min (-b) (a + τ)) (max (-a) (b + τ))
  have hT : T.Finite := finite_Ordinates_inter _ _
  refine (hT.preimage (left_injective (q := q) (τ := τ)).injOn).subset ?_
  intro p hp
  have hp' : negativeHeight p ∈ Icc a b := hp
  refine ⟨p.1.1.prop, ?_⟩
  rcases fibre_orientations p with ⟨h, _⟩ | ⟨h, _⟩
  · exact ⟨(min_le_left _ _).trans (by linarith [hp'.2]),
      (show (p.1.1 : ℝ) ≤ -a by linarith [hp'.1]).trans (le_max_left _ _)⟩
  · exact ⟨(min_le_right _ _).trans (by linarith [hp'.1]),
      (show (p.1.1 : ℝ) ≤ b + τ by linarith [hp'.2]).trans (le_max_right _ _)⟩

private theorem lt_negativeHeight {U Y : ℝ} (hUY : Y + 1 ≤ U) (hY : 0 < Y) (hτ : |τ| ≤ Y)
    (p : pairFibre q τ) (hp₁ : U < |(p.1.1 : ℝ)|) (hp₂ : U < |(p.1.2 : ℝ)|) :
    U < negativeHeight p := by
  rcases le_or_gt (p.1.1 : ℝ) p.1.2 with h | h
  · have hn : (p.1.1 : ℝ) < 0 := by
      by_contra! hn
      rw [abs_of_nonneg hn] at hp₁
      linarith [le_abs_self τ, fibre_sum p]
    rwa [negativeHeight, min_eq_left h, ← abs_of_neg hn]
  · have hn : (p.1.2 : ℝ) < 0 := by
      by_contra! hn
      rw [abs_of_nonneg hn] at hp₂
      linarith [le_abs_self τ, fibre_sum p]
    rwa [negativeHeight, min_eq_right h.le, ← abs_of_neg hn]

/-- The abstract cone yields a nonzero summed residue if every representation
comes from sufficiently large ordinates. -/
theorem exists_pairResidue_ne_zero_unconditional (hStir : Phi2HInf.StirlingStrip) {Y : ℝ} (hY : 0 < Y) :
    ∃ U : ℝ, Y + 1 ≤ U ∧ ∀ τ : ℝ, |τ| ≤ Y →
      Nonempty (pairFibre q τ) →
      (∀ p : pairFibre q τ, U < |(p.1.1 : ℝ)| ∧ U < |(p.1.2 : ℝ)|) →
      pairResidue q τ ≠ 0 := by
  obtain ⟨K, hBins⟩ := pair_bin_bound (q := q) hY
  obtain ⟨U, hU, hcone⟩ := Phi2HInf.sum_bKer_ne_zero_hinf hStir
    (B := 1 / 2) (K := K) (by norm_num) (by norm_num) hY
  refine ⟨U, hU, fun τ hτ ⟨p₀⟩ hp ↦ ?_⟩
  have hlarge (p : pairFibre q τ) : U < negativeHeight p :=
    lt_negativeHeight hU hY hτ p (hp p).1 (hp p).2
  have hS := finite_fibre_height (q := q) (τ := τ) U (negativeHeight p₀)
  obtain ⟨p, hpm, hmin⟩ := Set.exists_min_image _ negativeHeight hS
    ⟨p₀, (hlarge p₀).le, le_rfl⟩
  have hpm' : U ≤ negativeHeight p ∧ negativeHeight p ≤ negativeHeight p₀ := hpm
  have hmin' (p' : pairFibre q τ) : negativeHeight p ≤ negativeHeight p' := by
    by_cases h : negativeHeight p' ≤ negativeHeight p₀
    · exact hmin p' ⟨(hlarge p').le, h⟩
    · exact hpm'.2.trans (le_of_lt (lt_of_not_ge h))
  have hweight : 1 ≤ pairMultiplicity p :=
    Nat.mul_pos p.1.1.prop p.1.2.prop
  obtain ⟨_, hn⟩ := hcone τ hτ (fun _ ↦ 1 / 2) (fun _ ↦ 1 / 2) negativeHeight
    pairMultiplicity p (by intro; norm_num) (by intro; rfl) hpm'.1 hmin' hweight
    (fun v ↦ (finite_fibre_height v (v + 1)).subset (fun _ h ↦ ⟨h.1, h.2.le⟩)) (hBins τ hτ)
  have hval (p : pairFibre q τ) :
      pairWeight q p.1 = principalWeight q ^ 2 *
        ((pairMultiplicity p : ℂ) * Phi2HInf.bKerH (1 / 2) (1 / 2) τ (negativeHeight p)) := by
    rcases fibre_orientations p with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;>
      simp only [pairWeight, gammaWeight, pairMultiplicity, Phi2HInf.bKerH, criticalPoint,
        Nat.cast_mul, ofReal_div, ofReal_one, ofReal_ofNat, h₁, h₂, ofReal_neg, neg_mul, sub_eq_add_neg] <;>
      ring
  have hq₀ : principalWeight q ≠ 0 :=
    inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (NeZero.pos q)).ne')
  unfold pairResidue
  simp_rw [hval, tsum_mul_left]
  exact mul_ne_zero (pow_ne_zero _ hq₀) hn

theorem exists_pairResidue_ne_zero (hGRH : GRH q) (hStir : Phi2HInf.StirlingStrip) {Y : ℝ} (hY : 0 < Y) :
    ∃ U : ℝ, Y + 1 ≤ U ∧ ∀ τ : ℝ, |τ| ≤ Y →
      Nonempty (pairFibre q τ) →
      (∀ p : pairFibre q τ, U < |(p.1.1 : ℝ)| ∧ U < |(p.1.2 : ℝ)|) →
      pairResidue q τ ≠ 0 :=
  exists_pairResidue_ne_zero_unconditional hStir hY

end GoldbachBoundaries.ResidueClass
