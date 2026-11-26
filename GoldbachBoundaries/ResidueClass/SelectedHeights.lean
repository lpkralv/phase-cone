import GoldbachBoundaries.ResidueClass.JensenCount

/-! # Simultaneous separation of the two horizontal contour heights -/

noncomputable section

open Set MeasureTheory

namespace GoldbachBoundaries.ResidueClass

variable {q : ℕ} [NeZero q]

private theorem ordinate_window_ncard_le {V B : ℝ}
    (h : (∑ᶠ t ∈ Ordinates q ∩ Icc (V - 1 / 2) (V + 1 / 2), (ordinateWeight q t : ℝ)) ≤ B) :
    ((Ordinates q ∩ Icc (V - 1 / 2) (V + 1 / 2)).ncard : ℝ) ≤ B := by
  classical
  let F := finite_Ordinates_inter (q := q) (V - 1 / 2) (V + 1 / 2)
  refine le_trans ?_ h
  rw [Set.ncard_eq_toFinset_card _ F, finsum_mem_eq_finite_toFinset_sum _ F]
  calc
    _ = ∑ _t ∈ F.toFinset, (1 : ℝ) := by simp
    _ ≤ _ := Finset.sum_le_sum fun t ht ↦ by
      have hm : 0 < ordinateWeight q t := (F.mem_toFinset.mp ht).1
      exact_mod_cast (show 1 ≤ ordinateWeight q t from hm)

/-- For each sufficiently high unit interval choose one height that separates
both horizontal sides from every ordinate. The separation is bounded below
by the reciprocal of an affine function of the logarithm of the height. -/
theorem exists_selected_height (hGRH : GRH q) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ Y : ℝ, 2 ≤ Y → ∃ H ∈ Icc Y (Y + 1),
      ∀ t ∈ Ordinates q, 1 / (2 + K * Real.log (Y + 6)) ≤ |H - t| ∧
        1 / (2 + K * Real.log (Y + 6)) ≤ |-H - t| := by
  classical
  obtain ⟨C, hC, hmass⟩ := exists_ordinate_window_mass_bound hGRH
  refine ⟨12 * C, by positivity, fun Y hY ↦ ?_⟩
  let c (i : Fin 3) : ℝ := Y - 1 / 2 + i.val
  let W (V : ℝ) := Ordinates q ∩ Icc (V - 1 / 2) (V + 1 / 2)
  let E (i : Fin 3) := W (c i) ∪ (fun t : ℝ ↦ -t) '' W (-c i)
  let S := ⋃ i, E i
  let hf : S.Finite := Set.finite_iUnion fun i ↦
    (finite_Ordinates_inter _ _).union ((finite_Ordinates_inter _ _).image _)
  let Lg := Real.log (Y + 6)
  let d : ℝ := 1 / (2 + 12 * C * Lg)
  have hLg : 0 ≤ Lg := Real.log_nonneg (by linarith)
  have hden : 0 < 2 + 12 * C * Lg := by positivity
  have hd : 0 < d := by positivity
  have hd₁ : d ≤ 1 := (div_le_one hden).mpr (by nlinarith [mul_nonneg hC hLg])
  have hc (i : Fin 3) : 0 ≤ c i ∧ c i ≤ Y + 2 := by
    have h₀ : (0 : ℝ) ≤ i.val := by positivity
    have h₂ : (i.val : ℝ) ≤ 2 := by exact_mod_cast (show i.val ≤ 2 by omega)
    exact ⟨by dsimp [c]; linarith, by dsimp [c]; linarith⟩
  have hwin (V : ℝ) (hV : |V| ≤ Y + 2) : ((W V).ncard : ℝ) ≤ C * Lg :=
    ordinate_window_ncard_le (hmass V) |>.trans (mul_le_mul_of_nonneg_left
      (Real.log_le_log (by positivity) (by linarith)) hC)
  have hcard : (S.ncard : ℝ) ≤ 6 * C * Lg := by
    calc
      _ ≤ ∑ i : Fin 3, ((E i).ncard : ℝ) := by
        exact_mod_cast Set.ncard_iUnion_le_of_fintype E
      _ ≤ ∑ _i : Fin 3, (C * Lg + C * Lg) := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        have h₂ : (((fun t : ℝ ↦ -t) '' W (-c i)).ncard : ℝ) ≤ ((W (-c i)).ncard : ℝ) := by
          exact_mod_cast Set.ncard_image_le (finite_Ordinates_inter _ _)
        have h₀ : |c i| ≤ Y + 2 := (abs_of_nonneg (hc i).1).trans_le (hc i).2
        have hle : ((E i).ncard : ℝ) ≤ ((W (c i)).ncard : ℝ) +
            (((fun t : ℝ ↦ -t) '' W (-c i)).ncard : ℝ) := by
          exact_mod_cast Set.ncard_union_le (W (c i)) ((fun t : ℝ ↦ -t) '' W (-c i))
        exact hle.trans (add_le_add (hwin _ h₀) (h₂.trans (hwin _ (by simpa using h₀))))
      _ = _ := by simp; ring
  let Bad := ⋃ t ∈ hf.toFinset, Ioo (t - d) (t + d)
  have hvol : volume Bad < volume (Icc Y (Y + 1)) := by
    rw [Real.volume_Icc, show Y + 1 - Y = 1 by ring]
    calc
      volume Bad ≤ ∑ t ∈ hf.toFinset, volume (Ioo (t - d) (t + d)) := measure_biUnion_finset_le _ _
      _ = ∑ _t ∈ hf.toFinset, ENNReal.ofReal (2 * d) := by
        apply Finset.sum_congr rfl
        intro t _
        rw [Real.volume_Ioo, show t + d - (t - d) = 2 * d by ring]
      _ = ENNReal.ofReal ((S.ncard : ℝ) * (2 * d)) := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ by positivity), Finset.sum_const, nsmul_eq_mul,
          Set.ncard_eq_toFinset_card _ hf]
      _ < ENNReal.ofReal 1 := by
        rw [ENNReal.ofReal_lt_ofReal_iff one_pos]
        have hmul : d * (2 + 12 * C * Lg) = 1 := by dsimp [d]; field_simp [ne_of_gt hden]
        nlinarith [mul_le_mul_of_nonneg_right hcard hd.le]
  obtain ⟨H, hH, hout⟩ := Set.not_subset.mp (fun h ↦ (measure_mono h).not_gt hvol)
  have hsep (t : ℝ) (ht : t ∈ Ordinates q ∨ -t ∈ Ordinates q) : d ≤ |H - t| := by
    by_contra! hn
    obtain ⟨hlo, hhi⟩ := abs_lt.mp hn
    have hb : t ∈ Icc (Y - 1) (Y + 2) := ⟨by linarith [hH.1], by linarith [hH.2]⟩
    have hcover : ∃ i, t ∈ Icc (c i - 1 / 2) (c i + 1 / 2) := by
      by_cases h₀ : t ≤ Y
      · refine ⟨(0 : Fin 3), ?_⟩
        constructor <;> norm_num [c] <;> linarith [hb.1]
      · by_cases h₁ : t ≤ Y + 1
        · refine ⟨(1 : Fin 3), ?_⟩
          constructor <;> norm_num [c] <;> linarith
        · refine ⟨(2 : Fin 3), ?_⟩
          constructor <;> norm_num [c] <;> linarith [hb.2]
    obtain ⟨i, hi⟩ := hcover
    have htS : t ∈ S := by
      apply Set.mem_iUnion.mpr
      refine ⟨i, ?_⟩
      rcases ht with ht | ht
      · exact Or.inl ⟨ht, hi⟩
      · exact Or.inr ⟨-t, ⟨ht, ⟨by linarith [hi.2], by linarith [hi.1]⟩⟩, neg_neg _⟩
    apply hout
    exact Set.mem_iUnion.mpr ⟨t, Set.mem_iUnion.mpr ⟨hf.mem_toFinset.mpr htS,
      ⟨by linarith, by linarith⟩⟩⟩
  refine ⟨H, hH, fun t ht ↦ ⟨hsep t (.inl ht), ?_⟩⟩
  have h := hsep (-t) (.inr (by simpa using ht))
  convert h using 1
  rw [← abs_neg]
  congr 1
  ring

end GoldbachBoundaries.ResidueClass
