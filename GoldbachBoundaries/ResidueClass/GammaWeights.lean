import GoldbachBoundaries.ResidueClass.JensenCount

/-! # Absolute convergence of the weighted critical-line residues -/

noncomputable section

open Complex Filter Set

namespace GoldbachBoundaries.ResidueClass

variable {q : ℕ} [NeZero q]

/-- The positive factor in front of the principal residue and the zero sum. -/
def principalWeight (q : ℕ) : ℂ := (q.totient : ℂ)⁻¹

/-- The Gamma-weighted multiplicity, with the sign of the zero residue taken outside. -/
def gammaWeight (q : ℕ) [NeZero q] (t : ℝ) : ℂ :=
  principalWeight q * (ordinateWeight q t : ℂ) * Gamma (criticalPoint t)

private theorem floor_mem_window (t : ℝ) :
    t ∈ Icc ((⌊t⌋ : ℤ) : ℝ) (((⌊t⌋ : ℤ) : ℝ) + 1) :=
  ⟨Int.floor_le t, (Int.lt_floor_add_one t).le⟩

/-- The length-one multiplicity bound and third-order Gamma decay give a summable
majorant after grouping the ordinates by integer part. -/
theorem summable_norm_gammaWeight (hGRH : GRH q) :
    Summable (fun t : Ordinates q ↦ ‖gammaWeight q t‖) := by
  classical
  obtain ⟨C, hC, hmass⟩ := exists_ordinate_window_mass_bound hGRH
  obtain ⟨G, hG⟩ := TIdentity.norm_Gamma_mul_one_add_abs_im_pow_le
    (a := 1 / 2) (a' := 1 / 2) (by norm_num) 3
  let floorOrd (t : Ordinates q) : ℤ := ⌊(t : ℝ)⌋
  let W (n : ℤ) := Ordinates q ∩ Icc (n : ℝ) ((n : ℝ) + 1)
  let hW (n : ℤ) := finite_Ordinates_inter (q := q) (n : ℝ) ((n : ℝ) + 1)
  let includeWindow (n : ℤ) (t : {t : Ordinates q // floorOrd t = n}) : W n :=
    ⟨t.1, t.1.2, by simpa only [← t.2] using floor_mem_window (t.1 : ℝ)⟩
  have hInjective (n : ℤ) : Function.Injective (includeWindow n) :=
    fun _ _ h ↦ Subtype.ext (Subtype.ext (congrArg (fun t : W n ↦ (t : ℝ)) h))
  have hfinite (n : ℤ) : Finite {t : Ordinates q // floorOrd t = n} :=
    let := (hW n).to_subtype
    Finite.of_injective (includeWindow n) (hInjective n)
  rw [← (Equiv.sigmaFiberEquiv floorOrd).summable_iff]
  change Summable (fun t : Σ n : ℤ, {t : Ordinates q // floorOrd t = n} ↦
    ‖gammaWeight q (t.2.1 : ℝ)‖)
  rw [summable_sigma_of_nonneg (fun _ ↦ norm_nonneg _)]
  refine ⟨fun n ↦ by let := hfinite n; exact Summable.of_finite, ?_⟩
  let M := ‖principalWeight q‖ * (8 * |G|)
  have hM : 0 ≤ M := by positivity
  have hwindow (n : ℤ) (t : W n) :
      ‖gammaWeight q (t : ℝ)‖ ≤ M * ((ordinateWeight q t : ℝ) / (1 + |(n : ℝ)|) ^ 3) := by
    have hnt : |(n : ℝ)| ≤ |(t : ℝ)| + 1 := by
      rw [abs_le]
      constructor <;> linarith [t.2.2.1, t.2.2.2, le_abs_self (t : ℝ), neg_le_abs (t : ℝ)]
    have hg := hG (criticalPoint t) (by rw [criticalPoint_re]) (by rw [criticalPoint_re])
    rw [criticalPoint_im] at hg
    have hg' : ‖Gamma (criticalPoint t)‖ ≤ (8 * |G|) / (1 + |(n : ℝ)|) ^ 3 := by
      rw [le_div_iff₀ (by positivity)]
      calc
        _ ≤ ‖Gamma (criticalPoint t)‖ * (2 * (1 + |(t : ℝ)|)) ^ 3 := by
          gcongr
          linarith [abs_nonneg (t : ℝ)]
        _ = 8 * (‖Gamma (criticalPoint t)‖ * (1 + |(t : ℝ)|) ^ 3) := by ring
        _ ≤ _ := by gcongr; exact hg.trans (le_abs_self G)
    rw [gammaWeight, norm_mul, norm_mul, Complex.norm_natCast]
    calc
      _ ≤ ‖principalWeight q‖ * (ordinateWeight q t : ℝ) *
          ((8 * |G|) / (1 + |(n : ℝ)|) ^ 3) := by gcongr
      _ = _ := by dsimp [M]; ring
  have hmass' (n : ℤ) :
      (∑' t : W n, (ordinateWeight q t : ℝ)) ≤ C * (6 * (1 + |(n : ℝ)|)) := by
    have hleft : (n : ℝ) + 1 / 2 - 1 / 2 = n := by ring
    have hright : (n : ℝ) + 1 / 2 + 1 / 2 = n + 1 := by ring
    have h := hmass ((n : ℝ) + 1 / 2)
    rw [hleft, hright, finsum_mem_eq_finite_toFinset_sum _ (hW n)] at h
    have hL : Real.log (|(n : ℝ) + 1 / 2| + 4) ≤ 6 * (1 + |(n : ℝ)|) := by
      have h₁ := Real.log_le_self (show 0 ≤ |(n : ℝ) + 1 / 2| + 4 by positivity)
      have h₂ := abs_add_le (n : ℝ) (1 / 2)
      rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)] at h₂
      linarith [abs_nonneg (n : ℝ)]
    let : Fintype (W n) := (hW n).fintype
    rw [tsum_fintype]
    refine le_trans ?_ (h.trans (mul_le_mul_of_nonneg_left hL hC))
    exact le_of_eq (Finset.sum_subtype (hW n).toFinset (fun _ ↦ (hW n).mem_toFinset)
      (fun t : ℝ ↦ (ordinateWeight q t : ℝ))).symm
  have hfibre (n : ℤ) :
      (∑' t : {t : Ordinates q // floorOrd t = n}, ‖gammaWeight q (t.1 : ℝ)‖) ≤
        6 * M * C / (1 + |(n : ℝ)|) ^ 2 := by
    let := hfinite n
    let := (hW n).to_subtype
    calc
      _ ≤ ∑' t : W n, ‖gammaWeight q (t : ℝ)‖ :=
        hasSum_le_inj (includeWindow n) (hInjective n) (fun _ _ ↦ norm_nonneg _)
          (fun _ ↦ le_rfl) Summable.of_finite.hasSum Summable.of_finite.hasSum
      _ ≤ ∑' t : W n, M * ((ordinateWeight q t : ℝ) / (1 + |(n : ℝ)|) ^ 3) :=
        Summable.of_finite.tsum_le_tsum (hwindow n) Summable.of_finite
      _ = M * ((∑' t : W n, (ordinateWeight q t : ℝ)) / (1 + |(n : ℝ)|) ^ 3) := by
        rw [tsum_mul_left, tsum_div_const]
      _ ≤ M * (C * (6 * (1 + |(n : ℝ)|)) / (1 + |(n : ℝ)|) ^ 3) := by gcongr; exact hmass' n
      _ = _ := by field_simp
  have hsum : Summable (fun n : ℤ ↦ (6 * M * C) * (1 / (n : ℝ) ^ 2)) :=
    (Real.summable_one_div_int_pow.mpr (by decide : 1 < (2 : ℕ))).mul_left _
  refine hsum.of_norm_bounded_eventually ?_
  filter_upwards [(Set.finite_singleton (0 : ℤ)).compl_mem_cofinite] with n hn
  change n ≠ 0 at hn
  change ‖∑' t : {t : Ordinates q // floorOrd t = n}, ‖gammaWeight q (t.1 : ℝ)‖‖ ≤ _
  rw [Real.norm_of_nonneg (tsum_nonneg (fun _ ↦ norm_nonneg _))]
  refine (hfibre n).trans ?_
  rw [mul_one_div, ← sq_abs (n : ℝ)]
  exact div_le_div_of_nonneg_left (by positivity) (by exact pow_pos (abs_pos.mpr (by exact_mod_cast hn)) _)
    (pow_le_pow_left₀ (abs_nonneg _) (by linarith) _)

/-- The zero term in the explicit formula, summed over distinct ordinates. -/
def zeroTerm (q : ℕ) [NeZero q] (x : ℝ) : ℂ :=
  ∑' t : Ordinates q, gammaWeight q t * (x : ℂ) ^ (-criticalPoint t)

theorem summable_norm_zeroTerm (hGRH : GRH q) {x : ℝ} (hx : 0 < x) :
    Summable (fun t : Ordinates q ↦ ‖gammaWeight q t * (x : ℂ) ^ (-criticalPoint t)‖) := by
  refine ((summable_norm_gammaWeight hGRH).mul_right (x ^ (-(1 / 2) : ℝ))).congr fun t ↦ ?_
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx, neg_re, criticalPoint_re]

theorem norm_zeroTerm_le (hGRH : GRH q) {x : ℝ} (hx : 0 < x) :
    ‖zeroTerm q x‖ ≤ (∑' t : Ordinates q, ‖gammaWeight q t‖) * x ^ (-(1 / 2) : ℝ) := by
  refine (norm_tsum_le_tsum_norm (summable_norm_zeroTerm hGRH hx)).trans_eq ?_
  simp_rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx, neg_re, criticalPoint_re, tsum_mul_right]

end GoldbachBoundaries.ResidueClass
