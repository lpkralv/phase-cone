import GoldbachBoundaries.ResidueClass.ZeroWindows
import GoldbachBoundaries.ResidueClass.LFunctionGrowth

/-! # Logarithmic bound for the critical-line zero count -/

noncomputable section

open Complex Filter Metric Set

namespace GoldbachBoundaries.ResidueClass

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

private theorem jensenFunction_centre_lower (V : ℝ) :
    ‖riemannZeta 2‖⁻¹ ≤ ‖jensenFunction χ (2 + (V : ℂ) * I)‖ := by
  classical
  let c : ℂ := 2 + (V : ℂ) * I
  have hre : c.re = 2 := by simp [c]
  by_cases hχ : χ = 1
  · subst χ
    have hne : c ≠ 1 := by intro h; rw [h] at hre; norm_num at hre
    have hdist : 1 ≤ ‖c - 1‖ := by
      exact le_trans (by norm_num [sub_re, hre]) (Complex.re_le_norm _)
    change ‖riemannZeta 2‖⁻¹ ≤ ‖jensenFunction (1 : DirichletCharacter ℂ q) c‖
    simp only [jensenFunction, ite_true, DirichletCharacter.LFunctionTrivChar₁,
      Function.update_of_ne hne, norm_mul]
    refine (inv_norm_zeta_two_le_norm_lFunction (ψ := (1 : DirichletCharacter ℂ 1)) hre).trans ?_
    exact le_mul_of_one_le_left (norm_nonneg _) hdist
  · let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    simpa [jensenFunction, hχ, primitiveL, c] using
      inv_norm_zeta_two_le_norm_lFunction (ψ := χ.primitiveCharacter) hre

private theorem jensenFunction_outer_bound (V : ℝ) {z : ℂ}
    (hz : z ∈ sphere (2 + (V : ℂ) * I) (7 / 4)) :
    ‖jensenFunction χ z‖ ≤ 5 * (q : ℝ) * (|V| + 4)^2 := by
  classical
  let c : ℂ := 2 + (V : ℂ) * I
  have hre : c.re = 2 := by simp [c]
  have hd : ‖z - c‖ = 7 / 4 := by simpa only [mem_sphere, dist_eq_norm, c] using hz
  have hzre : 1 / 4 ≤ z.re := by
    have hh := (abs_le.mp ((abs_re_le_norm (z - c)).trans_eq hd)).1
    simp only [sub_re, hre] at hh
    linarith
  have hzpos : 0 < z.re := (by norm_num : (0 : ℝ) < 1 / 4).trans_le hzre
  have hzinv : z.re⁻¹ ≤ 4 := by
    rw [← one_div, div_le_iff₀ hzpos]
    linarith
  have hV : ‖((V : ℂ) * I)‖ = |V| := by simp [Real.norm_eq_abs]
  have h₀ := norm_add_le (z - c) c
  have h₁ := norm_add_le (z - c) (1 + (V : ℂ) * I)
  have hc := norm_add_le (2 : ℂ) ((V : ℂ) * I)
  have hc₁ := norm_add_le (1 : ℂ) ((V : ℂ) * I)
  have hz₀ : ‖z‖ ≤ |V| + 4 := by
    rw [sub_add_cancel, hd] at h₀
    rw [hV, norm_ofNat] at hc
    change ‖c‖ ≤ 2 + |V| at hc
    linarith
  have hz₁ : ‖z - 1‖ ≤ |V| + 4 := by
    have heq : z - c + (1 + (V : ℂ) * I) = z - 1 := by dsimp [c]; ring
    rw [heq, hd] at h₁
    rw [hV, norm_one] at hc₁
    linarith
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hX : 1 ≤ |V| + 4 := by linarith [abs_nonneg V]
  have hX' : |V| + 4 ≤ (|V| + 4)^2 := by
    simpa [pow_two] using mul_le_mul_of_nonneg_right hX (show 0 ≤ |V| + 4 by positivity)
  by_cases hχ : χ = 1
  · simp only [jensenFunction, hχ, ite_true]
    calc
      _ ≤ ‖z‖ + ‖z - 1‖ * ‖z‖ * z.re⁻¹ := by
        simpa only [div_eq_mul_inv] using norm_regularized_zeta_le hzpos
      _ ≤ (|V| + 4) + (|V| + 4) * (|V| + 4) * 4 := by gcongr
      _ ≤ 5 * (q : ℝ) * (|V| + 4)^2 := by
        have hq' := mul_le_mul_of_nonneg_right hq (sq_nonneg (|V| + 4))
        nlinarith
  · let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    have hm : (χ.conductor : ℝ) ≤ q :=
      by exact_mod_cast Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level
    simp only [jensenFunction, hχ, ite_false, primitiveL]
    calc
      _ ≤ (χ.conductor : ℝ) * ‖z‖ * z.re⁻¹ := by
        simpa only [div_eq_mul_inv] using norm_lFunction_le (primitiveCharacter_ne_one χ hχ) hzpos
      _ ≤ (q : ℝ) * (|V| + 4) * 4 := by gcongr
      _ ≤ 5 * (q : ℝ) * (|V| + 4)^2 := by
        have hq' := mul_le_mul_of_nonneg_left hX' (show 0 ≤ (q : ℝ) by positivity)
        have hq'' : 0 ≤ (q : ℝ) * (|V| + 4)^2 := by positivity
        linarith

/-- At fixed modulus, the multiplicity of each inducing function in a
length-one window is at most a constant times `log (|V| + 4)`, uniformly in
the character and window centre. -/
theorem exists_primitive_window_mass_bound (hGRH : GRH q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (χ : DirichletCharacter ℂ q) (V : ℝ),
      (∑ᶠ ρ ∈ zeroWindow χ (V - 1 / 2) (V + 1 / 2), (primitiveMult χ ρ : ℝ)) ≤
        C * Real.log (|V| + 4) := by
  let B : ℝ := 5 * (q : ℝ) * max 1 ‖riemannZeta 2‖
  let gapLog : ℝ := Real.log (35 / 32)
  have hL : 0 < gapLog := Real.log_pos (by norm_num)
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hB : 1 ≤ B := by
    calc
      _ ≤ (5 : ℝ) * 1 * 1 := by norm_num
      _ ≤ B := by
        dsimp [B]
        gcongr
        exact le_max_left _ _
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB
  refine ⟨(Real.log B / Real.log 4 + 2) / gapLog, by positivity, ?_⟩
  intro χ V
  let X : ℝ := |V| + 4
  let M : ℝ := 5 * (q : ℝ) * X^2
  have hX : 4 ≤ X := by dsimp [X]; linarith [abs_nonneg V]
  have hXpos : 0 < X := by linarith
  have hM : 1 ≤ M := by
    calc
      _ ≤ (5 : ℝ) * 1 * 4^2 := by norm_num
      _ ≤ M := by dsimp [M]; gcongr
  have hc := jensenFunction_centre_lower χ V
  have hzeta : 0 < ‖riemannZeta 2‖ :=
    norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_le_re (by norm_num))
  have hcpos : 0 < ‖jensenFunction χ (2 + (V : ℂ) * I)‖ := (inv_pos.mpr hzeta).trans_le hc
  have hratio : M / ‖jensenFunction χ (2 + (V : ℂ) * I)‖ ≤ B * X^2 := by
    calc
      _ ≤ M / ‖riemannZeta 2‖⁻¹ := div_le_div_of_nonneg_left (by positivity) (inv_pos.mpr hzeta) hc
      _ = 5 * (q : ℝ) * ‖riemannZeta 2‖ * X^2 := by
        rw [div_inv_eq_mul]
        dsimp [M]
        ring
      _ ≤ _ := by
        dsimp [B]
        gcongr
        exact le_max_right _ _
  have hlogX : Real.log 4 ≤ Real.log X := Real.log_le_log (by norm_num) hX
  have hscale : Real.log B ≤ Real.log B / Real.log 4 * Real.log X := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog4]
    exact mul_le_mul_of_nonneg_left hlogX hlogB
  have hJ := primitive_window_mass_le_jensen χ hGRH V M hM (fun _ hz ↦ jensenFunction_outer_bound χ V hz)
  refine hJ.trans ?_
  change Real.log (M / ‖jensenFunction χ (2 + (V : ℂ) * I)‖) / gapLog ≤
    (Real.log B / Real.log 4 + 2) / gapLog * Real.log X
  rw [div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ hL.le
  refine (Real.log_le_log (div_pos (lt_of_lt_of_le zero_lt_one hM) hcpos) hratio).trans ?_
  rw [Real.log_mul (ne_of_gt (zero_lt_one.trans_le hB)) (pow_ne_zero _ hXpos.ne'),
    Real.log_pow]
  push_cast
  nlinarith

/-- The aggregate count over distinct ordinates equals the sum of the
individual multiplicity counts, including zeros shared by different characters. -/
theorem ordinate_window_mass_eq_sum (hGRH : GRH q) (a b : ℝ) :
    (∑ᶠ t ∈ Ordinates q ∩ Icc a b, (ordinateWeight q t : ℝ)) =
      ∑ χ : DirichletCharacter ℂ q, ∑ᶠ ρ ∈ zeroWindow χ a b, (primitiveMult χ ρ : ℝ) := by
  classical
  let S := Ordinates q ∩ Icc a b
  let F := finite_Ordinates_inter (q := q) a b
  change (∑ᶠ t ∈ S, (ordinateWeight q t : ℝ)) = _
  rw [finsum_mem_eq_finite_toFinset_sum _ F]
  simp only [ordinateWeight, totalMult, Nat.cast_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro χ _
  let T := criticalPoint ⁻¹' zeroWindow χ a b
  have hne (t : ℝ) : criticalPoint t ≠ 1 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num [criticalPoint_re] at hh
  have hS : T ⊆ S := by
    intro t ht
    exact ⟨mem_Ordinates_iff.mpr ⟨χ, ht.1⟩, by simpa only [criticalPoint_im] using ht.2⟩
  have hS' : S ∩ Function.support (fun t ↦ (primitiveMult χ (criticalPoint t) : ℝ)) ⊆ T := by
    rintro t ⟨ht, hpos⟩
    have hp : 0 < primitiveMult χ (criticalPoint t) := by
      rw [Function.mem_support, Nat.cast_ne_zero] at hpos
      omega
    have hz := (primitiveMult_pos_iff χ (hne t)).mp hp
    exact ⟨⟨hz, by norm_num [criticalPoint_re], by norm_num [criticalPoint_re]⟩,
      by simpa only [criticalPoint_im] using ht.2⟩
  have hbij : Set.BijOn criticalPoint T (zeroWindow χ a b) := by
    refine ⟨fun _ h ↦ h, ?_, ?_⟩
    · intro t _ u _ he
      simpa only [criticalPoint_im] using congrArg Complex.im he
    · intro ρ hρ
      have he : criticalPoint ρ.im = ρ :=
        Complex.ext (by rw [criticalPoint_re, hGRH χ ρ hρ.1]) (criticalPoint_im _)
      exact ⟨ρ.im, by simpa only [T, Set.mem_preimage, he] using hρ, he⟩
  have hEq : (∑ᶠ t ∈ T, (primitiveMult χ (criticalPoint t) : ℝ)) =
      ∑ t ∈ F.toFinset, (primitiveMult χ (criticalPoint t) : ℝ) := by
    apply finsum_mem_eq_sum_of_inter_support_eq
    rw [F.coe_toFinset]
    exact subset_antisymm (inter_subset_inter_left _ hS)
      (fun t ht ↦ ⟨hS' ht, ht.2⟩)
  rw [← hEq]
  exact finsum_mem_eq_of_bijOn _ hbij (fun _ _ ↦ rfl)

/-- The existential-constant form of equation (11) of the binary proof. -/
theorem exists_ordinate_window_mass_bound (hGRH : GRH q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ V : ℝ,
      (∑ᶠ t ∈ Ordinates q ∩ Icc (V - 1 / 2) (V + 1 / 2), (ordinateWeight q t : ℝ)) ≤
        C * Real.log (|V| + 4) := by
  obtain ⟨C, hC, hmass⟩ := exists_primitive_window_mass_bound hGRH
  refine ⟨(Fintype.card (DirichletCharacter ℂ q) : ℝ) * C, by positivity, fun V ↦ ?_⟩
  rw [ordinate_window_mass_eq_sum hGRH]
  calc
    _ ≤ ∑ _χ : DirichletCharacter ℂ q, C * Real.log (|V| + 4) :=
      Finset.sum_le_sum fun χ _ ↦ hmass χ V
    _ = _ := by simp [mul_assoc]

/-- Two adjacent length-one windows give the radius-one bound used in the
local expansion. The midpoint may be counted twice in the upper bound. -/
theorem exists_primitive_unit_radius_mass_bound (hGRH : GRH q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (χ : DirichletCharacter ℂ q) (V : ℝ),
      (∑ᶠ ρ ∈ {ρ ∈ primitiveZeros χ | |ρ.im - V| ≤ 1}, (primitiveMult χ ρ : ℝ)) ≤
        C * Real.log (|V| + 4) := by
  classical
  obtain ⟨C, hC, hmass⟩ := exists_primitive_window_mass_bound hGRH
  refine ⟨4 * C, by positivity, fun χ V ↦ ?_⟩
  let f : ℂ → ℝ := fun ρ ↦ (primitiveMult χ ρ : ℝ)
  let S := zeroWindow χ (V - 1) (V + 1)
  let A := zeroWindow χ (V - 1) V
  let B := zeroWindow χ V (V + 1)
  have hS : {ρ ∈ primitiveZeros χ | |ρ.im - V| ≤ 1} = S := by
    ext ρ
    simp only [S, zeroWindow, mem_ofPred_eq, Set.mem_Icc, abs_le]
    constructor <;> rintro ⟨h, h₁, h₂⟩ <;> exact ⟨h, by linarith, by linarith⟩
  have hfin (a b : ℝ) :
      Function.HasFiniteSupport ((zeroWindow χ a b).indicator f) :=
    (finite_zeroWindow χ a b).subset (by
      intro ρ hρ
      by_contra hn
      exact hρ (indicator_of_notMem hn _))
  have hmass₁ := hmass χ (V - 1 / 2)
  have hmass₂ := hmass χ (V + 1 / 2)
  rw [show V - 1 / 2 - 1 / 2 = V - 1 by ring,
    show V - 1 / 2 + 1 / 2 = V by ring] at hmass₁
  rw [show V + 1 / 2 - 1 / 2 = V by ring,
    show V + 1 / 2 + 1 / 2 = V + 1 by ring] at hmass₂
  have hlog (x : ℝ) (hx : |x - V| ≤ 1 / 2) :
      Real.log (|x| + 4) ≤ 2 * Real.log (|V| + 4) := by
    have htriangle : |x| ≤ |x - V| + |V| := by
      simpa only [sub_add_cancel] using abs_add_le (x - V) V
    have hp := Real.log_pow (|V| + 4) 2
    rw [Nat.cast_ofNat] at hp
    rw [← hp]
    apply Real.log_le_log (by positivity)
    have hV := abs_nonneg V
    nlinarith [sq_nonneg |V|]
  rw [hS]
  calc
    (∑ᶠ ρ ∈ S, f ρ) ≤ (∑ᶠ ρ ∈ A, f ρ) + ∑ᶠ ρ ∈ B, f ρ := by
      simp only [finsum_mem_def]
      rw [← finsum_add_distrib (hfin (V - 1) V) (hfin V (V + 1))]
      refine finsum_le_finsum (hfin (V - 1) (V + 1))
        ((hfin (V - 1) V).add (hfin V (V + 1))) ?_
      intro ρ
      change S.indicator f ρ ≤ A.indicator f ρ + B.indicator f ρ
      by_cases hρ : ρ ∈ S
      · rw [indicator_of_mem hρ]
        by_cases hg : ρ.im ≤ V
        · rw [indicator_of_mem (show ρ ∈ A from ⟨hρ.1, hρ.2.1, hg⟩)]
          exact le_add_of_nonneg_right (indicator_apply_nonneg fun _ ↦ Nat.cast_nonneg _)
        · rw [indicator_of_mem (show ρ ∈ B from ⟨hρ.1, (lt_of_not_ge hg).le, hρ.2.2⟩)]
          exact le_add_of_nonneg_left (indicator_apply_nonneg fun _ ↦ Nat.cast_nonneg _)
      · rw [indicator_of_notMem hρ]
        exact add_nonneg (indicator_apply_nonneg fun _ ↦ Nat.cast_nonneg _)
          (indicator_apply_nonneg fun _ ↦ Nat.cast_nonneg _)
    _ ≤ C * Real.log (|V - 1 / 2| + 4) + C * Real.log (|V + 1 / 2| + 4) :=
      add_le_add hmass₁ hmass₂
    _ ≤ _ := by
      have h₁ := mul_le_mul_of_nonneg_left
        (hlog (V - 1 / 2) (by rw [show V - 1 / 2 - V = -(1 / 2) by ring]; norm_num)) hC
      have h₂ := mul_le_mul_of_nonneg_left
        (hlog (V + 1 / 2) (by rw [show V + 1 / 2 - V = 1 / 2 by ring]; norm_num)) hC
      linarith

end GoldbachBoundaries.ResidueClass
