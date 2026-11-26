import GoldbachBoundaries.PhaseCone.Sector

/-! The sector cone with polynomial coefficient mass in unit height bins. -/

noncomputable section

open Complex Filter Set Topology

namespace GoldbachBoundaries.PhaseCone

open Phi2HInf

-- Sector is a legacy module, so `import all` is unavailable. Resolve its
-- private helpers by their Lean names to reuse them without editing Sector.lean.
open Lean in
local macro "sector_helper " name:ident : term =>
  pure (mkIdent (mkPrivateNameCore `GoldbachBoundaries.PhaseCone.Sector
    (`GoldbachBoundaries.PhaseCone ++ name.getId)))

private theorem summable_shift_rpow_exp (p : ℝ) :
    Summable fun n : ℕ => (2 + (n : ℝ)) ^ p * Real.exp (-Real.pi * n) := by
  let m := ⌈p⌉₊
  have hm : p ≤ (m : ℝ) := Nat.le_ceil p
  have hs := (summable_nat_add_iff 2).2 (Real.summable_pow_mul_exp_neg_nat_mul m Real.pi_pos)
  have hs' : Summable fun n : ℕ => (2 + (n : ℝ)) ^ m * Real.exp (-Real.pi * n) := by
    apply (hs.mul_left (Real.exp (Real.pi * 2))).congr
    intro n
    push_cast
    rw [← mul_assoc, mul_comm (Real.exp (Real.pi * 2)), mul_assoc, ← Real.exp_add]
    ring_nf
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hs'
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le (by linarith [Nat.cast_nonneg (α := ℝ) n]) hm

set_option maxHeartbeats 600000 in
/-- The sector cone with polynomial bin mass of any nonnegative real degree. -/
theorem sum_bKer_ne_zero_sector_poly (hStir : StirlingStrip) {B Y K a δ A : ℝ}
    (hB : 1 / 2 ≤ B) (hB1 : B < 1) (hY : 0 < Y) (ha : 0 < a)
    (hA : 0 ≤ A) (hδ0 : 0 ≤ δ) (hδ : δ < Real.pi * (1 - B)) :
    ∃ U : ℝ, Y + 1 ≤ U ∧ ∀ τ : ℝ, |τ| ≤ Y →
      ∀ {ι : Type} (b c u : ι → ℝ) (d : ι → ℂ) (i₀ : ι),
      (∀ i, b i ∈ Icc (1 - B) B ∧ c i ∈ Icc (1 - B) B) →
      (∀ i, b i + c i = b i₀ + c i₀) → U ≤ u i₀ → (∀ i, u i₀ ≤ u i) → a ≤ ‖d i₀‖ →
      (∃ ω : ℂ, ‖ω‖ = 1 ∧ ∀ i, ∃ φ : ℝ, |φ| ≤ δ ∧
        d i = ω * (‖d i‖ : ℂ) * exp ((φ : ℂ) * I)) →
      (∀ v : ℝ, {i | u i ∈ Ico v (v + 1)}.Finite) →
      (∀ v : ℝ, 0 ≤ v →
        (∑ᶠ i ∈ {i | u i ∈ Ico v (v + 1)}, ‖d i‖) ≤ K * (v + Y + 4) ^ A) →
      Summable (fun i => ‖d i * bKerH (b i) (c i) τ (u i)‖) ∧
        ∑' i, d i * bKerH (b i) (c i) τ (u i) ≠ 0 := by
  classical
  obtain ⟨Uc, hUc, hcone⟩ := (sector_helper bKer_sector_projection) hStir hB hB1 hY hδ0 hδ
  obtain ⟨D, Ud, hD, _, hdecay⟩ := norm_bKer_ratio_le hStir hB hB1 hY
  let k := Real.sin ((Real.pi * (1 - B) - δ) / 2)
  have hk : 0 < k := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith
    · nlinarith [Real.pi_pos, mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hB)]
  let K' := max K 0
  have hK' : 0 ≤ K' := le_max_right _ _
  -- Choose the cutoff for the tail independently of the family.
  let majorant (n : ℕ) :=
    (K' * D * (Y + 6) ^ A) * ((2 + n) ^ (2 * A + 1) * Real.exp (-Real.pi * n))
  have hmajorant0 (n : ℕ) : 0 ≤ majorant n := by dsimp [majorant]; positivity
  have hmajorant : Summable majorant := (summable_shift_rpow_exp (2 * A + 1)).mul_left _
  obtain ⟨N, hN⟩ := ((tendsto_order.1 (tendsto_sum_nat_add majorant)).2
    (a * k / 2) (by positivity)).exists
  refine ⟨max Uc (max Ud (((N : ℝ) + 1) ^ 2)), hUc.trans (le_max_left _ _), ?_⟩
  intro τ hτ ι b c u d i₀ hbc hα hU hmin hmass ⟨ω, hω, hsector⟩ hfin hBins
  let u₀ := u i₀
  have hu₀c : Uc ≤ u₀ := (le_max_left _ _).trans hU
  have hu₀d : Ud ≤ u₀ := (le_max_left _ _).trans ((le_max_right _ _).trans hU)
  have hu₀N : ((N : ℝ) + 1) ^ 2 ≤ u₀ := (le_max_right _ _).trans ((le_max_right _ _).trans hU)
  have hu₀1 : 1 ≤ u₀ := by linarith [hUc.trans hu₀c]
  let w (i : ι) := bKerH (b i) (c i) τ (u i)
  let M := ‖w i₀‖
  have hM : 0 < M := by
    apply norm_pos_iff.mpr
    change bKerH (b i₀) (c i₀) τ u₀ ≠ 0
    rw [bKerH]
    exact mul_ne_zero (Complex.Gamma_ne_zero_of_re_pos (by simp; linarith [(hbc i₀).1.1]))
      (Complex.Gamma_ne_zero_of_re_pos (by simp; linarith [(hbc i₀).2.1]))
  let g (i : ι) := ‖w i‖ / M
  have hg (i : ι) : 0 ≤ g i := div_nonneg (norm_nonneg _) hM.le
  let ψ (n : ℕ) := D * (2 + n) * Real.exp (-Real.pi * n)
  have hψ (n : ℕ) : 0 ≤ ψ n := by dsimp [ψ]; positivity
  have hgle (i : ι) : g i ≤ ψ ⌊u i - u₀⌋₊ := by
    have hratio := hdecay (b i) (hbc i).1 (c i) (hbc i).2 (b i₀) (hbc i₀).1 (c i₀)
      (hbc i₀).2 (hα i) τ hτ u₀ (u i) hu₀d (hmin i)
    apply (div_le_iff₀ hM).mpr
    refine hratio.trans (mul_le_mul_of_nonneg_right ?_ hM.le)
    have hfloor := Nat.floor_le (sub_nonneg.mpr (hmin i))
    have hceil := Nat.lt_floor_add_one (u i - u₀)
    dsimp [ψ]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hD.le)
      (Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])) (Real.exp_pos _).le (by positivity)
  -- The bin majorant before restricting to the tail.
  let W (n : ℕ) := K' * (u₀ + n + Y + 4) ^ A
  have hW (n : ℕ) :
      (∑ᶠ i ∈ {i | u i ∈ Ico (u₀ + n) (u₀ + n + 1)}, ‖d i‖) ≤ W n :=
    (hBins (u₀ + n) (by positivity)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hW0 (n : ℕ) : 0 ≤ W n := by dsimp [W]; positivity
  have hsumW : Summable fun n => W n * ψ n := by
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (hW0 n) (hψ n)) (fun n => ?_)
      ((summable_shift_rpow_exp (A + 1)).mul_left (K' * D * (u₀ + Y + 4) ^ A))
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hbase : u₀ + n + Y + 4 ≤ (u₀ + Y + 4) * (2 + n) := by
      nlinarith only [hu₀1, hY, hn, mul_nonneg hn (show 0 ≤ u₀ + Y + 3 by linarith)]
    have hp := Real.rpow_le_rpow (by positivity) hbase hA
    rw [Real.mul_rpow (by positivity) (by positivity)] at hp
    rw [Real.rpow_add_one (by positivity)]
    have hh := mul_le_mul_of_nonneg_left hp
      (by positivity : 0 ≤ K' * D * (2 + n) * Real.exp (-Real.pi * n))
    dsimp [W, ψ]
    nlinarith only [hh]
  obtain ⟨hSn, _⟩ := (sector_helper fibre_tsum_le) u (fun i => ‖d i‖) u₀ hmin
    (fun i => norm_nonneg _) hfin W hW g ψ hg hψ hgle hsumW
  -- Only bins with n + 1 > √u₀ can meet the tail. Those bins also satisfy n ≥ N.
  let r := Real.sqrt u₀
  let t (i : ι) := if u i ≤ u₀ + r then 0 else g i
  let ψT (n : ℕ) := if (n : ℝ) + 1 ≤ r then 0 else ψ n
  let AN (n : ℕ) := if N ≤ n then majorant n else 0
  have hAN0 (n : ℕ) : 0 ≤ AN n := by dsimp [AN]; split_ifs <;> simp [hmajorant0 n]
  have hANs : Summable AN := Summable.of_nonneg_of_le hAN0
    (fun n => by dsimp [AN]; split_ifs <;> simp [hmajorant0 n]) hmajorant
  have hNr : (N : ℝ) + 1 ≤ r := Real.le_sqrt_of_sq_le hu₀N
  have hWψ (n : ℕ) : W n * ψT n ≤ AN n := by
    by_cases hn : (n : ℝ) + 1 ≤ r
    · simpa [ψT, hn] using hAN0 n
    · have hn' : r < (n : ℝ) + 1 := lt_of_not_ge hn
      have hNn : N ≤ n := by exact_mod_cast (by linarith : (N : ℝ) ≤ n)
      have hu₀n : u₀ < ((n : ℝ) + 1) ^ 2 := by
        rw [← Real.sq_sqrt (by linarith : (0 : ℝ) ≤ u₀)]
        exact pow_lt_pow_left₀ hn' (Real.sqrt_nonneg u₀) (by norm_num)
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hpoly : u₀ + n + Y + 4 ≤ (Y + 6) * (2 + n) ^ 2 := by
        nlinarith only [hu₀n, hn0,
          mul_nonneg hY.le (by nlinarith only [hn0, sq_nonneg (n : ℝ)] : 0 ≤ (2 + (n : ℝ)) ^ 2 - 1)]
      have hp := Real.rpow_le_rpow (by positivity) hpoly hA
      rw [Real.mul_rpow (by positivity) (by positivity),
        ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)] at hp
      norm_num at hp
      have hh := mul_le_mul_of_nonneg_left hp
        (by positivity : 0 ≤ K' * D * (2 + n) * Real.exp (-Real.pi * n))
      simp only [W, ψT, ite_eq_right hn, ψ, AN, ite_eq_left hNn, majorant]
      rw [Real.rpow_add_one (by positivity)]
      nlinarith only [hh]
  have hψT0 (n : ℕ) : 0 ≤ ψT n := by dsimp [ψT]; split_ifs <;> simp [hψ n]
  have hWψs : Summable fun n => W n * ψT n :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (hW0 n) (hψT0 n)) hWψ hANs
  have htψ (i : ι) : t i ≤ ψT ⌊u i - u₀⌋₊ := by
    by_cases hi : u i ≤ u₀ + r
    · simpa [t, hi] using hψT0 ⌊u i - u₀⌋₊
    · have hceil := Nat.lt_floor_add_one (u i - u₀)
      have hn : ¬ (⌊u i - u₀⌋₊ : ℝ) + 1 ≤ r := by
        intro hn
        exact hi (by linarith)
      simpa [t, hi, ψT, hn] using hgle i
  obtain ⟨hTs, hTle⟩ := (sector_helper fibre_tsum_le) u (fun i => ‖d i‖) u₀ hmin (fun i => norm_nonneg _) hfin
    W hW t ψT (fun i => by dsimp [t]; split_ifs <;> simp [hg i]) hψT0 htψ hWψs
  have hT : ∑' i, ‖d i‖ * t i ≤ a * k / 2 := by
    refine hTle.trans ((hWψs.tsum_le_tsum hWψ hANs).trans ?_)
    rw [← hANs.sum_add_tsum_nat_add N, Finset.sum_eq_zero (fun n hn => by
      simp [AN, Nat.not_le.mpr (Finset.mem_range.mp hn)])]
    simpa [AN, Nat.le_add_left] using hN.le
  -- Rotate by the inverse of the common direction and by the central Gamma phase.
  let rot := ω⁻¹ * coneRotation τ u₀
  have hωne : ω ≠ 0 := by intro h; simp [h] at hω
  have hrot : ‖rot‖ = 1 := by simp [rot, norm_inv, hω, norm_coneRotation]
  let f (i : ι) := rot * (d i * w i) / (M : ℂ)
  have hnorm (i : ι) : ‖f i‖ = ‖d i‖ * g i := by
    simp [f, g, hrot, Real.norm_of_nonneg hM.le, mul_div_assoc]
  have hproj (i : ι) (hi : u i ≤ u₀ + r) : k * (‖d i‖ * g i) ≤ (f i).re := by
    obtain ⟨φ, hφ, hd⟩ := hsector i
    have he : rot * (d i * w i) = (‖d i‖ : ℂ) *
        ((exp ((φ : ℂ) * I) * coneRotation τ u₀) * w i) := by
      unfold rot
      conv_lhs => rw [hd]
      calc
        _ = (ω⁻¹ * ω) * ((‖d i‖ : ℂ) *
            ((exp ((φ : ℂ) * I) * coneRotation τ u₀) * w i)) := by ring
        _ = _ := by rw [inv_mul_cancel₀ hωne, one_mul]
    have hp := hcone (b i) (hbc i).1 (c i) (hbc i).2 τ hτ u₀ (u i) φ hu₀c (hmin i) hi hφ
    dsimp only [f]
    rw [he, mul_div_assoc, Complex.re_ofReal_mul, Complex.div_ofReal_re]
    calc
      k * (‖d i‖ * g i) = ‖d i‖ * (k * ‖w i‖ / M) := by dsimp [g]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hp hM.le) (norm_nonneg _)
  have hlow (i : ι) :
      (if i = i₀ then a * k else 0) - ‖d i‖ * t i ≤ (f i).re := by
    by_cases hi : u i ≤ u₀ + r
    · simp only [t, ite_eq_left hi, mul_zero, sub_zero]
      split_ifs with h
      · subst i
        have hg₀ : g i₀ = 1 := div_self hM.ne'
        simpa [hg₀, mul_comm k] using
          (mul_le_mul_of_nonneg_left hmass hk.le).trans (by simpa [hg₀] using hproj i₀ hi)
      · exact (mul_nonneg hk.le (mul_nonneg (norm_nonneg _) (hg i))).trans (hproj i hi)
    · have hne : i ≠ i₀ := fun h => hi (by subst i; exact le_add_of_nonneg_right (Real.sqrt_nonneg _))
      simpa [t, hi, hne, hnorm i] using (abs_le.mp (Complex.abs_re_le_norm (f i))).1
  have hSf : Summable f := Summable.of_norm (hSn.congr fun i => (hnorm i).symm)
  have hind : Summable fun i => if i = i₀ then a * k else 0 := (hasSum_ite_eq i₀ (a * k)).summable
  have hge : a * k - ∑' i, ‖d i‖ * t i ≤ (∑' i, f i).re := by
    rw [Complex.re_tsum hSf]
    calc
      _ = ∑' i, ((if i = i₀ then a * k else 0) - ‖d i‖ * t i) := by
        rw [hind.tsum_sub hTs, tsum_ite_eq]
      _ ≤ _ := (hind.sub hTs).tsum_le_tsum hlow (Complex.hasSum_re hSf.hasSum).summable
  have hsumpos : 0 < (∑' i, f i).re := by linarith [mul_pos ha hk]
  have hnorm_original (i : ι) : ‖d i * w i‖ = M * (‖d i‖ * g i) := by
    simp only [norm_mul, g]
    field_simp [hM.ne']
  constructor
  · exact (hSn.mul_left M).congr fun i => (hnorm_original i).symm
  · intro hzero
    change ∑' i, d i * w i = 0 at hzero
    have hfzero : ∑' i, f i = 0 := by
      simp only [f, div_eq_mul_inv, tsum_mul_right, tsum_mul_left, hzero, mul_zero, zero_mul]
    simp [hfzero] at hsumpos

/-- The original log-squared sector cone follows at degree one. -/
theorem sum_bKer_ne_zero_sector_of_poly (hStir : StirlingStrip) {B Y K a δ : ℝ}
    (hB : 1 / 2 ≤ B) (hB1 : B < 1) (hY : 0 < Y) (ha : 0 < a)
    (hδ0 : 0 ≤ δ) (hδ : δ < Real.pi * (1 - B)) :
    ∃ U : ℝ, Y + 1 ≤ U ∧ ∀ τ : ℝ, |τ| ≤ Y →
      ∀ {ι : Type} (b c u : ι → ℝ) (d : ι → ℂ) (i₀ : ι),
      (∀ i, b i ∈ Icc (1 - B) B ∧ c i ∈ Icc (1 - B) B) →
      (∀ i, b i + c i = b i₀ + c i₀) → U ≤ u i₀ → (∀ i, u i₀ ≤ u i) → a ≤ ‖d i₀‖ →
      (∃ ω : ℂ, ‖ω‖ = 1 ∧ ∀ i, ∃ φ : ℝ, |φ| ≤ δ ∧
        d i = ω * (‖d i‖ : ℂ) * exp ((φ : ℂ) * I)) →
      (∀ v : ℝ, {i | u i ∈ Ico v (v + 1)}.Finite) →
      (∀ v : ℝ, 0 ≤ v →
        (∑ᶠ i ∈ {i | u i ∈ Ico v (v + 1)}, ‖d i‖) ≤ K * Real.log (v + Y + 4) ^ 2) →
      Summable (fun i => ‖d i * bKerH (b i) (c i) τ (u i)‖) ∧
        ∑' i, d i * bKerH (b i) (c i) τ (u i) ≠ 0 := by
  obtain ⟨U, hU, hpoly⟩ := sum_bKer_ne_zero_sector_poly (K := 4 * max K 0) (A := 1)
    hStir hB hB1 hY ha zero_le_one hδ0 hδ
  refine ⟨U, hU, ?_⟩
  intro τ hτ ι b c u d i₀ hbc hα hu₀ hmin hmass hsector hfin hbins
  refine hpoly τ hτ b c u d i₀ hbc hα hu₀ hmin hmass hsector hfin (fun v hv => ?_)
  calc
    _ ≤ K * Real.log (v + Y + 4) ^ 2 := hbins v hv
    _ ≤ max K 0 * Real.log (v + Y + 4) ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
    _ ≤ max K 0 * (4 * (v + Y + 4)) :=
      mul_le_mul_of_nonneg_left ((sector_helper log_sq_le_four_mul) (by linarith)) (le_max_right _ _)
    _ = _ := by rw [Real.rpow_one]; ring

#print axioms summable_shift_rpow_exp
#print axioms sum_bKer_ne_zero_sector_poly
#print axioms sum_bKer_ne_zero_sector_of_poly

end GoldbachBoundaries.PhaseCone
