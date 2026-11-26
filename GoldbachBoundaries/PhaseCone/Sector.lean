import GoldbachBoundaries.Phi2HInf.Fill.sum_bKer_ne_zero_hinf

/-! The sector form of the phase cone. -/

noncomputable section

open Complex Filter Set Topology

namespace GoldbachBoundaries.PhaseCone

open Phi2HInf

private theorem rotated_bMain_re_add_phase (b c τ u₀ u φ : ℝ) :
    ((exp ((φ : ℂ) * I) * coneRotation τ u₀) * bMain b c τ u).re =
      bAmp b c τ u * Real.cos (φ + (τ * (Real.log u - Real.log u₀) + Real.pi * (b - c) / 2)) := by
  have he : (φ : ℂ) * I + (-((τ * Real.log u₀ : ℝ) : ℂ) * I) +
      ((τ * Real.log u + Real.pi * (b - c) / 2 : ℝ) : ℂ) * I =
      ((φ + (τ * (Real.log u - Real.log u₀) + Real.pi * (b - c) / 2) : ℝ) : ℂ) * I := by
    push_cast
    ring
  unfold coneRotation bMain
  rw [mul_left_comm, ← exp_add, ← exp_add, he]
  simp [Complex.exp_re]

/-- The square-root window leaves a positive projection even after adding the coefficient phase. -/
private theorem bKer_sector_projection (hStir : StirlingStrip) {B Y δ : ℝ}
    (hB : 1 / 2 ≤ B) (hB1 : B < 1) (hY : 0 < Y)
    (hδ0 : 0 ≤ δ) (hδ : δ < Real.pi * (1 - B)) :
    ∃ U : ℝ, Y + 1 ≤ U ∧
      ∀ b ∈ Icc (1 - B) B, ∀ c ∈ Icc (1 - B) B, ∀ τ : ℝ, |τ| ≤ Y →
        ∀ u₀ u φ : ℝ, U ≤ u₀ → u₀ ≤ u → u ≤ u₀ + Real.sqrt u₀ → |φ| ≤ δ →
          Real.sin ((Real.pi * (1 - B) - δ) / 2) * ‖bKerH b c τ u‖ ≤
            ((exp ((φ : ℂ) * I) * coneRotation τ u₀) * bKerH b c τ u).re := by
  let σ := Real.pi * (1 - B) - δ
  let k := Real.sin (σ / 2)
  let k' := Real.sin (3 * σ / 4)
  have hσ : 0 < σ := sub_pos.mpr hδ
  have hσle : σ ≤ Real.pi / 2 := by
    dsimp [σ]
    nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hB)]
  have hk : 0 < k := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hkk : k < k' := Real.sin_lt_sin_of_lt_of_le_pi_div_two
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (by linarith)
  obtain ⟨C, U₁, _, hU₁, happrox⟩ := norm_bKer_asymp hStir hB hB1 hY
  refine ⟨max U₁ (max ((4 * Y / σ) ^ 2) ((1 + k) * C / (k' - k))),
    hU₁.trans (le_max_left _ _), ?_⟩
  intro b hb c hc τ hτ u₀ u φ hU hu hw hφ
  have hu₁ := (le_max_left _ _).trans hU
  have hU' := (le_max_right _ _).trans hU
  have h1 : 1 ≤ u₀ := by linarith [hU₁.trans hu₁]
  have hu0 : 0 < u := by linarith
  have hphase := phase_window_bound hY hσ hτ h1 ((le_max_left _ _).trans hU') hu hw
  have hsplit : |Real.pi * (b - c) / 2| ≤ Real.pi / 2 - Real.pi * (1 - B) := by
    rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hab : |b - c| ≤ 2 * B - 1 := abs_le.mpr
      ⟨by linarith [hb.1, hc.2], by linarith [hb.2, hc.1]⟩
    linarith [mul_le_mul_of_nonneg_left hab Real.pi_pos.le]
  let x := τ * (Real.log u - Real.log u₀)
  let y := Real.pi * (b - c) / 2
  have hangle : |φ + (x + y)| ≤ Real.pi / 2 - 3 * σ / 4 := by
    have hx : |x| ≤ σ / 4 := hphase
    have hy : |y| ≤ Real.pi / 2 - Real.pi * (1 - B) := hsplit
    dsimp [σ] at hx ⊢
    linarith [abs_add_le φ (x + y), abs_add_le x y]
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) hangle
  rw [Real.cos_abs, Real.cos_pi_div_two_sub] at hcos
  have hmain : k' * bAmp b c τ u ≤
      ((exp ((φ : ℂ) * I) * coneRotation τ u₀) * bMain b c τ u).re := by
    rw [rotated_bMain_re_add_phase, mul_comm]
    exact mul_le_mul_of_nonneg_left hcos (bAmp_pos hu0).le
  apply cone_of_relative_error (bAmp_pos hu0).le hk.le
    (by rw [norm_mul, norm_coneRotation]; simp [Complex.norm_exp])
    (norm_bMain b c τ u hu0) hmain (happrox b hb c hc τ hτ u (hu₁.trans hu))
  have hquot := ((le_max_right _ _).trans hU').trans hu
  have hreserve := (div_le_iff₀ (sub_pos.mpr hkk)).mp hquot
  rw [← mul_div_assoc]
  exact (div_le_iff₀ hu0).mpr (by simpa [mul_comm] using hreserve)

/-- The fibre summation bound for nonnegative real weights, using the same floor bins
as `Phi2Proof.D_fibre_tsum_le`. -/
private theorem fibre_tsum_le {ι : Type} (u m : ι → ℝ) (u₀ : ℝ)
    (hu : ∀ i, u₀ ≤ u i) (hm : ∀ i, 0 ≤ m i)
    (hfin : ∀ v : ℝ, {i | u i ∈ Ico v (v + 1)}.Finite)
    (W : ℕ → ℝ) (hW : ∀ n : ℕ,
      (∑ᶠ i ∈ {i | u i ∈ Ico (u₀ + n) (u₀ + n + 1)}, m i) ≤ W n)
    (h : ι → ℝ) (ψ : ℕ → ℝ) (hh : ∀ i, 0 ≤ h i) (hψ : ∀ n, 0 ≤ ψ n)
    (hle : ∀ i, h i ≤ ψ ⌊u i - u₀⌋₊) (hWψ : Summable fun n => W n * ψ n) :
    Summable (fun i => m i * h i) ∧ ∑' i, m i * h i ≤ ∑' n, W n * ψ n := by
  classical
  let s (n : ℕ) : Set ι := {i | u i ∈ Ico (u₀ + n) (u₀ + n + 1)}
  have hmem (i : ι) (n : ℕ) : i ∈ s n ↔ ⌊u i - u₀⌋₊ = n := by
    rw [Nat.floor_eq_iff (sub_nonneg.mpr (hu i))]
    change (u₀ + n ≤ u i ∧ u i < u₀ + n + 1) ↔
      ((n : ℝ) ≤ u i - u₀ ∧ u i - u₀ < n + 1)
    constructor <;> intro hi <;> constructor <;> linarith [hi.1, hi.2]
  have hpart (i : ι) : ∃! n, i ∈ s n :=
    ⟨⌊u i - u₀⌋₊, (hmem i _).mpr rfl, fun n hn => ((hmem i n).mp hn).symm⟩
  have hfinite (n : ℕ) : (s n).Finite := hfin (u₀ + n)
  have hnonneg (i : ι) : 0 ≤ m i * h i := mul_nonneg (hm i) (hh i)
  have hbin (n : ℕ) : (∑' i : s n, m i * h i) ≤ W n * ψ n := by
    let _ := (hfinite n).fintype
    rw [tsum_fintype, ← Finset.sum_subtype (hfinite n).toFinset
      (fun i => (hfinite n).mem_toFinset) (fun i => m i * h i)]
    calc
      _ ≤ ∑ i ∈ (hfinite n).toFinset, m i * ψ n := by
        refine Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left ?_ (hm i)
        simpa only [(hmem i n).mp ((hfinite n).mem_toFinset.mp hi)] using hle i
      _ = (∑ᶠ i ∈ s n, m i) * ψ n := by
        rw [finsum_mem_eq_finite_toFinset_sum _ (hfinite n), Finset.sum_mul]
      _ ≤ W n * ψ n := mul_le_mul_of_nonneg_right (hW n) (hψ n)
  have hbins := Summable.of_nonneg_of_le (fun n => tsum_nonneg fun i : s n => hnonneg i)
    hbin hWψ
  have hsub (n : ℕ) : Summable fun i : s n => m i * h i := by
    let _ := (hfinite n).fintype
    exact Summable.of_finite
  have hs := (summable_partition hnonneg hpart).mpr ⟨hsub, hbins⟩
  refine ⟨hs, ?_⟩
  rw [← (Set.sigmaEquiv s hpart).tsum_eq (fun i => m i * h i)]
  exact (((Set.sigmaEquiv s hpart).summable_iff.mpr hs).tsum_sigma' hsub).le.trans
    (hbins.tsum_le_tsum hbin hWψ)

private theorem log_sq_le_four_mul {x : ℝ} (hx : 1 ≤ x) : Real.log x ^ 2 ≤ 4 * x := by
  have h := Real.log_le_rpow_div (x := x) (by linarith) (by norm_num : (0 : ℝ) < 1 / 2)
  rw [← Real.sqrt_eq_rpow] at h
  calc
    Real.log x ^ 2 ≤ (2 * Real.sqrt x) ^ 2 :=
      pow_le_pow_left₀ (Real.log_nonneg hx) (by linarith) 2
    _ = 4 * x := by rw [mul_pow, Real.sq_sqrt (by linarith)]; ring

set_option maxHeartbeats 600000 in
/-- The Gamma-product series converges absolutely and is nonzero
when the coefficients share a sector with half-angle strictly below `π (1 - B)`. -/
theorem sum_bKer_ne_zero_sector (hStir : StirlingStrip) {B Y K a δ : ℝ}
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
  classical
  obtain ⟨Uc, hUc, hcone⟩ := bKer_sector_projection hStir hB hB1 hY hδ0 hδ
  obtain ⟨D, Ud, hD, _, hdecay⟩ := norm_bKer_ratio_le hStir hB hB1 hY
  let k := Real.sin ((Real.pi * (1 - B) - δ) / 2)
  have hk : 0 < k := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith
    · nlinarith [Real.pi_pos, mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hB)]
  let K' := max K 0
  have hK' : 0 ≤ K' := le_max_right _ _
  -- Choose the cutoff for the tail independently of the family.
  let A (n : ℕ) := 4 * K' * D * (Y + 6) * ((2 + n) ^ 3 * Real.exp (-Real.pi * n))
  have hA0 (n : ℕ) : 0 ≤ A n := by dsimp [A]; positivity
  have hAs : Summable A := (summable_cube_exp 2).mul_left (4 * K' * D * (Y + 6))
  obtain ⟨N, hN⟩ := ((tendsto_order.1 (tendsto_sum_nat_add A)).2
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
  let W (n : ℕ) := 4 * K' * (u₀ + n + Y + 4)
  have hW (n : ℕ) :
      (∑ᶠ i ∈ {i | u i ∈ Ico (u₀ + n) (u₀ + n + 1)}, ‖d i‖) ≤ W n := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    refine (hBins (u₀ + n) (by linarith)).trans ?_
    calc
      _ ≤ K' * Real.log (u₀ + n + Y + 4) ^ 2 :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
      _ ≤ K' * (4 * (u₀ + n + Y + 4)) :=
        mul_le_mul_of_nonneg_left (log_sq_le_four_mul (by linarith)) hK'
      _ = W n := by dsimp [W]; ring
  have hsumW : Summable fun n => W n * ψ n := by
    refine Summable.of_nonneg_of_le (fun n => by dsimp [W, ψ]; positivity) (fun n => ?_)
      ((summable_cube_exp (u₀ + Y + 4)).mul_left (4 * K' * D))
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hbase : 1 ≤ u₀ + Y + 4 + n := by linarith
    have hsmall : 2 + (n : ℝ) ≤ u₀ + Y + 4 + n := by linarith
    have hprod : (u₀ + n + Y + 4) * (2 + n) ≤ (u₀ + Y + 4 + n) ^ 3 := by
      have hh := mul_le_mul_of_nonneg_left hsmall (by linarith : 0 ≤ u₀ + n + Y + 4)
      nlinarith only [hh, mul_nonneg (sq_nonneg (u₀ + Y + 4 + n)) (sub_nonneg.mpr hbase)]
    have hh := mul_le_mul_of_nonneg_left hprod
      (by positivity : 0 ≤ 4 * K' * D * Real.exp (-Real.pi * n))
    dsimp [W, ψ]
    nlinarith only [hh]
  obtain ⟨hSn, _⟩ := fibre_tsum_le u (fun i => ‖d i‖) u₀ hmin
    (fun i => norm_nonneg _) hfin W hW g ψ hg hψ hgle hsumW
  -- Only bins with n + 1 > √u₀ can meet the tail. Those bins also satisfy n ≥ N.
  let r := Real.sqrt u₀
  let t (i : ι) := if u i ≤ u₀ + r then 0 else g i
  let ψT (n : ℕ) := if (n : ℝ) + 1 ≤ r then 0 else ψ n
  let AN (n : ℕ) := if N ≤ n then A n else 0
  have hAN0 (n : ℕ) : 0 ≤ AN n := by dsimp [AN]; split_ifs <;> simp [hA0 n]
  have hANs : Summable AN := Summable.of_nonneg_of_le hAN0
    (fun n => by dsimp [AN]; split_ifs <;> simp [hA0 n]) hAs
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
      have hh := mul_le_mul_of_nonneg_left hpoly
        (by positivity : 0 ≤ 4 * K' * D * (2 + n) * Real.exp (-Real.pi * n))
      simp only [W, ψT, ite_eq_right hn, ψ, AN, ite_eq_left hNn, A]
      nlinarith only [hh]
  have hψT0 (n : ℕ) : 0 ≤ ψT n := by dsimp [ψT]; split_ifs <;> simp [hψ n]
  have hWψs : Summable fun n => W n * ψT n :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (by dsimp [W]; positivity) (hψT0 n)) hWψ hANs
  have htψ (i : ι) : t i ≤ ψT ⌊u i - u₀⌋₊ := by
    by_cases hi : u i ≤ u₀ + r
    · simpa [t, hi] using hψT0 ⌊u i - u₀⌋₊
    · have hceil := Nat.lt_floor_add_one (u i - u₀)
      have hn : ¬ (⌊u i - u₀⌋₊ : ℝ) + 1 ≤ r := by
        intro hn
        exact hi (by linarith)
      simpa [t, hi, ψT, hn] using hgle i
  obtain ⟨hTs, hTle⟩ := fibre_tsum_le u (fun i => ‖d i‖) u₀ hmin (fun i => norm_nonneg _) hfin
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

/-- The integer-weight H∞ cone, recovered by taking the coefficient phase to be zero. -/
theorem sum_bKer_ne_zero_hinf_of_sector (hStir : StirlingStrip) {B Y K : ℝ}
    (hB : 1 / 2 ≤ B) (hB1 : B < 1) (hY : 0 < Y) :
    ∃ U : ℝ, Y + 1 ≤ U ∧ ∀ τ : ℝ, |τ| ≤ Y →
      ∀ {ι : Type} (b c u : ι → ℝ) (q : ι → ℕ) (i₀ : ι),
      (∀ i, b i ∈ Icc (1 - B) B ∧ c i ∈ Icc (1 - B) B) →
      (∀ i, b i + c i = b i₀ + c i₀) → U ≤ u i₀ → (∀ i, u i₀ ≤ u i) → 1 ≤ q i₀ →
      (∀ v : ℝ, {i | u i ∈ Ico v (v + 1)}.Finite) →
      (∀ v : ℝ, 0 ≤ v →
        (∑ᶠ i ∈ {i | u i ∈ Ico v (v + 1)}, (q i : ℝ)) ≤ K * Real.log (v + Y + 4) ^ 2) →
      Summable (fun i => ‖(q i : ℂ) * bKerH (b i) (c i) τ (u i)‖) ∧
        ∑' i, (q i : ℂ) * bKerH (b i) (c i) τ (u i) ≠ 0 := by
  obtain ⟨U, hU, hsector⟩ := sum_bKer_ne_zero_sector (K := K) (a := 1) (δ := 0)
    hStir hB hB1 hY zero_lt_one le_rfl (mul_pos Real.pi_pos (sub_pos.mpr hB1))
  refine ⟨U, hU, ?_⟩
  intro τ hτ ι b c u q i₀ hbc hα hu₀ hmin hq hfin hBins
  refine hsector τ hτ b c u (fun i => (q i : ℂ)) i₀ hbc hα hu₀ hmin ?_ ?_ hfin ?_
  · simpa using (show (1 : ℝ) ≤ (q i₀ : ℝ) by exact_mod_cast hq)
  · exact ⟨1, norm_one, fun i => ⟨0, by simp, by simp⟩⟩
  · simpa using hBins

#print axioms sum_bKer_ne_zero_sector
#print axioms sum_bKer_ne_zero_hinf_of_sector

end GoldbachBoundaries.PhaseCone
