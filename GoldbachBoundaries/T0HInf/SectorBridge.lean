import GoldbachBoundaries.PhaseCone.SectorPoly
import GoldbachBoundaries.T0HInf.FilteredKernel
import GoldbachBoundaries.Phi2HInf.Fill.collision_family

/-! The filtered atoms follow from the sector cone at the original collision heights. -/
noncomputable section
open Complex Filter Topology Set
namespace GoldbachBoundaries.T0HInf
open GoldbachBoundaries Paper2
open _root_.GoldbachBoundaries.Phi2HInf
  (StirlingStrip bKerH collisionIdx criticalPairIdx criticalVal
    orientCollision swapCollision oriented_family_bins)

theorem pair_family_ne_zero_of_large_of_sector (hZ1 : Z1) (hZ2 : Z2) (hStir : StirlingStrip)
    {B Y : ℝ} (hB : 1 / 2 ≤ B) (hB1 : B < 1) (hY : 0 < Y) :
    ∃ X : ℝ, Y < X ∧ ∀ s : ℂ, |s.im| ≤ Y →
      ∀ {ι : Type} (p : ι → collisionIdx s), Function.Injective p → Nonempty ι →
      (∀ i, ((p i).1.1 : ℂ).re ∈ Icc (1 - B) B ∧ ((p i).1.2 : ℂ).re ∈ Icc (1 - B) B) →
      (∀ i, X < |((p i).1.1 : ℂ).im| ∧ X < |((p i).1.2 : ℂ).im|) →
      (∑' i, zeroCoef (p i).1.1 * zeroCoef (p i).1.2) ≠ 0 := by
  classical
  obtain ⟨K, hK⟩ := oriented_family_bins hZ1 hZ2 hY
  let δ := Real.pi * (1 - B) / 2
  have hδ : 0 < δ := div_pos (mul_pos Real.pi_pos (sub_pos.mpr hB1)) (by norm_num)
  let D : ℝ := 2 * (Y + 1)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  obtain ⟨U, hUY, hU⟩ := PhaseCone.sum_bKer_ne_zero_sector_poly
    (K := (1 + D) * max K 0) (a := 1) (δ := δ) (A := 4)
    hStir hB hB1 hY zero_lt_one (by norm_num) hδ.le (by dsimp [δ] at *; linarith)
  have harg : ContinuousAt Complex.arg (1 : ℂ) :=
    Complex.continuousAt_arg (by simp [Complex.mem_slitPlane_iff])
  obtain ⟨ε, hε, hargε⟩ := Metric.continuousAt_iff.mp harg δ hδ
  let X := max U (max (D + 2) (D / ε + 1))
  have hUX : U ≤ X := le_max_left _ _
  have hYX : Y < X := by linarith [hUY.trans hUX]
  refine ⟨X, hYX, ?_⟩
  intro s hs ι p hp hne hbc hlarge
  let o (i : ι) := orientCollision (p i)
  let b (i : ι) := ((o i).1.1 : ℂ).re
  let c (i : ι) := ((o i).1.2 : ℂ).re
  let u (i : ι) := -((o i).1.2 : ℂ).im
  let q (i : ι) := zetaMult (p i).1.1 * zetaMult (p i).1.2
  obtain ⟨hfin, hbin⟩ := hK s hs p hp
  let F (i : ι) := filterFactor (b i) (c i) s.im (u i)
  let d (i : ι) := (q i : ℂ) * F i
  have hbig (i : ι) : X < u i := by
    have him : ((p i).1.1 : ℂ).im + ((p i).1.2 : ℂ).im = s.im := by
      simpa only [add_im] using congrArg Complex.im (p i).2
    have hhi := hlarge i
    dsimp [u, o, orientCollision]
    split_ifs with hneg
    · simpa only [abs_of_neg hneg] using hhi.2
    · have hpos : 0 ≤ ((p i).1.2 : ℂ).im := le_of_not_gt hneg
      rw [abs_of_nonneg hpos] at hhi
      have hleft : ((p i).1.1 : ℂ).im < 0 := by linarith [le_abs_self s.im]
      simpa only [swapCollision, Prod.swap, abs_of_neg hleft] using hhi.1
  have hbc' (i : ι) : b i ∈ Icc (1 - B) B ∧ c i ∈ Icc (1 - B) B := by
    dsimp [b, c, o, orientCollision]
    split_ifs
    · exact hbc i
    · exact ⟨(hbc i).2, (hbc i).1⟩
  have hsumre (i : ι) : b i + c i = s.re := by
    simpa only [b, c, add_re] using congrArg Complex.re (o i).2
  obtain ⟨i₁⟩ := hne
  let S := {i : ι | u i ≤ u i₁}
  have hSfin : S.Finite := by
    refine (Set.Finite.biUnion (Finset.range (⌊u i₁⌋₊ + 1)).finite_toSet
      (fun k _ => hfin (k : ℝ))).subset ?_
    intro i hi
    have hui : 0 ≤ u i := by linarith [hbig i]
    simp only [Set.mem_iUnion, Finset.coe_range, Set.mem_Iio, Set.mem_ofPred_eq]
    exact ⟨⌊u i⌋₊, Nat.lt_succ_of_le (Nat.floor_le_floor hi),
      Nat.floor_le hui, Nat.lt_floor_add_one _⟩
  obtain ⟨i₀, hi₀S, hi₀⟩ := hSfin.toFinset.exists_min_image u ⟨i₁, by simp [S]⟩
  have hmin (i : ι) : u i₀ ≤ u i := by
    by_cases hi : i ∈ S
    · exact hi₀ i (hSfin.mem_toFinset.mpr hi)
    · have h1 : u i₁ < u i := not_le.mp hi
      have h2 : u i₀ ≤ u i₁ := hSfin.mem_toFinset.mp hi₀S
      exact h2.trans h1.le
  have hmult {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) : 1 ≤ zetaMult ρ :=
    one_le_zetaMult_of_zero (fun h => by
      have hh := hρ.2.2
      rw [h, Complex.one_re] at hh
      exact lt_irrefl _ hh) hρ.1
  have hq : 1 ≤ q i₀ := by
    have h1 := hmult (p i₀).1.1.2
    have h2 := hmult (p i₀).1.2.2
    dsimp [q]
    nlinarith
  have hu1 (i : ι) : 1 ≤ u i := by linarith [hUY.trans hUX, hbig i]
  have herror (i : ι) : ‖F i - (u i : ℂ) ^ 2‖ ≤ D * u i := by
    have ⟨hb, hc⟩ := hbc' i
    exact filterFactor_error
      ⟨by linarith [hb.1], hb.2.trans hB1.le⟩
      ⟨by linarith [hc.1], hc.2.trans hB1.le⟩ hY hs (hu1 i)
  have hnormSq (i : ι) : ‖(u i : ℂ) ^ 2‖ = u i ^ 2 := by
    rw [Complex.norm_pow, Complex.norm_real, Real.norm_of_nonneg (by linarith [hu1 i])]
  have hnorm (i : ι) : ‖d i‖ = (q i : ℝ) * ‖F i‖ := by
    simp [d]
  have hmass : 1 ≤ ‖d i₀‖ := by
    have hlu : D + 2 ≤ u i₀ :=
      (le_max_left (D + 2) (D / ε + 1)).trans ((le_max_right U _).trans (hbig i₀).le)
    have h := norm_le_norm_sub_add ((u i₀ : ℂ) ^ 2) (F i₀)
    rw [norm_sub_rev, hnormSq] at h
    have hF₀ : 1 ≤ ‖F i₀‖ := by
      nlinarith only [h, herror i₀, hu1 i₀,
        mul_nonneg (by linarith [hu1 i₀] : 0 ≤ u i₀) (sub_nonneg.mpr hlu)]
    rw [hnorm]
    exact one_le_mul_of_one_le_of_one_le (by exact_mod_cast hq) hF₀
  have hsector : ∃ ω : ℂ, ‖ω‖ = 1 ∧ ∀ i, ∃ φ : ℝ, |φ| ≤ δ ∧
      d i = ω * (‖d i‖ : ℂ) * exp ((φ : ℂ) * I) := by
    refine ⟨1, norm_one, fun i => ?_⟩
    let z := F i / (u i : ℂ) ^ 2
    have hu : 0 < u i := by linarith [hu1 i]
    have huC : (u i : ℂ) ^ 2 ≠ 0 := pow_ne_zero _ (by exact_mod_cast hu.ne')
    have hnear : dist z 1 < ε := by
      rw [dist_eq_norm]
      change ‖F i / (u i : ℂ) ^ 2 - 1‖ < ε
      rw [div_sub_one huC, norm_div, hnormSq, div_lt_iff₀ (sq_pos_of_pos hu)]
      have hlarge' : D / ε < u i := by
        have hh := (le_max_right (D + 2) (D / ε + 1)).trans (le_max_right U _)
        linarith [hh.trans_lt (hbig i)]
      exact (herror i).trans_lt (by
        have hh := (div_lt_iff₀ hε).mp hlarge'
        nlinarith only [mul_lt_mul_of_pos_right hh hu])
    have hphase : |z.arg| < δ := by
      simpa [Real.dist_eq] using hargε hnear
    have hd : d i = ((q i : ℝ) * u i ^ 2 : ℝ) * z := by
      push_cast
      change (q i : ℂ) * F i = (q i : ℂ) * (u i : ℂ) ^ 2 * (F i / (u i : ℂ) ^ 2)
      rw [mul_assoc, mul_comm ((u i : ℂ) ^ 2), div_mul_cancel₀ _ huC]
    refine ⟨z.arg, hphase.le, ?_⟩
    calc
      d i = ((q i : ℝ) * u i ^ 2 : ℝ) * z := hd
      _ = ((q i : ℝ) * u i ^ 2 : ℝ) * ((‖z‖ : ℂ) * exp ((z.arg : ℂ) * I)) := by
        rw [Complex.norm_mul_exp_arg_mul_I]
      _ = _ := by
        rw [one_mul, hd, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        push_cast
        ring
  have hbins (v : ℝ) (hv : 0 ≤ v) :
      (∑ᶠ i ∈ {i | u i ∈ Ico v (v + 1)}, ‖d i‖) ≤
        ((1 + D) * max K 0) * (v + Y + 4) ^ (4 : ℝ) := by
    let x := v + Y + 4
    have hx : 1 ≤ x := by dsimp [x]; linarith
    have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx
    have hlog : Real.log x ≤ x := Real.log_le_self (zero_le_one.trans hx)
    rw [finsum_mem_eq_finite_toFinset_sum _ (hfin v)]
    calc
      _ ≤ ∑ i ∈ (hfin v).toFinset, ((1 + D) * x ^ 2) * (q i : ℝ) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : u i ∈ Ico v (v + 1) := (hfin v).mem_toFinset.mp hi
        have hux : u i ≤ x := by dsimp [x]; linarith [hi'.2]
        have hnormF := norm_le_norm_sub_add (F i) ((u i : ℂ) ^ 2)
        rw [hnormSq] at hnormF
        have hF : ‖F i‖ ≤ (1 + D) * x ^ 2 := calc
          _ ≤ D * u i + u i ^ 2 := by linarith only [hnormF, herror i]
          _ ≤ (1 + D) * u i ^ 2 := by
            have hui : 0 ≤ u i := by linarith [hu1 i]
            nlinarith only [mul_nonneg (mul_nonneg hD hui) (sub_nonneg.mpr (hu1 i))]
          _ ≤ (1 + D) * x ^ 2 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith [hu1 i]) hux 2) (by positivity)
        rw [hnorm, mul_comm (↑(q i) : ℝ)]
        exact mul_le_mul_of_nonneg_right hF (Nat.cast_nonneg _)
      _ = ((1 + D) * x ^ 2) * ∑ᶠ i ∈ {i | u i ∈ Ico v (v + 1)}, (q i : ℝ) := by
        rw [finsum_mem_eq_finite_toFinset_sum _ (hfin v), Finset.mul_sum]
      _ ≤ ((1 + D) * x ^ 2) * (max K 0 * x ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        refine (hbin v hv).trans ((mul_le_mul_of_nonneg_right (le_max_left K 0) (sq_nonneg _)).trans ?_)
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog0 hlog 2) (le_max_right K 0)
      _ = _ := by
        change _ = _ * x ^ (4 : ℝ)
        rw [show x ^ (4 : ℝ) = x ^ (4 : ℕ) from Real.rpow_natCast x 4]
        ring
  have hnonzero := (hU s.im hs b c u d i₀ hbc'
    (fun i => (hsumre i).trans (hsumre i₀).symm) (hUX.trans (hbig i₀).le)
    hmin hmass hsector hfin hbins).2
  have hterm (i : ι) : zeroCoef (p i).1.1 * zeroCoef (p i).1.2 =
      d i * bKerH (b i) (c i) s.im (u i) := by
    have him : ((o i).1.1 : ℂ).im + ((o i).1.2 : ℂ).im = s.im := by
      simpa only [add_im] using congrArg Complex.im (o i).2
    have hfirst : (b i : ℂ) + ((u i + s.im : ℝ) : ℂ) * I = (o i).1.1 := by
      apply Complex.ext <;> simp [b, u] <;> linarith
    have hsecond : (c i : ℂ) - (u i : ℂ) * I = (o i).1.2 := by
      apply Complex.ext <;> simp [c, u]
    unfold d F
    rw [bKerH, filterFactor, hfirst, hsecond]
    dsimp [q, o, orientCollision]
    split_ifs <;> simp only [swapCollision, Prod.swap, zeroCoef, Phi2Proof.zeroCoef, Nat.cast_mul] <;> ring
  simpa only [← hterm] using hnonzero

theorem collisionAtom_ne_zero_of_large_of_sector (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2)
    (hStir : StirlingStrip) {Y : ℝ} (hY : 0 < Y) :
    ∃ X : ℝ, Y < X ∧ ∀ s : ℂ, |s.im| ≤ Y → Nonempty (collisionIdx s) →
      (∀ p : collisionIdx s, X < |(p.1.1 : ℂ).im| ∧ X < |(p.1.2 : ℂ).im|) →
      collisionAtom s ≠ 0 := by
  have hB : 1 / 2 ≤ Bsup := (lem_B_i hZ1).1.trans (lem_B_i hZ1).2.1
  obtain ⟨X, hXY, hX⟩ := pair_family_ne_zero_of_large_of_sector hZ1 hZ2 hStir hB (lem_B_iii hH) hY
  refine ⟨X, hXY, ?_⟩
  intro s hs hne hlarge
  have hstrip (ρ : NontrivialZeros) : (ρ : ℂ).re ∈ Icc (1 - Bsup) Bsup := by
    refine ⟨?_, M1.re_le_Bsup ρ.2⟩
    have hr := M1.re_le_Bsup ((hZ1 ρ ρ.2).2.1)
    simp only [sub_re, one_re, conj_re] at hr
    linarith
  exact hX s hs id Function.injective_id hne
    (fun p => ⟨hstrip p.1.1, hstrip p.1.2⟩) hlarge

theorem criticalAtom_ne_zero_of_large_of_sector (hZ1 : Z1) (hZ2 : Z2) (hStir : StirlingStrip)
    {Y : ℝ} (hY : 0 < Y) : ∃ X : ℝ, Y < X ∧
      ∀ τ : ℝ, |τ| ≤ Y → Nonempty (criticalPairIdx τ) →
        (∀ p : criticalPairIdx τ,
          X < |(criticalVal p.1.1).im| ∧ X < |(criticalVal p.1.2).im|) → criticalAtom τ ≠ 0 := by
  obtain ⟨X, hXY, hX⟩ := pair_family_ne_zero_of_large_of_sector hZ1 hZ2 hStir
    (B := 1 / 2) le_rfl (by norm_num) hY
  refine ⟨X, hXY, ?_⟩
  intro τ hτ hne hlarge
  let f : criticalPairIdx τ → collisionIdx (1 + (τ : ℂ) * I) :=
    fun p => ⟨(p.1.1.1, p.1.2.1), p.2⟩
  have hf : Function.Injective f := by
    intro p q h
    have hv := congrArg (fun r : collisionIdx (1 + (τ : ℂ) * I) => r.1) h
    apply Subtype.ext
    exact Prod.ext (Subtype.ext (congrArg Prod.fst hv)) (Subtype.ext (congrArg Prod.snd hv))
  apply hX (1 + (τ : ℂ) * I) (by simpa using hτ) f hf hne _ hlarge
  intro p
  change (criticalVal p.1.1).re ∈ Icc (1 - 1 / 2) (1 / 2) ∧
    (criticalVal p.1.2).re ∈ Icc (1 - 1 / 2) (1 / 2)
  rw [show (criticalVal p.1.1).re = 1 / 2 from p.1.1.2,
    show (criticalVal p.1.2).re = 1 / 2 from p.1.2.2]
  norm_num

#print axioms pair_family_ne_zero_of_large_of_sector
#print axioms collisionAtom_ne_zero_of_large_of_sector
#print axioms criticalAtom_ne_zero_of_large_of_sector

end GoldbachBoundaries.T0HInf
