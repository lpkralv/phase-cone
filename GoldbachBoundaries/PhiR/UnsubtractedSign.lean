import GoldbachBoundaries.PhiR.UnsubtractedRealLimit
import GoldbachBoundaries.Paper2.M1.Fill.sum_zetaMult_window_le
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # The sign of the unsubtracted real-point limit -/

noncomputable section

open Filter Set Topology ComplexConjugate

namespace GoldbachBoundaries.PhiRProof

open GoldbachBoundaries.Paper2 GoldbachBoundaries.Phi2Proof

/-- Every nontrivial zero has absolute ordinate greater than 14. -/
def H14 : Prop := ∀ ρ : NontrivialZeros, 14 < |(ρ : ℂ).im|

/-- For real heights at least 14, the positive-ordinate zero count with multiplicities is
at most the square of the height divided by eight. -/
def HN : Prop := ∀ T : ℝ, 14 ≤ T → Nzero T ≤ T ^ 2 / 8

/-- The contribution of a distinct zero to the mass at ordinate zero. -/
def zeroWeight (ρ : ℂ) : ℝ :=
  Real.pi * (zetaMult ρ : ℝ) ^ 2 / Real.cosh (Real.pi * ρ.im)

theorem zeroWeight_nonneg (ρ : ℂ) : 0 ≤ zeroWeight ρ := by
  unfold zeroWeight
  positivity

private theorem zeroWeight_conj {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) :
    zeroWeight (conj ρ) = zeroWeight ρ := by
  rw [zeroWeight, zeroWeight, zetaMult_conj hρ, Complex.conj_im, mul_neg, Real.cosh_neg]

private theorem zeroWeight_le {ρ : ℂ} {t : ℝ} (ht : t ≤ ρ.im) :
    zeroWeight ρ ≤ (2 * Real.pi * Real.exp (-Real.pi * t)) * (zetaMult ρ : ℝ) ^ 2 := by
  have hcosh : Real.exp (Real.pi * t) / 2 ≤ Real.cosh (Real.pi * ρ.im) := by
    rw [Real.cosh_eq]
    linarith [Real.exp_pos (-(Real.pi * ρ.im)),
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht Real.pi_pos.le)]
  unfold zeroWeight
  calc
    _ ≤ Real.pi * (zetaMult ρ : ℝ) ^ 2 / (Real.exp (Real.pi * t) / 2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hcosh
    _ = _ := by rw [neg_mul, Real.exp_neg]; ring

/-- The nontrivial zeros with positive imaginary part. -/
def positiveZeros : Set NontrivialZeros := {ρ | 0 < (ρ : ℂ).im}

private def positiveShell (n : ℕ) : Set positiveZeros :=
  {ρ | 14 + (n : ℝ) ≤ (ρ.1 : ℂ).im ∧ (ρ.1 : ℂ).im < 15 + (n : ℝ)}

private theorem existsUnique_nat_interval {x : ℝ} (hx : 0 ≤ x) :
    ∃! n : ℕ, (n : ℝ) ≤ x ∧ x < (n : ℝ) + 1 := by
  let n := ⌊x⌋₊
  have hlo : (n : ℝ) ≤ x := Nat.floor_le hx
  have hhi : x < (n : ℝ) + 1 := Nat.lt_floor_add_one _
  refine ⟨n, ⟨hlo, hhi⟩, fun m hm => ?_⟩
  have hmn : m < n + 1 := by exact_mod_cast (show (m : ℝ) < (n : ℝ) + 1 by linarith [hm.1])
  have hnm : n < m + 1 := by exact_mod_cast (show (n : ℝ) < (m : ℝ) + 1 by linarith [hm.2])
  omega

private theorem positiveShell_partition (h14 : H14) (ρ : positiveZeros) :
    ∃! n, ρ ∈ positiveShell n := by
  have hpos : 0 < (ρ.1 : ℂ).im := ρ.2
  have h14' : 14 < (ρ.1 : ℂ).im := by simpa only [abs_of_pos hpos] using h14 ρ.1
  refine (existsUnique_congr ?_).mp (existsUnique_nat_interval (x := (ρ.1 : ℂ).im - 14)
    (by linarith))
  intro n
  change _ ↔ (14 + (n : ℝ) ≤ (ρ.1 : ℂ).im ∧ (ρ.1 : ℂ).im < 15 + (n : ℝ))
  constructor <;> rintro ⟨ha, hb⟩ <;> exact ⟨by linarith, by linarith⟩

private def shellEmbedding (n : ℕ) :
    positiveShell n ↪ {ρ : ℂ | ρ ∈ NontrivialZeros ∧ 0 < ρ.im ∧ ρ.im ≤ 15 + (n : ℝ)} where
  toFun ρ := ⟨(ρ.1.1 : ℂ), ρ.1.1.2, ρ.1.2, ρ.2.2.le⟩
  inj' := by
    intro ρ σ h
    have hval := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext (Subtype.ext hval))

private instance (n : ℕ) : Fintype (positiveShell n) :=
  letI := (M1.finite_zeros_im_pos_le (15 + (n : ℝ))).fintype
  Fintype.ofInjective (shellEmbedding n) (shellEmbedding n).injective

private def shellBound (n : ℕ) : ℝ :=
  2 * Real.pi / 64 * (15 + (n : ℝ)) ^ 4 * Real.exp (-Real.pi * (14 + (n : ℝ)))

private theorem positiveShell_bound (hN : HN) (n : ℕ) :
    ∑' ρ : positiveShell n, zeroWeight (ρ.1.1 : ℂ) ≤ shellBound n := by
  classical
  let f := M1.finite_zeros_im_pos_le (15 + (n : ℝ))
  let m (ρ : positiveShell n) : ℝ := zetaMult (ρ.1.1 : ℂ)
  have hsum : ∑ ρ, m ρ ≤ (15 + (n : ℝ)) ^ 2 / 8 := by
    refine le_trans ?_ (hN _ (by linarith [Nat.cast_nonneg (α := ℝ) n]))
    unfold Nzero
    rw [finsum_mem_eq_finite_toFinset_sum _ f]
    refine Finset.sum_le_sum_of_injOn (fun ρ => (ρ.1.1 : ℂ)) ?_ ?_ (fun _ _ => le_rfl)
      (fun _ _ _ => by positivity)
    · intro ρ _ σ _ h
      exact (shellEmbedding n).injective (Subtype.ext h)
    · intro ρ hρ
      obtain ⟨σ, -, rfl⟩ := Finset.mem_image.mp hρ
      exact f.mem_toFinset.mpr (shellEmbedding n σ).2
  calc
    _ = ∑ ρ : positiveShell n, zeroWeight (ρ.1.1 : ℂ) := tsum_fintype _
    _ ≤ ∑ ρ : positiveShell n, (2 * Real.pi * Real.exp (-Real.pi * (14 + (n : ℝ)))) *
        (m ρ) ^ 2 := Finset.sum_le_sum fun ρ _ => zeroWeight_le ρ.2.1
    _ = (2 * Real.pi * Real.exp (-Real.pi * (14 + (n : ℝ)))) * ∑ ρ, (m ρ) ^ 2 :=
      (Finset.mul_sum ..).symm
    _ ≤ (2 * Real.pi * Real.exp (-Real.pi * (14 + (n : ℝ)))) *
        ((15 + (n : ℝ)) ^ 2 / 8) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => by exact Nat.cast_nonneg _)).trans
        (pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _) hsum 2)
    _ = shellBound n := by unfold shellBound; ring

private theorem exp_neg_fourteen_pi_lt : Real.exp (-Real.pi * 14) < 8e-20 := by
  have hsmall : (2.66 : ℝ) ≤ Real.exp 0.98 := by
    refine le_trans ?_ (Real.sum_le_exp_of_nonneg (x := 0.98) (by norm_num) 6)
    norm_num [Finset.sum_range_succ]
  have hexp : (12500000000000000000 : ℝ) < Real.exp (Real.pi * 14) := calc
    _ < (2.7182818283 : ℝ) ^ 43 * 2.66 := by norm_num
    _ ≤ (Real.exp 1) ^ 43 * Real.exp 0.98 :=
      mul_le_mul (pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 43) hsmall
        (by norm_num) (by positivity)
    _ = Real.exp ((43 : ℕ) * 1 + 0.98) := by rw [Real.exp_add, Real.exp_nat_mul]
    _ ≤ _ := Real.exp_le_exp.mpr (by norm_num; linarith [Real.pi_gt_d4])
  rw [neg_mul, Real.exp_neg, ← one_div, div_lt_iff₀ (Real.exp_pos _)]
  linarith only [mul_lt_mul_of_pos_right hexp (by norm_num : (0 : ℝ) < 8e-20)]

private theorem shell_ratio_le : (16 / 15 : ℝ) ^ 4 * Real.exp (-Real.pi) ≤ 0.06 := by
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  have hsmall : (1.1 : ℝ) ≤ Real.exp 0.1 := by
    convert Real.add_one_le_exp (0.1 : ℝ) using 1
    norm_num
  have h : (2.7182818283 : ℝ) ^ 3 * 1.1 ≤ Real.exp Real.pi := calc
    _ ≤ (Real.exp 1) ^ 3 * Real.exp 0.1 :=
      mul_le_mul (pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 3) hsmall
        (by norm_num) (by positivity)
    _ = Real.exp ((3 : ℕ) * 1 + 0.1) := by rw [Real.exp_add, Real.exp_nat_mul]
    _ ≤ _ := Real.exp_le_exp.mpr (by norm_num; linarith [Real.pi_gt_d2])
  exact (by norm_num : (16 / 15 : ℝ) ^ 4 ≤ 0.06 * ((2.7182818283 : ℝ) ^ 3 * 1.1)).trans
    (mul_le_mul_of_nonneg_left h (by norm_num))

private theorem log_two_pi_gt : (1.8 : ℝ) < Real.log (2 * Real.pi) := by
  apply (Real.lt_log_iff_exp_lt (by positivity)).mpr
  have hsmall : (1.2 : ℝ) ≤ Real.exp 0.2 := by
    convert Real.add_one_le_exp (0.2 : ℝ) using 1
    norm_num
  have h : Real.exp 1.8 * 1.2 ≤ Real.exp 1 ^ 2 := calc
    _ ≤ Real.exp 1.8 * Real.exp 0.2 := mul_le_mul_of_nonneg_left hsmall (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add, ← Real.exp_nat_mul]; norm_num
  have hsq := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 2
  linarith [h.trans hsq, Real.pi_gt_d2]

private theorem shellBound_succ_le {k n : ℕ} (hkn : k ≤ n) :
    shellBound (n + 1) ≤
      ((16 + (k : ℝ)) / (15 + (k : ℝ))) ^ 4 * Real.exp (-Real.pi) * shellBound n := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hkn' : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have hbase : 15 + ((n + 1 : ℕ) : ℝ) ≤
      ((16 + (k : ℝ)) / (15 + (k : ℝ))) * (15 + (n : ℝ)) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    push_cast
    nlinarith only [hkn']
  have hpow := pow_le_pow_left₀ (by positivity) hbase 4
  rw [mul_pow] at hpow
  have hexp : Real.exp (-Real.pi * (14 + ((n + 1 : ℕ) : ℝ))) =
      Real.exp (-Real.pi * (14 + (n : ℝ))) * Real.exp (-Real.pi) := by
    rw [← Real.exp_add]; congr 1; push_cast; ring
  unfold shellBound
  rw [hexp]
  convert mul_le_mul_of_nonneg_right hpow
    (show 0 ≤ 2 * Real.pi / 64 *
      (Real.exp (-Real.pi * (14 + (n : ℝ))) * Real.exp (-Real.pi)) by positivity) using 1 <;> ring

private theorem shellBound_le (n : ℕ) :
    shellBound n ≤ (13 / 2 / 64 * 15 ^ 4 * 8e-20 : ℝ) * (0.06 : ℝ) ^ n := by
  induction n with
  | zero =>
    simp only [shellBound, Nat.cast_zero, add_zero, pow_zero, mul_one]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_right
        (show 2 * Real.pi / 64 ≤ (13 / 2 / 64 : ℝ) by linarith [Real.pi_lt_d2])
        (by positivity))
      exp_neg_fourteen_pi_lt.le (Real.exp_pos _).le (by positivity)
  | succ n ih =>
    have hstep : shellBound (n + 1) ≤ ((16 / 15 : ℝ) ^ 4 * Real.exp (-Real.pi)) * shellBound n := by
      simpa only [Nat.cast_zero, add_zero] using shellBound_succ_le (Nat.zero_le n)
    exact hstep.trans <| by
      rw [pow_succ']
      convert mul_le_mul shell_ratio_le ih (by unfold shellBound; positivity)
        (by positivity : (0 : ℝ) ≤ 0.06) using 1 <;> ring

private def negativeZerosEquiv : positiveZeros ≃ (positiveZerosᶜ : Set NontrivialZeros) where
  toFun ρ := ⟨⟨conj (ρ.1 : ℂ), conj_mem_nontrivialZeros ρ.1.2⟩, by
    have hρ : 0 < (ρ.1 : ℂ).im := ρ.2
    change ¬0 < (conj (ρ.1 : ℂ)).im
    rw [Complex.conj_im]
    linarith⟩
  invFun ρ := ⟨⟨conj (ρ.1 : ℂ), conj_mem_nontrivialZeros ρ.1.2⟩, by
    have hρ : ¬0 < (ρ.1 : ℂ).im := ρ.2
    have hne := M1.im_ne_zero_of_mem_nontrivialZeros ρ.1.2
    change 0 < (conj (ρ.1 : ℂ)).im
    rw [Complex.conj_im]
    exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hρ) hne)⟩
  left_inv _ := Subtype.ext (Subtype.ext (by simp))
  right_inv _ := Subtype.ext (Subtype.ext (by simp))

private theorem tsum_eq_two_mul_positive_of_conj (w : NontrivialZeros → ℝ)
    (hconj : ∀ ρ : positiveZeros, w (negativeZerosEquiv ρ).1 = w ρ.1)
    (hf : Summable fun ρ : positiveZeros => w ρ.1) :
    (∑' ρ, w ρ) = 2 * ∑' ρ : positiveZeros, w ρ.1 := by
  classical
  let fneg (ρ : (positiveZerosᶜ : Set NontrivialZeros)) := w ρ.1
  have hfneg : Summable fneg :=
    negativeZerosEquiv.summable_iff.mp (hf.congr fun ρ => (hconj ρ).symm)
  let e := Equiv.Set.sumCompl positiveZeros
  calc
    (∑' ρ, w ρ) = (∑' ρ : positiveZeros, w ρ.1) + ∑' ρ, fneg ρ :=
      (e.tsum_eq w).symm.trans (Summable.tsum_sum (f := w ∘ e) hf hfneg)
    _ = 2 * ∑' ρ : positiveZeros, w ρ.1 := by
      rw [two_mul, ← negativeZerosEquiv.tsum_eq fneg]
      exact congrArg (_ + ·) (tsum_congr hconj)

/-- Conjugation pairs the positive and negative zeros with equal weights. -/
theorem muZero_eq_two_mul_tsum_positive
    (hf : Summable fun ρ : positiveZeros => zeroWeight (ρ.1 : ℂ)) :
    muZero = 2 * ∑' ρ : positiveZeros, zeroWeight (ρ.1 : ℂ) :=
  tsum_eq_two_mul_positive_of_conj _ (fun ρ => zeroWeight_conj ρ.1.2) hf

/-- The absolute-ordinate tail is twice its positive-ordinate part. -/
theorem tsum_zeroWeight_abs_tail_eq_two_mul_positive {T : ℝ}
    (hTail : Summable (fun ρ : {ρ : NontrivialZeros | T < |(ρ : ℂ).im|} =>
      zeroWeight (ρ.1 : ℂ))) :
    (∑' ρ : {ρ : NontrivialZeros | T < |(ρ : ℂ).im|}, zeroWeight (ρ.1 : ℂ)) =
      2 * ∑' ρ : {ρ : positiveZeros | T < (ρ.1 : ℂ).im}, zeroWeight (ρ.1.1 : ℂ) := by
  classical
  let tail : Set NontrivialZeros := {ρ | T < |(ρ : ℂ).im|}
  let f (ρ : NontrivialZeros) := zeroWeight (ρ : ℂ)
  let w := tail.indicator f
  let positiveTail : Set positiveZeros := {ρ | T < (ρ.1 : ℂ).im}
  have hpos (ρ : positiveZeros) : w ρ.1 = positiveTail.indicator (fun z => f z.1) ρ := by
    have hρ : 0 < (ρ.1 : ℂ).im := ρ.2
    simp [w, f, tail, positiveTail, Set.indicator, abs_of_pos hρ]
  have hw : Summable w := summable_subtype_iff_indicator.mp hTail
  have hwpos : Summable (fun ρ : positiveZeros => w ρ.1) := hw.subtype _
  have hsymm (ρ : positiveZeros) : w (negativeZerosEquiv ρ).1 = w ρ.1 := by
    change w ⟨conj (ρ.1 : ℂ), _⟩ = w ρ.1
    simp [w, f, tail, Set.indicator, Complex.conj_im, zeroWeight_conj ρ.1.2]
  change (∑' ρ : tail, f ρ.1) = 2 * ∑' ρ : positiveTail, f ρ.1.1
  calc
    _ = ∑' ρ, w ρ := tsum_subtype tail f
    _ = 2 * ∑' ρ : positiveZeros, w ρ.1 :=
      tsum_eq_two_mul_positive_of_conj w hsymm hwpos
    _ = _ := congrArg (2 * ·) ((tsum_congr hpos).trans (tsum_subtype positiveTail _).symm)

set_option maxHeartbeats 800000 in
/-- At heights above `14 + k`, the positive-ordinate weight is bounded by a geometric
majorant of the shells starting at `14 + k`. -/
theorem positive_tail_bound (hN : HN) (k : ℕ) {q : ℝ}
    (hq : 0 ≤ q) (hq' : q < 1)
    (hratio : ((16 + (k : ℝ)) / (15 + (k : ℝ))) ^ 4 * Real.exp (-Real.pi) ≤ q) :
    let tail := {ρ : positiveZeros | 14 + (k : ℝ) < (ρ.1 : ℂ).im}
    let f (ρ : tail) := zeroWeight (ρ.1.1 : ℂ)
    Summable f ∧ (∑' ρ, f ρ) ≤
      (2 * Real.pi / 64 * (15 + (k : ℝ)) ^ 4 * Real.exp (-Real.pi * (14 + (k : ℝ)))) /
        (1 - q) := by
  classical
  dsimp only
  let tail := {ρ : positiveZeros | 14 + (k : ℝ) < (ρ.1 : ℂ).im}
  let f (ρ : tail) := zeroWeight (ρ.1.1 : ℂ)
  let shell (n : ℕ) : Set tail := {ρ | ρ.1 ∈ positiveShell (k + n)}
  have hpartition (ρ : tail) : ∃! n, ρ ∈ shell n := by
    have hρ : 14 + (k : ℝ) < (ρ.1.1 : ℂ).im := ρ.2
    refine (existsUnique_congr ?_).mp
      (existsUnique_nat_interval (x := (ρ.1.1 : ℂ).im - (14 + (k : ℝ))) (by linarith))
    intro n
    change _ ↔ (14 + ((k + n : ℕ) : ℝ) ≤ (ρ.1.1 : ℂ).im ∧
      (ρ.1.1 : ℂ).im < 15 + ((k + n : ℕ) : ℝ))
    push_cast
    constructor <;> rintro ⟨ha, hb⟩ <;> exact ⟨by linarith, by linarith⟩
  let emb (n : ℕ) : shell n ↪ positiveShell (k + n) :=
    ⟨fun ρ => ⟨ρ.1.1, ρ.2⟩, by
      intro ρ σ h
      have hval := congrArg (fun z : positiveShell (k + n) => z.1) h
      exact Subtype.ext (Subtype.ext hval)⟩
  let instShell (n : ℕ) : Fintype (shell n) := Fintype.ofInjective (emb n) (emb n).injective
  have hgeom (n : ℕ) : shellBound (k + n) ≤ shellBound k * q ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        _ ≤ ((16 + (k : ℝ)) / (15 + (k : ℝ))) ^ 4 * Real.exp (-Real.pi) * shellBound (k + n) :=
          shellBound_succ_le (Nat.le_add_right k n)
        _ ≤ q * (shellBound k * q ^ n) :=
          mul_le_mul hratio ih (by unfold shellBound; positivity) hq
        _ = _ := by rw [pow_succ]; ring
  have hle (n : ℕ) : (∑' ρ : shell n, f ρ.1) ≤ shellBound k * q ^ n := by
    refine le_trans ?_ ((positiveShell_bound hN (k + n)).trans (hgeom n))
    rw [tsum_fintype, tsum_fintype]
    exact Finset.sum_le_sum_of_injOn (emb n) (emb n).injective.injOn
      (by simp) (fun _ _ => le_rfl) (fun _ _ _ => zeroWeight_nonneg _)
  have hg : Summable (fun n : ℕ => shellBound k * q ^ n) :=
    (summable_geometric_of_lt_one hq hq').mul_left _
  have houter : Summable (fun n => ∑' ρ : shell n, f ρ.1) :=
    hg.of_nonneg_of_le (fun _ => tsum_nonneg fun _ => zeroWeight_nonneg _) hle
  have hf : Summable f :=
    (summable_partition (f := f) (fun _ => zeroWeight_nonneg _) hpartition).mpr
      ⟨fun _ => (hasSum_fintype _).summable, houter⟩
  refine ⟨hf, ?_⟩
  change (∑' ρ, f ρ) ≤ shellBound k / (1 - q)
  calc
    _ = ∑' n, ∑' ρ : shell n, f ρ.1 := by
      rw [← (Set.sigmaEquiv _ hpartition).tsum_eq f]
      exact ((Set.sigmaEquiv _ hpartition).summable_iff.mpr hf).tsum_sigma
    _ ≤ ∑' n, shellBound k * q ^ n := houter.tsum_le_tsum hle hg
    _ = _ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hq hq', div_eq_mul_inv]

set_option maxHeartbeats 800000 in
/-- The mass at ordinate zero is less than 8.752e-16 under the two explicit zero bounds. -/
theorem muZero_lt (h14 : H14) (hN : HN) : muZero < 8.752e-16 := by
  classical
  let f (ρ : positiveZeros) := zeroWeight (ρ.1 : ℂ)
  let g (n : ℕ) := (13 / 2 / 64 * 15 ^ 4 * 8e-20 : ℝ) * (0.06 : ℝ) ^ n
  have hg : Summable g := (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hle (n : ℕ) : (∑' ρ : positiveShell n, f ρ.1) ≤ g n :=
    (positiveShell_bound hN n).trans (shellBound_le n)
  have houter : Summable (fun n => ∑' ρ : positiveShell n, f ρ.1) :=
    hg.of_nonneg_of_le (fun _ => tsum_nonneg fun _ => zeroWeight_nonneg _) hle
  have hf : Summable f :=
    (summable_partition (f := f) (fun ρ => zeroWeight_nonneg (ρ.1 : ℂ))
      (positiveShell_partition h14)).mpr
      ⟨fun _ => (hasSum_fintype _).summable, houter⟩
  have hsum : ∑' ρ, f ρ ≤ ∑' n, g n := calc
    _ = ∑' n, ∑' ρ : positiveShell n, f ρ.1 := by
      rw [← (Set.sigmaEquiv _ (positiveShell_partition h14)).tsum_eq f]
      exact ((Set.sigmaEquiv _ (positiveShell_partition h14)).summable_iff.mpr hf).tsum_sigma
    _ ≤ _ := houter.tsum_le_tsum hle hg
  rw [muZero_eq_two_mul_tsum_positive hf]
  have hgeo : ∑' n, g n = (13 / 2 / 64 * 15 ^ 4 * 8e-20 : ℝ) * (1 - 0.06)⁻¹ := by
    dsimp [g]
    rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  rw [hgeo] at hsum
  norm_num at hsum ⊢
  linarith only [hsum]

/-- The real limit value in the class-one paper is negative for the indicated range of arities.
The hypotheses RH, Z2 and Z3 identify the value as a limit via the preceding module. -/
theorem phiR_real_limit_neg (_hRH : RiemannHypothesis) (_hZ2 : Z2) (_hZ3 : Z3)
    (h14 : H14) (hN : HN) {r : ℕ} (hr : 2 ≤ r) (hrMax : r ≤ 4 * 10 ^ 15) :
    ((r.choose 2 : ℝ) * muZero - (r : ℝ) * Real.log (2 * Real.pi)) /
      ((r - 2).factorial : ℝ) < 0 := by
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hmax : (r : ℝ) ≤ 4000000000000000 := by exact_mod_cast hrMax
  have hprod : ((r : ℝ) - 1) * muZero < 2 * Real.log (2 * Real.pi) := by
    calc
      _ ≤ ((r : ℝ) - 1) * 8.752e-16 :=
        mul_le_mul_of_nonneg_left (muZero_lt h14 hN).le (by linarith)
      _ < _ := by linarith [log_two_pi_gt]
  apply div_neg_of_neg_of_pos _ (by positivity)
  rw [Nat.cast_choose_two]
  calc
    _ = (r : ℝ) / 2 * (((r : ℝ) - 1) * muZero - 2 * Real.log (2 * Real.pi)) := by ring
    _ < 0 := mul_neg_of_pos_of_neg (by linarith) (sub_neg.mpr hprod)

/-- The unsubtracted radial limit along the real axis is a negative real number. -/
theorem phiR_tendsto_negative_real (hRH : RiemannHypothesis) (hZ2 : Z2) (hZ3 : Z3)
    (h14 : H14) (hN : HN) {r : ℕ} (hr : 2 ≤ r) (hrMax : r ≤ 4 * 10 ^ 15) :
    ∃ L : ℝ, L < 0 ∧
      Tendsto (fun η : ℝ => (η : ℂ) * PhiRc r ((r : ℂ) - 1 + η)) (𝓝[>] 0) (𝓝 (L : ℂ)) :=
  ⟨_, phiR_real_limit_neg hRH hZ2 hZ3 h14 hN hr hrMax, phiR_real_limit hRH hZ2 hZ3 hr⟩

end GoldbachBoundaries.PhiRProof
