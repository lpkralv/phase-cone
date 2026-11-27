import GoldbachBoundaries.PhiR.LowZerosSpec
import GoldbachBoundaries.PhiR.UnsubtractedSign
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan

/-! # The integer gap for the unsubtracted real-point limit -/

noncomputable section

open Set

namespace GoldbachBoundaries.PhiRProof

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- The integer immediately below the real threshold. -/
def gapN : ℕ := 5639249912025015212

def muLo : ℝ := 6.518161440195427267760e-19
def muHi : ℝ := 6.518161440195427267830e-19

private def piLo : ℝ := 3.14159265358979323846264338327
private def piHi : ℝ := 3.14159265358979323846264338328

set_option maxHeartbeats 1500000

private theorem exp_eq_pow (x : ℝ) (n : ℕ) (hn : 0 < n) :
    Real.exp x = Real.exp (x / (n : ℝ)) ^ n := by
  rw [← Real.exp_nat_mul, ← mul_div_assoc, mul_comm (n : ℝ) x,
    mul_div_cancel_right₀ _ (by exact_mod_cast Nat.ne_of_gt hn)]

-- For small arguments, check the Taylor polynomial and the remainder by exact arithmetic.
private theorem exp_le_truncation {x : ℝ} (hx : |x| ≤ 1) :
    Real.exp x ≤ (∑ m ∈ Finset.range 28, x ^ m / (m.factorial : ℝ)) +
      |x| ^ 28 * (29 / ((28 : ℕ).factorial * 28 : ℝ)) := by
  have h := (abs_le.mp (Real.exp_bound hx (n := 28) (by decide))).2
  norm_num only [Nat.succ_eq_add_one, Nat.reduceAdd, Nat.cast_ofNat] at h
  linarith only [h]

local macro "reduced_exp_decide" : tactic => `(tactic|
  first
  | refine (exp_le_truncation (by norm_num)).trans ?_
    norm_num [Finset.sum_range_succ]
  | refine le_trans ?_ (Real.sum_le_exp_of_nonneg (by norm_num) 28)
    norm_num [Finset.sum_range_succ])

private theorem arctan_truncation {x : ℝ} (hx : 0 ≤ x) (hx' : x < 1) (n : ℕ) :
    |Real.arctan x - ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * x ^ (2 * i + 1) /
      ((2 * i + 1 : ℕ) : ℝ)| ≤ x ^ (2 * n + 1) / (1 - x ^ 2) := by
  let f (i : ℕ) := (-1 : ℝ) ^ i * x ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ)
  have hf : HasSum f (Real.arctan x) :=
    Real.hasSum_arctan (by simpa [Real.norm_eq_abs, abs_of_nonneg hx] using hx')
  let g (i : ℕ) := x ^ (2 * n + 1) * (x ^ 2) ^ i
  have hq : x ^ 2 < 1 := by nlinarith
  have hg : Summable g := (summable_geometric_of_lt_one (sq_nonneg x) hq).mul_left _
  have hle (i : ℕ) : ‖f (i + n)‖ ≤ g i := by
    have hden : (0 : ℝ) ≤ ((2 * (i + n) + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    simp only [f, g, Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
      one_mul, abs_of_nonneg hx, abs_of_nonneg hden]
    rw [show 2 * (i + n) + 1 = (2 * n + 1) + 2 * i by omega, pow_add, pow_mul]
    exact div_le_self (by positivity) (by exact_mod_cast (show 1 ≤ 2 * n + 1 + 2 * i by omega))
  have hnorm : Summable (fun i => ‖f (i + n)‖) :=
    hg.of_nonneg_of_le (fun _ => norm_nonneg _) hle
  change |Real.arctan x - ∑ i ∈ Finset.range n, f i| ≤ _
  rw [← hf.tsum_eq, ← hf.summable.sum_add_tsum_nat_add n, add_sub_cancel_left,
    ← Real.norm_eq_abs]
  calc
    _ ≤ ∑' i, ‖f (i + n)‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' i, g i := hnorm.tsum_le_tsum hle hg
    _ = _ := by
      dsimp only [g]
      rw [tsum_mul_left, tsum_geometric_of_lt_one (sq_nonneg x) hq, div_eq_mul_inv]

private theorem pi_bounds : piLo < Real.pi ∧ Real.pi < piHi := by
  have h5 := abs_le.mp (arctan_truncation (x := (5 : ℝ)⁻¹) (by norm_num) (by norm_num) 23)
  have h239 := abs_le.mp (arctan_truncation (x := (239 : ℝ)⁻¹) (by norm_num) (by norm_num) 8)
  have hMachin := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
  norm_num [Finset.sum_range_succ] at h5 h239 hMachin
  unfold piLo piHi
  constructor <;> linarith only [h5.1, h5.2, h239.1, h239.2, hMachin]

private theorem tail_ratio_le : (34 / 33 : ℝ) ^ 4 * Real.exp (-Real.pi) ≤ 0.05 := by
  calc
    _ ≤ (34 / 33 : ℝ) ^ 4 * Real.exp (-3.14) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg Real.pi_gt_d2.le))
        (by positivity)
    _ ≤ _ := by
      rw [exp_eq_pow _ 4 (by decide)]
      have h : Real.exp (-(3.14 : ℝ) / 4) ≤ 0.4562 := by
        norm_num
        reduced_exp_decide
      have hp := pow_le_pow_left₀ (Real.exp_pos _).le h 4
      exact (mul_le_mul_of_nonneg_left hp (by norm_num)).trans (by norm_num)

/-- A rational upper bound for the exponential at the tail cutoff. -/
theorem exp_neg_pi_mul_32_lt : Real.exp (-Real.pi * 32) < 2.1876e-44 := calc
  _ ≤ Real.exp (-(3.141592 : ℝ) * 32) :=
    Real.exp_le_exp.mpr (by linarith only [Real.pi_gt_d6])
  _ < _ := by
    rw [exp_eq_pow _ 128 (by decide)]
    have h : Real.exp (-(3.141592 : ℝ) * 32 / 128) ≤ 0.45593821 := by
      norm_num
      reduced_exp_decide
    exact (pow_le_pow_left₀ (Real.exp_pos _).le h _).trans_lt (by norm_num)

private theorem tail_majorant_lt :
    2 * (2 * Real.pi / 64 * 33 ^ 4 * Real.exp (-Real.pi * 32) / (1 - 0.05)) < 5.58e-39 := by
  have he : Real.exp (-Real.pi * 32) < 2.2e-44 :=
    exp_neg_pi_mul_32_lt.trans (by norm_num)
  have hpi : 2 * Real.pi / 64 ≤ (13 / 2 / 64 : ℝ) := by linarith [Real.pi_lt_d2]
  calc
    _ ≤ (2 * (13 / 2 / 64 * 33 ^ 4 * 2.2e-44 / (1 - 0.05)) : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact mul_le_mul (mul_le_mul_of_nonneg_right hpi (by positivity)) he.le
        (Real.exp_pos _).le (by norm_num)
    _ < _ := by norm_num

private def pairWeight (a b t : ℝ) : ℝ := 2 * a / Real.cosh (b * t)

private theorem pairWeight_le {a b t a' b' t' : ℝ} (ha : a ≤ a')
    (hb : b' ≤ b) (ht : t' ≤ t) (ha' : 0 ≤ a') (hb' : 0 ≤ b') (ht' : 0 ≤ t') :
    pairWeight a b t ≤ pairWeight a' b' t' := by
  have hbt : b' * t' ≤ b * t := mul_le_mul hb ht ht' (hb'.trans hb)
  have hpos : 0 ≤ b' * t' := mul_nonneg hb' ht'
  unfold pairWeight
  exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ha (by norm_num))
    (Real.cosh_pos _).le).trans
    (div_le_div_of_nonneg_left (mul_nonneg (by norm_num) ha') (Real.cosh_pos _)
      (Real.cosh_le_cosh.mpr (by rwa [abs_of_nonneg hpos, abs_of_nonneg (hpos.trans hbt)])))

private theorem pairWeight_log (a : ℝ) {q : ℝ} (hq : 0 < q) :
    pairWeight a 1 (Real.log (q ^ (128 : ℕ))) = 4 * a / (q ^ 128 + (q ^ 128)⁻¹) := by
  rw [pairWeight, one_mul, Real.cosh_eq, Real.exp_neg, Real.exp_log (pow_pos hq _),
    div_div_eq_mul_div]
  ring

private theorem pairWeight_lower {a x q : ℝ} (ha : 0 ≤ a) (hx : 0 ≤ x) (hq : 0 < q)
    (he : Real.exp (x / 128) ≤ q) :
    4 * a / (q ^ 128 + (q ^ 128)⁻¹) ≤ pairWeight a 1 x := by
  rw [← pairWeight_log a hq]
  apply pairWeight_le le_rfl le_rfl _ ha zero_le_one hx
  rw [Real.le_log_iff_exp_le (pow_pos hq _), exp_eq_pow _ 128 (by decide)]
  exact pow_le_pow_left₀ (Real.exp_pos _).le he _

private theorem pairWeight_upper {a x q : ℝ} (ha : 0 ≤ a) (hq : 1 ≤ q)
    (he : q ≤ Real.exp (x / 128)) :
    pairWeight a 1 x ≤ 4 * a / (q ^ 128 + (q ^ 128)⁻¹) := by
  have hq' : 0 < q := zero_lt_one.trans_le hq
  rw [← pairWeight_log a hq']
  apply pairWeight_le le_rfl le_rfl _ ha zero_le_one (Real.log_nonneg (one_le_pow₀ hq))
  rw [Real.log_le_iff_le_exp (pow_pos hq' _), exp_eq_pow _ 128 (by decide)]
  exact pow_le_pow_left₀ hq'.le he _

private def expLo (i : Fin 4) : ℝ :=
  ![1.41470120881737374794364978, 1.67524341791814238763045771,
    1.84754697591477506601349214, 2.11010731675073745191330121] i

private def expHi (i : Fin 4) : ℝ :=
  ![1.41470120881737374794364979, 1.67524341791814238763045772,
    1.84754697591477506601349215, 2.11010731675073745191330122] i

private def pairLo (i : Fin 4) : ℝ :=
  ![6.518161437581836183051225e-19, 2.613581644384965478970084e-28,
    9.440330357099657741790807e-34, 3.874612804313823781443644e-41] i

private def pairHi (i : Fin 4) : ℝ :=
  ![6.518161437581836183051232e-19, 2.613581644384965478970087e-28,
    9.440330357099657741790814e-34, 3.874612804313823781443648e-41] i

private theorem pairLo_le (i : Fin 4) : pairLo i ≤ pairWeight piLo piHi (hi i) := by
  have he : Real.exp (piHi * hi i / 128) ≤ expHi i := by
    fin_cases i <;> norm_num [piHi, hi, start, expHi] <;> reduced_exp_decide
  have h := pairWeight_lower (a := piLo) (by norm_num [piLo])
    (show 0 ≤ piHi * hi i by fin_cases i <;> norm_num [piHi, hi, start])
    (show 0 < expHi i by fin_cases i <;> norm_num [expHi]) he
  refine le_trans ?_ (by simpa only [pairWeight, one_mul] using h)
  fin_cases i <;> norm_num [pairLo, piLo, expHi]

private theorem le_pairHi (i : Fin 4) : pairWeight piHi piLo (lo i) ≤ pairHi i := by
  have he : expLo i ≤ Real.exp (piLo * lo i / 128) := by
    fin_cases i <;> norm_num [piLo, lo, start, expLo] <;> reduced_exp_decide
  have h := pairWeight_upper (a := piHi) (by norm_num [piHi])
    (show 1 ≤ expLo i by fin_cases i <;> norm_num [expLo]) he
  refine le_trans (by simpa only [pairWeight, one_mul] using h) ?_
  fin_cases i <;> norm_num [pairHi, piHi, expLo]

private theorem endpoint_lower : muLo < ∑ i, pairWeight piLo piHi (hi i) :=
  (show muLo < ∑ i, pairLo i by norm_num [muLo, pairLo, Fin.sum_univ_four]).trans_le
    (Finset.sum_le_sum fun i _ => pairLo_le i)

private theorem endpoint_upper :
    (∑ i, pairWeight piHi piLo (lo i)) + 5.58e-39 < muHi := by
  calc
    _ ≤ (∑ i, pairHi i) + 5.58e-39 :=
      add_le_add_left (Finset.sum_le_sum fun i _ => le_pairHi i) _
    _ < _ := by norm_num [muHi, pairHi, Fin.sum_univ_four]

/-- The lower mass bound is above the bottom of the window for the integer gap. -/
theorem log_div_gapN_lt_muLo : 2 * Real.log (2 * Real.pi) / (gapN : ℝ) < muLo := by
  calc
    _ ≤ 2 * Real.log (2 * piHi) / (gapN : ℝ) := by
      apply div_le_div_of_nonneg_right _ (by norm_num [gapN])
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_left pi_bounds.2.le (by norm_num))
    _ < _ := by
      rw [div_lt_iff₀ (by norm_num [gapN]), ← lt_div_iff₀' (by norm_num : (0 : ℝ) < 2)]
      rw [Real.log_lt_iff_lt_exp (by norm_num [piHi])]
      rw [exp_eq_pow _ 2 (by decide)]
      have h : 2.50662827463100050250 ≤ Real.exp (muLo * (gapN : ℝ) / 2 / (2 : ℝ)) := by
        norm_num [gapN, muLo]
        reduced_exp_decide
      exact (by norm_num [piHi] : 2 * piHi < (2.50662827463100050250 : ℝ) ^ 2).trans_le
        (pow_le_pow_left₀ (by norm_num) h 2)

/-- The upper mass bound is below the top of the window for the integer gap. -/
theorem muHi_lt_log_div_gapN_sub_one :
    muHi < 2 * Real.log (2 * Real.pi) / ((gapN : ℝ) - 1) := by
  calc
    _ < 2 * Real.log (2 * piLo) / ((gapN : ℝ) - 1) := by
      rw [lt_div_iff₀ (by norm_num [gapN]), ← div_lt_iff₀' (by norm_num : (0 : ℝ) < 2)]
      rw [Real.lt_log_iff_exp_lt (by norm_num [piLo])]
      rw [exp_eq_pow _ 2 (by decide)]
      have h : Real.exp (muHi * ((gapN : ℝ) - 1) / 2 / (2 : ℝ)) ≤ 2.50662827463100050215 := by
        norm_num [gapN, muHi]
        reduced_exp_decide
      exact (pow_le_pow_left₀ (Real.exp_pos _).le h 2).trans_lt (by norm_num [piLo])
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (by norm_num [gapN])
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Real.log_le_log (by norm_num [piLo])
        (mul_le_mul_of_nonneg_left pi_bounds.1.le (by norm_num))

private theorem lo_pos (i : Fin 4) : 0 < lo i := by
  fin_cases i <;> norm_num [lo, start]

/-- The four certified conjugate pairs and a bound on the doubled positive tail enclose
the mass at ordinate zero. -/
theorem muZero_mem_of_positive_tail (hLow : ReleaseLowZeros)
    (hTailSum : Summable (fun z : {z : positiveZeros | 32 < (z.1 : ℂ).im} =>
      zeroWeight (z.1.1 : ℂ)))
    (hTailBound : 2 * (∑' z : {z : positiveZeros | 32 < (z.1 : ℂ).im},
      zeroWeight (z.1.1 : ℂ)) < 5.58e-39) :
    muLo < muZero ∧ muZero < muHi := by
  classical
  obtain ⟨ρ, hρ, hbracket, hcover⟩ := hLow
  let low := {z : positiveZeros | (z.1 : ℂ).im ≤ 32}
  let f (z : positiveZeros) : ℝ := zeroWeight (z.1 : ℂ)
  let toLow (i : Fin 4) : low :=
    have h : ρ i ∈ {z : ℂ | z ∈ NontrivialZeros ∧ z.im ∈ Ioc 0 32} :=
      hcover.symm ▸ mem_range_self i
    ⟨⟨⟨ρ i, h.1⟩, h.2.1⟩, h.2.2⟩
  let e : Fin 4 ≃ low := Equiv.ofBijective toLow ⟨by
    intro i j h
    exact hρ (congrArg (fun z : low => (z.1.1 : ℂ)) h), by
    intro z
    have hz : (z.1.1 : ℂ) ∈ {z : ℂ | z ∈ NontrivialZeros ∧ z.im ∈ Ioc 0 32} :=
      ⟨z.1.1.2, z.1.2, z.2⟩
    rw [hcover] at hz
    obtain ⟨i, hi⟩ := hz
    exact ⟨i, Subtype.ext (Subtype.ext (Subtype.ext hi))⟩⟩
  let instLow : Fintype low := Fintype.ofEquiv (Fin 4) e
  have hlo : Summable (fun z : low => f z.1) := (hasSum_fintype _).summable
  have hcompl : {z : positiveZeros | 32 < (z.1 : ℂ).im} = lowᶜ := by
    ext z
    change 32 < (z.1 : ℂ).im ↔ ¬ (z.1 : ℂ).im ≤ 32
    exact not_le.symm
  rw [hcompl] at hTailSum hTailBound
  have hf : Summable f :=
    (Equiv.Set.sumCompl low).summable_iff.mp (Summable.sum _ hlo hTailSum)
  have hsplit : muZero = (∑ i, pairWeight Real.pi Real.pi (ρ i).im) +
      2 * ∑' z : (lowᶜ : Set positiveZeros), f z.1 := by
    rw [muZero_eq_two_mul_tsum_positive hf, ← hlo.tsum_add_tsum_compl hTailSum,
      mul_add, ← e.tsum_eq (fun z : low => f z.1), tsum_fintype, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    change 2 * zeroWeight (ρ i) = pairWeight Real.pi Real.pi (ρ i).im
    rw [zeroWeight, (hbracket i).2.2]
    simp [pairWeight, mul_div_assoc]
  have hlow : (∑ i, pairWeight piLo piHi (hi i)) ≤
      ∑ i, pairWeight Real.pi Real.pi (ρ i).im := by
    refine Finset.sum_le_sum fun i _ => ?_
    exact pairWeight_le pi_bounds.1.le pi_bounds.2.le (hbracket i).1.2.le Real.pi_pos.le
      Real.pi_pos.le (le_trans (lo_pos i).le (hbracket i).1.1.le)
  have hhigh : (∑ i, pairWeight Real.pi Real.pi (ρ i).im) ≤
      ∑ i, pairWeight piHi piLo (lo i) := by
    refine Finset.sum_le_sum fun i _ => ?_
    exact pairWeight_le pi_bounds.2.le pi_bounds.1.le (hbracket i).1.1.le
      (Real.pi_pos.le.trans pi_bounds.2.le) (by norm_num [piLo]) (lo_pos i).le
  have htailNonneg : 0 ≤ ∑' z : (lowᶜ : Set positiveZeros), f z.1 :=
    tsum_nonneg fun _ => zeroWeight_nonneg _
  rw [hsplit]
  constructor
  · linarith only [endpoint_lower, hlow, htailNonneg]
  · linarith only [endpoint_upper, hhigh, hTailBound]

/-- The four certified conjugate pairs and the count bound enclose the mass at ordinate zero. -/
theorem muZero_mem (_hRH : RiemannHypothesis) (_hZ2 : Z2)
    (hLow : ReleaseLowZeros) (hN : HN) : muLo < muZero ∧ muZero < muHi := by
  have htail := positive_tail_bound hN 18 (by norm_num : (0 : ℝ) ≤ 0.05)
    (by norm_num : (0.05 : ℝ) < 1)
    (by convert tail_ratio_le using 2; norm_num)
  have hcut : (14 : ℝ) + ((18 : ℕ) : ℝ) = 32 := by norm_num
  have hnext : (15 : ℝ) + ((18 : ℕ) : ℝ) = 33 := by norm_num
  dsimp only at htail
  rw [hcut, hnext] at htail
  exact muZero_mem_of_positive_tail hLow htail.1
    ((mul_le_mul_of_nonneg_left htail.2 (by norm_num)).trans_lt tail_majorant_lt)

/-- The mass enclosure places the sign-change threshold between consecutive integers. -/
theorem rStar_gap_of_muZero_mem (hpos : 0 < muZero)
    (hmem : muLo < muZero ∧ muZero < muHi) :
    (gapN : ℝ) < 1 + 2 * Real.log (2 * Real.pi) / muZero ∧
      1 + 2 * Real.log (2 * Real.pi) / muZero < (gapN : ℝ) + 1 := by
  have hNpos : (0 : ℝ) < gapN := by norm_num [gapN]
  have hNsub : (0 : ℝ) < (gapN : ℝ) - 1 := by norm_num [gapN]
  obtain ⟨hlo, hhi⟩ := hmem
  have h1 := (lt_div_iff₀ hNsub).mp (hhi.trans muHi_lt_log_div_gapN_sub_one)
  have h2 := (div_lt_iff₀ hNpos).mp (log_div_gapN_lt_muLo.trans hlo)
  constructor
  · have h := (lt_div_iff₀ hpos).mpr (by simpa [mul_comm] using h1 :
      ((gapN : ℝ) - 1) * muZero < 2 * Real.log (2 * Real.pi))
    linarith only [h]
  · have h := (div_lt_iff₀ hpos).mpr (by simpa [mul_comm] using h2 :
      2 * Real.log (2 * Real.pi) < (gapN : ℝ) * muZero)
    linarith only [h]

/-- The sign-change threshold lies strictly between two consecutive integers. -/
theorem rStar_gap (hRH : RiemannHypothesis) (hZ2 : Z2) (hLow : ReleaseLowZeros) (hN : HN) :
    (gapN : ℝ) < 1 + 2 * Real.log (2 * Real.pi) / muZero ∧
      1 + 2 * Real.log (2 * Real.pi) / muZero < (gapN : ℝ) + 1 :=
  rStar_gap_of_muZero_mem (muZero_pos hRH hZ2) (muZero_mem hRH hZ2 hLow hN)

/-- The gap determines the sign of the real limit at every admissible integer arity. -/
theorem phiR_real_limit_ne_zero_of_gap (hpos : 0 < muZero)
    (hgap : (gapN : ℝ) < 1 + 2 * Real.log (2 * Real.pi) / muZero ∧
      1 + 2 * Real.log (2 * Real.pi) / muZero < (gapN : ℝ) + 1)
    (r : ℕ) (hr : 2 ≤ r) :
    let value := ((r.choose 2 : ℝ) * muZero - (r : ℝ) * Real.log (2 * Real.pi)) /
      ((r - 2).factorial : ℝ)
    value ≠ 0 ∧ (r ≤ gapN → value < 0) ∧ (gapN + 1 ≤ r → 0 < value) := by
  dsimp only
  obtain ⟨hleft, hright⟩ := hgap
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hfactor :
      (r.choose 2 : ℝ) * muZero - (r : ℝ) * Real.log (2 * Real.pi) =
        ((r : ℝ) / 2) * (((r : ℝ) - 1) * muZero - 2 * Real.log (2 * Real.pi)) := by
    rw [Nat.cast_choose_two]
    ring
  let v := ((r.choose 2 : ℝ) * muZero - (r : ℝ) * Real.log (2 * Real.pi)) /
    ((r - 2).factorial : ℝ)
  change v ≠ 0 ∧ (r ≤ gapN → v < 0) ∧ (gapN + 1 ≤ r → 0 < v)
  have hneg (h : r ≤ gapN) : v < 0 := by
    dsimp only [v]
    rw [hfactor]
    have h' : (r : ℝ) ≤ gapN := by exact_mod_cast h
    have hp := (lt_div_iff₀ hpos).mp (show (r : ℝ) - 1 <
      2 * Real.log (2 * Real.pi) / muZero by linarith only [h', hleft])
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by linarith) (sub_neg.mpr hp))
      (by positivity)
  have hpositive (h : gapN + 1 ≤ r) : 0 < v := by
    dsimp only [v]
    rw [hfactor]
    have h' : (gapN : ℝ) + 1 ≤ r := by exact_mod_cast h
    have hp := (div_lt_iff₀ hpos).mp (show
      2 * Real.log (2 * Real.pi) / muZero < (r : ℝ) - 1 by linarith only [h', hright])
    exact div_pos (mul_pos (by linarith) (sub_pos.mpr hp)) (by positivity)
  refine ⟨?_, hneg, hpositive⟩
  rcases le_or_gt r gapN with h | h
  · exact (hneg h).ne
  · exact (hpositive h).ne'

/-- Every admissible integer arity gives a nonzero real limit, with its sign determined by
the integer gap. -/
theorem phiR_real_limit_ne_zero (hRH : RiemannHypothesis) (hZ2 : Z2) (_hZ3 : Z3)
    (hLow : ReleaseLowZeros) (hN : HN) (r : ℕ) (hr : 2 ≤ r) :
    let value := ((r.choose 2 : ℝ) * muZero - (r : ℝ) * Real.log (2 * Real.pi)) /
      ((r - 2).factorial : ℝ)
    value ≠ 0 ∧ (r ≤ gapN → value < 0) ∧ (gapN + 1 ≤ r → 0 < value) :=
  phiR_real_limit_ne_zero_of_gap (muZero_pos hRH hZ2) (rStar_gap hRH hZ2 hLow hN) r hr

end GoldbachBoundaries.PhiRProof
