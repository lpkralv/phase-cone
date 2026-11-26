import GoldbachBoundaries.Paper2.M3.Real
import PrimeNumberTheoremAnd.Consequences

/-!
`tΘ(t) → 1` as `t → 0⁺`, from the prime number theorem `θ(x) ~ x` (PNT+'s sorry-free `chebyshev_asymptotic`).

Discrete Abel summation with `q = e^{-t}`: `Θ(t) = ∑ aₙ qⁿ` (`aₙ = log n` for `n` prime, else `0`) equals
`(1 - q) ∑ θ(n) qⁿ`; with `|θ(n) - n| ≤ εn + C` this gives `|Θ(t) - q/(1-q)| ≤ ε q/(1-q) + C`, and
`t q/(1-q) = t/(eᵗ - 1) → 1`.
-/

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
namespace GoldbachBoundaries.Paper2.M3
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- `aₙ = log n` for `n` prime, `0` otherwise. -/
def ccA (n : ℕ) : ℝ := if n.Prime then Real.log n else 0

/-- Partial sums `P N = ∑_{k < N} aₖ`. -/
def ccP (N : ℕ) : ℝ := ∑ k ∈ Finset.range N, ccA k

lemma ccA_nonneg (n : ℕ) : 0 ≤ ccA n := by
  unfold ccA; split_ifs
  · exact Real.log_natCast_nonneg n
  · exact le_rfl

lemma ccA_le (n : ℕ) : ccA n ≤ n := by
  unfold ccA; split_ifs
  · exact (Real.log_le_sub_one_of_pos (by exact_mod_cast (‹n.Prime›).pos)).trans (by linarith)
  · exact Nat.cast_nonneg n

lemma ccP_nonneg (N : ℕ) : 0 ≤ ccP N := Finset.sum_nonneg fun k _ => ccA_nonneg k

lemma ccP_le (N : ℕ) : ccP N ≤ (N : ℝ) ^ 2 := by
  unfold ccP
  calc ∑ k ∈ Finset.range N, ccA k ≤ ∑ _k ∈ Finset.range N, (N : ℝ) :=
        Finset.sum_le_sum fun k hk => (ccA_le k).trans (by
          have := Finset.mem_range.1 hk; exact_mod_cast this.le)
    _ = (N : ℝ) ^ 2 := by simp; ring

/-- `P (n + 1) = θ(n)`. -/
lemma ccP_succ_eq_theta (n : ℕ) : ccP (n + 1) = Chebyshev.theta n := by
  rw [Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast, Finset.sum_filter, ccP]
  rw [← Nat.Ico_zero_eq_range, Finset.Ico_add_one_right_eq_Icc]
  exact Finset.sum_congr rfl fun k _ => rfl

/-- `Θ(t) = ∑ aₙ qⁿ`, `q = e^{-t}`. -/
lemma cc_Theta_eq_tsum (t : ℝ) : Theta t = ∑' n : ℕ, ccA n * Real.exp (-t) ^ n := by
  have hsupp : Function.support (fun n : ℕ => ccA n * Real.exp (-t) ^ n) ⊆ {p | p.Prime} := by
    intro n hn
    by_contra hp
    apply hn
    simp [ccA, show ¬ n.Prime from hp]
  rw [← tsum_subtype_eq_of_support_subset hsupp]
  unfold Theta
  refine tsum_congr fun p => ?_
  have hp : (p : ℕ).Prime := p.prop
  simp only [ccA, hp, ite_true]
  rw [← Real.exp_nat_mul]
  congr 2
  ring

/-- Summation by parts, finite form:
`∑_{n<N} aₙ qⁿ = (1 - q) ∑_{n<N} P(n+1) qⁿ + P(N) q^N`. -/
lemma cc_sum_by_parts (q : ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range N, ccA n * q ^ n =
      (1 - q) * ∑ n ∈ Finset.range N, ccP (n + 1) * q ^ n + ccP N * q ^ N := by
  induction N with
  | zero => simp [ccP]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    have hP : ccP (N + 1) = ccP N + ccA N := by simp [ccP, Finset.sum_range_succ]
    rw [hP, pow_succ]
    ring

lemma cc_summable_A {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) : Summable fun n : ℕ => ccA n * q ^ n := by
  have hs : Summable fun n : ℕ => (n : ℝ) ^ 1 * q ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one 1 (by rw [Real.norm_of_nonneg hq0]; exact hq1)
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (ccA_nonneg n) (pow_nonneg hq0 n)) (fun n => ?_) hs
  rw [pow_one]
  exact mul_le_mul_of_nonneg_right (ccA_le n) (pow_nonneg hq0 n)

lemma cc_summable_P {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable fun n : ℕ => ccP (n + 1) * q ^ n := by
  have hq : ‖q‖ < 1 := by rw [Real.norm_of_nonneg hq0]; exact hq1
  have hs : Summable fun n : ℕ => ((n : ℝ) ^ 2 * q ^ n + 2 * ((n : ℝ) ^ 1 * q ^ n)) + q ^ n :=
    ((summable_pow_mul_geometric_of_norm_lt_one 2 hq).add
      ((summable_pow_mul_geometric_of_norm_lt_one 1 hq).mul_left 2)).add
      (summable_geometric_of_lt_one hq0 hq1)
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (ccP_nonneg _) (pow_nonneg hq0 n)) (fun n => ?_) hs
  have h1 := ccP_le (n + 1)
  have hqn := pow_nonneg hq0 n
  push_cast at h1
  nlinarith

/-- Summation by parts, series form: `∑ aₙ qⁿ = (1 - q) ∑ θ(n) qⁿ`. -/
lemma cc_tsum_A_eq {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∑' n : ℕ, ccA n * q ^ n = (1 - q) * ∑' n : ℕ, ccP (n + 1) * q ^ n := by
  have hA := (cc_summable_A hq0 hq1).hasSum.tendsto_sum_nat
  have hB := (cc_summable_P hq0 hq1).hasSum.tendsto_sum_nat
  have hPq : Tendsto (fun N : ℕ => ccP N * q ^ N) atTop (𝓝 0) := by
    have h0 := tendsto_pow_const_mul_const_pow_of_abs_lt_one 2 (r := q) (by rw [abs_of_nonneg hq0]; exact hq1)
    refine squeeze_zero (fun N => mul_nonneg (ccP_nonneg N) (pow_nonneg hq0 N)) (fun N => ?_) h0
    exact mul_le_mul_of_nonneg_right (ccP_le N) (pow_nonneg hq0 N)
  have hR := (hB.const_mul (1 - q)).add hPq
  rw [add_zero] at hR
  refine tendsto_nhds_unique hA (hR.congr fun N => ?_)
  exact (cc_sum_by_parts q N).symm

/-- `|θ(n) - n| ≤ εn + C` for all `n` (from `chebyshev_asymptotic`). -/
lemma cc_theta_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, |ccP (n + 1) - n| ≤ ε * n + C := by
  have h := chebyshev_asymptotic.isLittleO
  rw [Asymptotics.isLittleO_iff] at h
  obtain ⟨X, hX⟩ := eventually_atTop.1 (h hε)
  set X' : ℝ := max X 0 with hX'
  refine ⟨Chebyshev.theta X' + X', add_nonneg (Chebyshev.theta_nonneg _) (le_max_right _ _), fun n => ?_⟩
  rw [ccP_succ_eq_theta]
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  by_cases hn : X ≤ (n : ℝ)
  · have := hX n hn
    simp only [Pi.sub_apply, id, Real.norm_eq_abs, abs_of_nonneg hn0] at this
    linarith [Chebyshev.theta_nonneg X', le_max_right X 0]
  · push Not at hn
    have hnX : (n : ℝ) ≤ X' := le_trans hn.le (le_max_left _ _)
    have h1 : Chebyshev.theta n ≤ Chebyshev.theta X' := Chebyshev.theta_mono hnX
    have h2 := Chebyshev.theta_nonneg (n : ℝ)
    rw [abs_le]
    constructor <;> nlinarith

/-- The key estimate: `|Θ(t) - q/(1-q)| ≤ ε q/(1-q) + C`, `q = e^{-t}`, `t > 0`. -/
lemma cc_Theta_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t →
      |Theta t - Real.exp (-t) / (1 - Real.exp (-t))| ≤
        ε * (Real.exp (-t) / (1 - Real.exp (-t))) + C := by
  obtain ⟨C, hC0, hC⟩ := cc_theta_bound hε
  refine ⟨C, hC0, fun t ht => ?_⟩
  set q := Real.exp (-t) with hqdef
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hq : ‖q‖ < 1 := by rw [Real.norm_of_nonneg hq0.le]; exact hq1
  have h1q : 0 < 1 - q := by linarith
  rw [cc_Theta_eq_tsum, ← hqdef, cc_tsum_A_eq hq0.le hq1]
  set B := ∑' n : ℕ, ccP (n + 1) * q ^ n with hB
  have hBs : HasSum (fun n : ℕ => ccP (n + 1) * q ^ n) B := (cc_summable_P hq0.le hq1).hasSum
  have hN : HasSum (fun n : ℕ => (n : ℝ) * q ^ n) (q / (1 - q) ^ 2) := hasSum_coe_mul_geometric_of_norm_lt_one hq
  have hG : HasSum (fun n : ℕ => q ^ n) (1 - q)⁻¹ := hasSum_geometric_of_lt_one hq0.le hq1
  have hD : HasSum (fun n : ℕ => (ccP (n + 1) - n) * q ^ n) (B - q / (1 - q) ^ 2) := by
    simpa [sub_mul] using hBs.sub hN
  have hE : HasSum (fun n : ℕ => (ε * n + C) * q ^ n) (ε * (q / (1 - q) ^ 2) + C * (1 - q)⁻¹) := by
    simpa [add_mul, mul_assoc] using (hN.mul_left ε).add (hG.mul_left C)
  have hup : B - q / (1 - q) ^ 2 ≤ ε * (q / (1 - q) ^ 2) + C * (1 - q)⁻¹ :=
    hasSum_le (fun n => mul_le_mul_of_nonneg_right (le_abs_self _ |>.trans (hC n)) (pow_nonneg hq0.le n)) hD hE
  have hlo : -(ε * (q / (1 - q) ^ 2) + C * (1 - q)⁻¹) ≤ B - q / (1 - q) ^ 2 := by
    have := hasSum_le (fun n => ?_) hE.neg hD
    · exact this
    · have := (abs_le.1 (hC n)).1
      have hqn := pow_nonneg hq0.le n
      simp only [← neg_mul]
      exact mul_le_mul_of_nonneg_right this hqn
  have key : (1 - q) * B - q / (1 - q) = (1 - q) * (B - q / (1 - q) ^ 2) := by
    field_simp
  rw [key, abs_mul, abs_of_pos h1q]
  have hbd : |B - q / (1 - q) ^ 2| ≤ ε * (q / (1 - q) ^ 2) + C * (1 - q)⁻¹ := abs_le.2 ⟨hlo, hup⟩
  calc (1 - q) * |B - q / (1 - q) ^ 2| ≤ (1 - q) * (ε * (q / (1 - q) ^ 2) + C * (1 - q)⁻¹) :=
        mul_le_mul_of_nonneg_left hbd h1q.le
    _ = ε * (q / (1 - q)) + C := by field_simp

/-- `t e^{-t}/(1 - e^{-t}) → 1` as `t → 0⁺`. -/
lemma cc_tendsto_u :
    Tendsto (fun t : ℝ => t * (Real.exp (-t) / (1 - Real.exp (-t)))) (𝓝[>] 0) (𝓝 1) := by
  have hd := (Real.hasDerivAt_exp 0).tendsto_slope
  rw [Real.exp_zero] at hd
  have hinv := (hd.mono_left (nhdsWithin_mono _ (fun t (ht : 0 < t) => ne_of_gt ht))).inv₀ one_ne_zero
  rw [inv_one] at hinv
  refine hinv.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : (0 : ℝ) < t := ht
  rw [slope_def_field, Real.exp_zero, Real.exp_neg]
  have he : 1 < Real.exp t := Real.one_lt_exp_iff.2 ht'
  have he0 : Real.exp t - 1 ≠ 0 := by linarith
  have he1 : Real.exp t ≠ 0 := (Real.exp_pos t).ne'
  field_simp
  ring

/-- **`tΘ(t) → 1` as `t → 0⁺`** (PNT). Abel summation: `Θ(t) = t ∫_0^∞ θ(x) e^{-xt} dx` for `t > 0`
(Mathlib's `sum_mul_eq_sub_integral_mul` / Abel summation, or a direct Tonelli on `∑_p log p ∫_p^∞ te^{-xt} dx`). PNT+'s
`chebyshev_asymptotic` (`θ ~ id`): for `ε > 0` there is `C_ε` with `|θ(x) - x| ≤ εx + C_ε` for all `x ≥ 0`; with
`t²∫_0^∞ xe^{-xt}dx = 1` and `t²∫_0^∞ e^{-xt}dx = t`, `|tΘ(t) - 1| ≤ ε + C_ε t`. Size: 200–350 lines. -/
theorem tendsto_mul_Theta : Tendsto (fun t : ℝ => t * Theta t) (𝓝[>] 0) (𝓝 1) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  obtain ⟨C, hC0, hC⟩ := cc_Theta_bound (ε := η / 4) (by linarith)
  have hu := cc_tendsto_u
  have h1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), |t * (Real.exp (-t) / (1 - Real.exp (-t))) - 1| < η / 4 := by
    have := Metric.tendsto_nhds.1 hu (η / 4) (by linarith)
    simpa [Real.dist_eq] using this
  have h2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t * (Real.exp (-t) / (1 - Real.exp (-t))) < 2 :=
    hu.eventually (gt_mem_nhds (by norm_num))
  have h3 : ∀ᶠ t in 𝓝[>] (0 : ℝ), C * t < η / 4 := by
    have : Tendsto (fun t : ℝ => C * t) (𝓝[>] 0) (𝓝 0) := by
      exact ((by fun_prop : Continuous fun t : ℝ => C * t).tendsto' 0 0 (by simp)).mono_left
        nhdsWithin_le_nhds
    exact this.eventually (gt_mem_nhds (by linarith))
  filter_upwards [h1, h2, h3, self_mem_nhdsWithin] with t ht1 ht2 ht3 ht
  have ht0 : (0 : ℝ) < t := ht
  rw [Real.dist_eq]
  set u := Real.exp (-t) / (1 - Real.exp (-t)) with hu
  have hb := hC t ht0
  have hsplit : t * Theta t - 1 = t * (Theta t - u) + (t * u - 1) := by ring
  rw [hsplit]
  have hu0 : 0 ≤ t * u := by
    have : 0 ≤ u := div_nonneg (Real.exp_pos _).le (by
      have := Real.exp_lt_one_iff.2 (show -t < 0 by linarith); linarith)
    positivity
  calc |t * (Theta t - u) + (t * u - 1)| ≤ |t * (Theta t - u)| + |t * u - 1| := abs_add_le _ _
    _ = t * |Theta t - u| + |t * u - 1| := by rw [abs_mul, abs_of_pos ht0]
    _ ≤ t * (η / 4 * u + C) + |t * u - 1| := by gcongr
    _ = η / 4 * (t * u) + C * t + |t * u - 1| := by ring
    _ < η / 4 * 2 + η / 4 + η / 4 := by gcongr
    _ = η := by ring

end GoldbachBoundaries.Paper2.M3
