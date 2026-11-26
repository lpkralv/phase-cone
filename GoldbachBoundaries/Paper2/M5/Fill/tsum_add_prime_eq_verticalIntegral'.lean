import GoldbachBoundaries.Paper2.M5.Qleft
import GoldbachBoundaries.Paper2.M1.Fill.KernelCommon
import GoldbachBoundaries.Paper2.M1.Fill.«one_add_cpow_neg_eq_verticalIntegral'»

/-! Filler for `tsum_add_prime_eq_verticalIntegral'` (M5, group T1). Adapted from M1's
`Fill/T_eq_verticalIntegral'_KerS.lean` and M4b's `Fill/tsum_eq_verticalIntegral'_of_mellin.lean` (left prime sum
replaced by a general absolutely convergent Dirichlet series `∑ a_i n_i^{-w}`). -/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

namespace FillT1

/-- `(n/p)^{-w} = n^{-w} p^{w}` for `n ≥ 0` and a prime `p`. -/
lemma div_cpow_nat_prime (n : ℕ) (q : Nat.Primes) (w : ℂ) :
    ((((n : ℝ) / ((q : ℕ) : ℝ) : ℝ)) : ℂ) ^ (-w) = ((n : ℂ)) ^ (-w) * ((q : ℕ) : ℂ) ^ w := by
  have hp : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  have hq : (0 : ℝ) < ((q : ℕ) : ℝ) := by exact_mod_cast q.prop.pos
  have harg : (((q : ℕ) : ℝ) : ℂ).arg ≠ Real.pi := by
    rw [arg_ofReal_of_nonneg hq.le]; exact Real.pi_pos.ne
  rw [div_eq_mul_inv, ofReal_mul, mul_cpow_ofReal_nonneg hp (inv_nonneg.mpr hq.le), ofReal_inv,
    inv_cpow _ _ harg, ← cpow_neg, neg_neg, ofReal_natCast, ofReal_natCast]

/-- `(n + p)^{-s} = p^{-s} (1 + n/p)^{-s}`. -/
lemma add_cpow_nat_prime (n : ℕ) (q : Nat.Primes) (s : ℂ) :
    (((n + (q : ℕ) : ℕ) : ℂ)) ^ (-s) =
      ((q : ℕ) : ℂ) ^ (-s) * ((1 + (n : ℝ) / ((q : ℕ) : ℝ) : ℝ) : ℂ) ^ (-s) := by
  have hq : (0 : ℝ) < ((q : ℕ) : ℝ) := by exact_mod_cast q.prop.pos
  have h1 : (0 : ℝ) ≤ 1 + (n : ℝ) / ((q : ℕ) : ℝ) := by positivity
  have hq' : ((q : ℕ) : ℂ) ≠ 0 := by exact_mod_cast q.prop.ne_zero
  have he : (((n + (q : ℕ) : ℕ) : ℂ)) =
      ((((q : ℕ) : ℝ) * (1 + (n : ℝ) / ((q : ℕ) : ℝ)) : ℝ) : ℂ) := by
    push_cast
    field_simp
    ring
  rw [he, ofReal_mul, mul_cpow_ofReal_nonneg hq.le h1, ofReal_natCast]

end FillT1

open FillT1 in
theorem tsum_add_prime_eq_verticalIntegral' {ι : Type*} [Countable ι] (a : ι → ℂ) (n : ι → ℕ)
    (hn : ∀ i, 1 ≤ n i) {s : ℂ} {c : ℝ} (hc0 : 0 < c) (hc : c < s.re - 1)
    (ha : Summable fun i => ‖a i‖ * (n i : ℝ) ^ (-c)) :
    Summable (fun ip : ι × Nat.Primes =>
      ‖a ip.1 * (Real.log (ip.2 : ℕ) : ℂ) * (((n ip.1 + (ip.2 : ℕ) : ℕ) : ℂ)) ^ (-s)‖) ∧
    Integrable (fun y : ℝ => KerS s (c + y * I) * (∑' i, a i * ((n i : ℕ) : ℂ) ^ (-(c + y * I))) *
      Q (s - (c + y * I))) ∧
    ∑' ip : ι × Nat.Primes, a ip.1 * (Real.log (ip.2 : ℕ) : ℂ) * (((n ip.1 + (ip.2 : ℕ) : ℕ) : ℂ)) ^ (-s) =
      VerticalIntegral' (fun w => KerS s w * (∑' i, a i * ((n i : ℕ) : ℂ) ^ (-w)) * Q (s - w)) c := by
  have hcs : c < s.re := by linarith
  have hre1 : ∀ y : ℝ, ((c : ℂ) + y * I).re = c := fun y => by simp
  have hre2 : ∀ y : ℝ, (s - ((c : ℂ) + y * I)).re = s.re - c := fun y => by simp
  have hnpos : ∀ i, 0 < n i := fun i => hn i
  -- the two factors
  set A : ι → ℂ → ℂ := fun i w => a i * ((n i : ℕ) : ℂ) ^ (-w) with hA
  set B : Nat.Primes → ℂ → ℂ := fun p w => (Real.log (p : ℕ) : ℂ) * ((p : ℕ) : ℂ) ^ (-w) with hB
  -- the `(i, p)` integrand on the line
  set F : ι × Nat.Primes → ℝ → ℂ := fun ip y =>
    KerS s (c + y * I) * (A ip.1 (c + y * I) * B ip.2 (s - (c + y * I))) with hF
  have hFeq : ∀ ip : ι × Nat.Primes, ∀ y : ℝ,
      F ip y = (a ip.1 * (Real.log (ip.2 : ℕ) : ℂ) * ((ip.2 : ℕ) : ℂ) ^ (-s)) *
        (KerS s (c + y * I) *
          ((((n ip.1 : ℝ) / ((ip.2 : ℕ) : ℝ) : ℝ)) : ℂ) ^ (-((c : ℂ) + y * I))) := by
    intro ip y
    have hq0 : ((ip.2 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast ip.2.prop.ne_zero
    rw [div_cpow_nat_prime, hF]
    simp only [hA, hB]
    have hsplit : ((ip.2 : ℕ) : ℂ) ^ (-(s - ((c : ℂ) + y * I))) =
        ((ip.2 : ℕ) : ℂ) ^ (-s) * ((ip.2 : ℕ) : ℂ) ^ ((c : ℂ) + y * I) := by
      rw [← cpow_add _ _ hq0]; congr 1; ring
    rw [hsplit]
    ring
  have htpos : ∀ ip : ι × Nat.Primes, 0 < (n ip.1 : ℝ) / ((ip.2 : ℕ) : ℝ) :=
    fun ip => div_pos (by exact_mod_cast hnpos ip.1) (by exact_mod_cast ip.2.prop.pos)
  have hFint : ∀ ip : ι × Nat.Primes, Integrable (F ip) := by
    intro ip
    have h := (one_add_cpow_neg_eq_verticalIntegral' hc0 hcs (htpos ip)).1
    rw [show F ip = _ from funext (hFeq ip)]
    exact h.const_mul _
  have hterm : ∀ ip : ι × Nat.Primes,
      a ip.1 * (Real.log (ip.2 : ℕ) : ℂ) * (((n ip.1 + (ip.2 : ℕ) : ℕ) : ℂ)) ^ (-s) =
      (1 / (2 * Real.pi * I)) * (I * ∫ y : ℝ, F ip y) := by
    intro ip
    have h := (one_add_cpow_neg_eq_verticalIntegral' hc0 hcs (htpos ip)).2
    rw [add_cpow_nat_prime, h, VerticalIntegral', VerticalIntegral, smul_eq_mul, smul_eq_mul]
    simp_rw [hFeq ip]
    rw [integral_const_mul]
    ring
  -- summability of the `L¹` norms
  set α : ι → ℝ := fun i => ‖a i‖ * (n i : ℝ) ^ (-c) with hα
  set β : Nat.Primes → ℝ := fun q => ‖B q ((s.re - c : ℝ) : ℂ)‖ with hβ
  have hβsum : Summable β := summable_norm_Q_terms (z := ((s.re - c : ℝ) : ℂ)) (by simp; linarith)
  have hnormA : ∀ i, ∀ w : ℂ, ‖A i w‖ = ‖a i‖ * (n i : ℝ) ^ (-w.re) := by
    intro i w
    simp only [hA]
    rw [norm_mul, norm_natCast_cpow_of_pos (hnpos i)]
    simp
  have hnormF : ∀ ip : ι × Nat.Primes, ∀ y : ℝ,
      ‖F ip y‖ = ‖KerS s (c + y * I)‖ * (α ip.1 * β ip.2) := by
    intro ip y
    rw [hF]
    dsimp only
    rw [norm_mul, norm_mul, hnormA, hre1]
    simp only [hα, hβ, hB]
    rw [norm_Q_term_eq_re ip.2 (s - ((c : ℂ) + y * I)), hre2]
  have hab : Summable fun ip : ι × Nat.Primes => α ip.1 * β ip.2 :=
    ha.mul_of_nonneg hβsum (fun _ => by positivity) (fun _ => norm_nonneg _)
  have hK := integrable_KerS_line hc0 hcs
  have hsumF : Summable fun ip : ι × Nat.Primes => ∫ y : ℝ, ‖F ip y‖ := by
    refine (hab.mul_left (∫ y : ℝ, ‖KerS s (c + y * I)‖)).congr fun ip => ?_
    simp_rw [hnormF ip]
    rw [integral_mul_const]
  have hswap := integral_tsum_of_summable_integral_norm hFint hsumF
  have hAsum : ∀ y : ℝ, Summable fun i => ‖A i (c + y * I)‖ := by
    intro y
    refine ha.congr fun i => ?_
    rw [hnormA, hre1]
  have hinner : ∀ y : ℝ, ∑' ip : ι × Nat.Primes, F ip y =
      KerS s (c + y * I) * (∑' i, a i * ((n i : ℕ) : ℂ) ^ (-(c + y * I))) * Q (s - (c + y * I)) := by
    intro y
    rw [hF]
    simp only
    rw [tsum_mul_left, mul_assoc]
    congr 1
    rw [Q]
    refine (tsum_mul_tsum_of_summable_norm (f := fun i => A i (c + y * I))
      (g := fun q => B q (s - (c + y * I))) (hAsum y) ?_).symm
    exact summable_norm_Q_terms (by rw [hre2]; linarith)
  have hpoint : ∀ y : ℝ, Summable (fun ip : ι × Nat.Primes => ‖F ip y‖) := by
    intro y
    exact (hab.mul_left ‖KerS s (c + y * I)‖).congr fun ip => (hnormF ip y).symm
  have hmeas : AEStronglyMeasurable (fun y : ℝ => ∑' ip, F ip y) :=
    AEStronglyMeasurable.tsum (fun ip => (hFint ip).aestronglyMeasurable)
  have hint : Integrable (fun y : ℝ => ∑' ip, F ip y) := by
    refine Integrable.mono' (hK.norm.mul_const (∑' ip : ι × Nat.Primes, α ip.1 * β ip.2)) hmeas ?_
    apply Eventually.of_forall
    intro y
    calc ‖∑' ip, F ip y‖ ≤ ∑' ip, ‖F ip y‖ := norm_tsum_le_tsum_norm (hpoint y)
      _ = ‖KerS s (c + y * I)‖ * ∑' ip : ι × Nat.Primes, α ip.1 * β ip.2 := by
        simp_rw [hnormF]
        rw [tsum_mul_left]
  refine ⟨?_, ?_, ?_⟩
  · have hnormI : Summable (fun ip => ‖∫ y : ℝ, F ip y‖) :=
      hsumF.of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => norm_integral_le_integral_norm _)
    simp_rw [hterm]
    simpa only [norm_mul, mul_assoc] using
      (hnormI.mul_left (‖(1 / (2 * Real.pi * I) : ℂ)‖ * ‖I‖))
  · simpa only [hinner] using hint
  · simp_rw [hterm]
    rw [tsum_mul_left, tsum_mul_left, hswap]
    simp_rw [hinner]
    rfl

end GoldbachBoundaries.Paper2.M5
