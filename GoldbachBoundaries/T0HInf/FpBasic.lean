import GoldbachBoundaries.T0HInf.Defs
import Mathlib.Analysis.Calculus.SmoothSeries

/-! Positive prime moments give uniform convergence, the derivative, and exponential tails. -/
noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
namespace GoldbachBoundaries.T0HInf
open GoldbachBoundaries Paper2

def primeMomentTerm (k : ℕ) (x : ℝ) (p : Nat.Primes) : ℝ :=
  Real.log (p : ℕ) * ((p : ℕ) : ℝ) ^ k * Real.exp (-((p : ℕ) * x))

def primeMoment (k : ℕ) (x : ℝ) : ℝ := ∑' p : Nat.Primes, primeMomentTerm k x p

lemma primeMomentTerm_nonneg (k : ℕ) (x : ℝ) (p : Nat.Primes) : 0 ≤ primeMomentTerm k x p := by
  unfold primeMomentTerm
  have hlog : 0 ≤ Real.log (p : ℕ) := Real.log_nonneg (by exact_mod_cast p.prop.one_lt.le)
  positivity

lemma summable_primeMomentTerm (k : ℕ) {x : ℝ} (hx : 0 < x) :
    Summable (primeMomentTerm k x) := by
  have h := (Real.summable_pow_mul_exp_neg_nat_mul (k + 1) hx).subtype {n : ℕ | n.Prime}
  apply h.of_nonneg_of_le (primeMomentTerm_nonneg k x)
  intro p
  dsimp [primeMomentTerm]
  calc Real.log (p : ℕ) * ((p : ℕ) : ℝ) ^ k * Real.exp (-((p : ℕ) * x))
      ≤ ((p : ℕ) : ℝ) * ((p : ℕ) : ℝ) ^ k * Real.exp (-((p : ℕ) * x)) := by
        gcongr
        exact Real.log_le_self (Nat.cast_nonneg _)
    _ = _ := by
      change ((p : ℕ) : ℝ) * ((p : ℕ) : ℝ) ^ k * Real.exp (-((p : ℕ) * x)) =
        ((p : ℕ) : ℝ) ^ (k + 1) * Real.exp (-x * (p : ℕ))
      rw [pow_succ]
      ring_nf

lemma continuousOn_primeMoment (k : ℕ) : ContinuousOn (primeMoment k) (Ioi 0) := by
  intro x hx
  have hx2 : 0 < x / 2 := by have := mem_Ioi.mp hx; linarith
  have hcont : ContinuousOn (primeMoment k) (Ioi (x / 2)) := by
    apply continuousOn_tsum (fun p => by unfold primeMomentTerm; fun_prop)
      (summable_primeMomentTerm k hx2)
    intro p y hy
    rw [Real.norm_of_nonneg (primeMomentTerm_nonneg k y p)]
    unfold primeMomentTerm
    have hlog : 0 ≤ Real.log (p : ℕ) := Real.log_nonneg (by exact_mod_cast p.prop.one_lt.le)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    have : x / 2 < y := hy
    have : (0 : ℝ) ≤ (p : ℕ) := Nat.cast_nonneg _
    nlinarith
  exact (hcont.continuousAt (Ioi_mem_nhds (by have := mem_Ioi.mp hx; linarith))).continuousWithinAt

lemma primeMoment_nonneg (k : ℕ) (x : ℝ) : 0 ≤ primeMoment k x :=
  tsum_nonneg (primeMomentTerm_nonneg k x)

lemma primeMoment_tail (k : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    primeMoment k x ≤ (Real.exp 2 * primeMoment k 1) * Real.exp (-2 * x) := by
  have hs1 := summable_primeMomentTerm k (x := 1) one_pos
  have hsx := summable_primeMomentTerm k (x := x) (by linarith)
  have heq : (Real.exp 2 * primeMoment k 1) * Real.exp (-2 * x) =
      ∑' p : Nat.Primes, Real.exp (-2 * x) * (Real.exp 2 * primeMomentTerm k 1 p) := by
    rw [tsum_mul_left, tsum_mul_left]
    unfold primeMoment
    ring
  rw [heq]
  apply Summable.tsum_le_tsum _ hsx ((hs1.mul_left _).mul_left _)
  intro p
  have hp : (2 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.prop.two_le
  have hlog : 0 ≤ Real.log (p : ℕ) := Real.log_nonneg (by linarith)
  unfold primeMomentTerm
  calc Real.log (p : ℕ) * ((p : ℕ) : ℝ) ^ k * Real.exp (-((p : ℕ) * x))
      ≤ Real.log (p : ℕ) * ((p : ℕ) : ℝ) ^ k * Real.exp (-2 * x + 2 - (p : ℕ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.exp_le_exp.mpr
        nlinarith [mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr hx)]
    _ = _ := by rw [sub_eq_add_neg, Real.exp_add, Real.exp_add]; simp only [mul_one]; ring

lemma Fp_eq_primeMoment : Fp = primeMoment 0 := by
  funext x
  simp only [Fp, TIdentity.Fw, primeMoment, primeMomentTerm, pow_zero, mul_one]

lemma FpPrime_eq_primeMoment (x : ℝ) : FpPrime x = -primeMoment 1 x := by
  rw [FpPrime, primeMoment, ← tsum_neg]
  apply tsum_congr
  intro p
  simp only [primeMomentTerm, pow_one]
  ring

theorem hasDerivAt_Fp {x : ℝ} (hx : 0 < x) : HasDerivAt Fp (FpPrime x) x := by
  let f (p : Nat.Primes) (y : ℝ) := Real.log (p : ℕ) * Real.exp (-((p : ℕ) * y))
  let f' (p : Nat.Primes) (y : ℝ) := -primeMomentTerm 1 y p
  have hx2 : 0 < x / 2 := by linarith
  have hder (p : Nat.Primes) (y : ℝ) : HasDerivAt (f p) (f' p y) y := by
    have h := (((hasDerivAt_id y).const_mul ((p : ℕ) : ℝ)).neg.exp).const_mul (Real.log (p : ℕ))
    convert h using 1 <;> dsimp [f, f', primeMomentTerm] <;> ring
  have hbound (p : Nat.Primes) (y : ℝ) (hy : y ∈ Ioi (x / 2)) :
      ‖f' p y‖ ≤ primeMomentTerm 1 (x / 2) p := by
    change ‖-primeMomentTerm 1 y p‖ ≤ _
    rw [norm_neg, Real.norm_of_nonneg (primeMomentTerm_nonneg _ _ _)]
    unfold primeMomentTerm
    have hlog : 0 ≤ Real.log (p : ℕ) := Real.log_nonneg (by exact_mod_cast p.prop.one_lt.le)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    have : x / 2 < y := hy
    have : (0 : ℝ) ≤ (p : ℕ) := Nat.cast_nonneg _
    nlinarith
  have h := hasDerivAt_tsum_of_isPreconnected (summable_primeMomentTerm 1 hx2)
    isOpen_Ioi (convex_Ioi (x / 2)).isPreconnected (fun p y _ => hder p y) hbound
    (show x ∈ Ioi (x / 2) by change x / 2 < x; linarith)
    (TIdentity.summable_log_mul_exp_neg hx) (show x ∈ Ioi (x / 2) by change x / 2 < x; linarith)
  rw [FpPrime_eq_primeMoment]
  convert! h using 1 <;> simp only [f, f', Fp, TIdentity.Fw, tsum_neg, primeMoment]

theorem filteredPrime_basic : ContinuousOn L (Ioi 0) ∧
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 1 ≤ x → ‖L x‖ ≤ K * Real.exp (-x) := by
  have hrepr (x : ℝ) : L x = ((primeMoment 0 x - x * primeMoment 1 x : ℝ) : ℂ) := by
    rw [L, Fp_eq_primeMoment, FpPrime_eq_primeMoment]
    push_cast
    ring
  constructor
  · have hc := (continuousOn_primeMoment 0).sub (continuousOn_id.mul (continuousOn_primeMoment 1))
    have h := Complex.continuous_ofReal.comp_continuousOn hc
    exact h.congr (fun x _ => hrepr x)
  · let K0 := Real.exp 2 * primeMoment 0 1
    let K1 := Real.exp 2 * primeMoment 1 1
    have hK0 : 0 ≤ K0 := mul_nonneg (Real.exp_pos _).le (primeMoment_nonneg _ _)
    have hK1 : 0 ≤ K1 := mul_nonneg (Real.exp_pos _).le (primeMoment_nonneg _ _)
    refine ⟨K0 + K1, by positivity, ?_⟩
    intro x hx
    have hx0 : 0 ≤ x := by linarith
    have hex : x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
    have he : Real.exp x * Real.exp (-2 * x) = Real.exp (-x) := by rw [← Real.exp_add]; congr 1; ring
    have he' : Real.exp (-2 * x) ≤ Real.exp (-x) := Real.exp_le_exp.mpr (by linarith)
    rw [hrepr, Complex.norm_real, Real.norm_eq_abs]
    calc |primeMoment 0 x - x * primeMoment 1 x|
        ≤ primeMoment 0 x + x * primeMoment 1 x := by
          simpa only [abs_of_nonneg (primeMoment_nonneg 0 x),
            abs_of_nonneg (mul_nonneg hx0 (primeMoment_nonneg 1 x))] using
            abs_sub (primeMoment 0 x) (x * primeMoment 1 x)
      _ ≤ K0 * Real.exp (-2 * x) + x * (K1 * Real.exp (-2 * x)) := by
        gcongr
        · exact primeMoment_tail 0 hx
        · exact primeMoment_tail 1 hx
      _ ≤ K0 * Real.exp (-x) + Real.exp x * (K1 * Real.exp (-2 * x)) := by gcongr
      _ = (K0 + K1) * Real.exp (-x) := by rw [mul_left_comm (Real.exp x) K1, he]; ring

end GoldbachBoundaries.T0HInf
