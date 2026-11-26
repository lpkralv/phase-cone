import GoldbachBoundaries.Paper2.M5.Qleft
import GoldbachBoundaries.Paper2.M5.Fill.«tsum_add_prime_eq_verticalIntegral'»

/-! Filler for `Tk_succ_eq_verticalIntegral'` (M5, group T1): split the last prime off a `(k+1)`-tuple
(`Fin.cons`) and apply `tsum_add_prime_eq_verticalIntegral'` with `a = ∏ log p_i`, `n = ∑ p_i`. -/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

namespace FillT1

/-- `(p, q) ↦ Fin.cons q p`: a `(k+1)`-tuple of primes is a `k`-tuple and one more prime. -/
def consEquivT (k : ℕ) : (Fin k → Nat.Primes) × Nat.Primes ≃ (Fin (k + 1) → Nat.Primes) where
  toFun ip := Fin.cons ip.2 ip.1
  invFun p := (Fin.tail p, p 0)
  left_inv ip := by simp
  right_inv p := by simp

/-- The summand of `T_k`. -/
def tkTerm (k : ℕ) (s : ℂ) (p : Fin k → Nat.Primes) : ℂ :=
  (∏ i, (Real.log (p i : ℕ) : ℂ)) * (((∑ i, (p i : ℕ) : ℕ) : ℂ)) ^ (-s)

lemma tkTerm_cons (k : ℕ) (s : ℂ) (ip : (Fin k → Nat.Primes) × Nat.Primes) :
    tkTerm (k + 1) s (consEquivT k ip) =
      (∏ i, (Real.log (ip.1 i : ℕ) : ℂ)) * (Real.log (ip.2 : ℕ) : ℂ) *
        ((((∑ i, (ip.1 i : ℕ)) + (ip.2 : ℕ) : ℕ) : ℂ)) ^ (-s) := by
  simp only [tkTerm, consEquivT, Equiv.coe_fn_mk, Fin.prod_univ_succ, Fin.sum_univ_succ, Fin.cons_zero,
    Fin.cons_succ]
  rw [add_comm ((ip.2 : ℕ)) _]
  ring

lemma one_le_sum_primes {k : ℕ} (hk : 1 ≤ k) (p : Fin k → Nat.Primes) : 1 ≤ ∑ i, (p i : ℕ) := by
  have h0 : (p ⟨0, hk⟩ : ℕ) ≤ ∑ i, (p i : ℕ) :=
    Finset.single_le_sum (f := fun i => (p i : ℕ)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
  exact le_trans (p ⟨0, hk⟩).prop.one_lt.le h0

lemma norm_tkTerm (k : ℕ) {w : ℂ} (p : Fin k → Nat.Primes) (hp : 1 ≤ ∑ i, (p i : ℕ)) :
    ‖tkTerm k w p‖ = ‖∏ i, (Real.log (p i : ℕ) : ℂ)‖ * ((∑ i, (p i : ℕ) : ℕ) : ℝ) ^ (-w.re) := by
  rw [tkTerm, norm_mul, norm_natCast_cpow_of_pos hp]
  simp

end FillT1

open FillT1 in
theorem Tk_succ_eq_verticalIntegral' {k : ℕ} (hk : 1 ≤ k) :
    (∀ w : ℂ, (k : ℝ) < w.re → Summable (fun p : Fin k → Nat.Primes =>
      ‖(∏ i, (Real.log (p i : ℕ) : ℂ)) * (((∑ i, (p i : ℕ) : ℕ) : ℂ)) ^ (-w)‖)) ∧
    ∀ s : ℂ, ∀ c : ℝ, (k : ℝ) < c → c < s.re - 1 →
      Tk (k + 1) s = VerticalIntegral' (fun w => KerS s w * Tk k w * Q (s - w)) c := by
  -- the step from the absolute convergence at level `k` (on `Re > k`) to the Mellin–Barnes data
  have hstep : ∀ k : ℕ, 1 ≤ k →
      (∀ w : ℂ, (k : ℝ) < w.re → Summable (fun p : Fin k → Nat.Primes => ‖tkTerm k w p‖)) →
      ∀ s : ℂ, ∀ c : ℝ, (k : ℝ) < c → c < s.re - 1 →
        Summable (fun p : Fin (k + 1) → Nat.Primes => ‖tkTerm (k + 1) s p‖) ∧
        Tk (k + 1) s = VerticalIntegral' (fun w => KerS s w * Tk k w * Q (s - w)) c := by
    intro k hk hsum s c hkc hcs
    have hc0 : 0 < c := lt_of_le_of_lt (by exact_mod_cast (Nat.zero_le k)) hkc
    have ha : Summable fun p : Fin k → Nat.Primes =>
        ‖∏ i, (Real.log (p i : ℕ) : ℂ)‖ * ((∑ i, (p i : ℕ) : ℕ) : ℝ) ^ (-c) := by
      refine (hsum (c : ℂ) (by simpa using hkc)).congr fun p => ?_
      rw [norm_tkTerm k p (one_le_sum_primes hk p)]
      simp
    obtain ⟨h1, -, h3⟩ := tsum_add_prime_eq_verticalIntegral'
      (fun p : Fin k → Nat.Primes => ∏ i, (Real.log (p i : ℕ) : ℂ))
      (fun p : Fin k → Nat.Primes => ∑ i, (p i : ℕ)) (one_le_sum_primes hk) hc0 hcs ha
    refine ⟨?_, ?_⟩
    · rw [← (consEquivT k).summable_iff]
      refine h1.congr fun ip => ?_
      simp only [Function.comp_apply, tkTerm_cons]
    · have hT : Tk (k + 1) s = ∑' p, tkTerm (k + 1) s p := rfl
      rw [hT, ← (consEquivT k).tsum_eq]
      simp only [tkTerm_cons]
      rw [h3]
      rfl
  -- absolute convergence at every level `k ≥ 1`
  have hconv : ∀ k : ℕ, 1 ≤ k →
      ∀ w : ℂ, (k : ℝ) < w.re → Summable (fun p : Fin k → Nat.Primes => ‖tkTerm k w p‖) := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
      intro w hw
      rw [← (Equiv.funUnique (Fin 1) Nat.Primes).symm.summable_iff]
      refine (summable_norm_Q_terms (z := w) (by simpa using hw)).congr fun q => ?_
      simp [tkTerm, Equiv.funUnique]
    | succ k hk ih =>
      intro w hw
      have hw' : (k : ℝ) + 1 < w.re := by push_cast at hw; linarith
      exact (hstep k hk ih w (((k : ℝ) + (w.re - 1)) / 2) (by linarith) (by linarith)).1
  refine ⟨fun w hw => hconv k hk w hw, fun s c hkc hcs => (hstep k hk (hconv k hk) s c hkc hcs).2⟩

end GoldbachBoundaries.Paper2.M5
