import GoldbachBoundaries.T0HInf.FpBasic

/-! Mellin transforms of positive prime moments, with absolute convergence. -/
noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
namespace GoldbachBoundaries.T0HInf
open GoldbachBoundaries Paper2

lemma prime_moment_cpow (k : ℕ) (p : Nat.Primes) (s : ℂ) :
    (Real.log (p : ℕ) : ℂ) * ((p : ℕ) : ℂ) ^ k / ((p : ℕ) : ℂ) ^ (s + k) =
      (Real.log (p : ℕ) : ℂ) * ((p : ℕ) : ℂ) ^ (-s) := by
  have hp : ((p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast p.prop.ne_zero
  rw [cpow_add _ _ hp, cpow_natCast, cpow_neg]
  field_simp

lemma mellin_primeMoment (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    MellinConvergent (fun x => (primeMoment k x : ℂ)) (s + k) ∧
      mellin (fun x => (primeMoment k x : ℂ)) (s + k) = Gamma (s + k) * Q s := by
  let a (p : Nat.Primes) : ℂ := (Real.log (p : ℕ) : ℂ) * ((p : ℕ) : ℂ) ^ k
  let w (p : Nat.Primes) : ℝ := (p : ℕ)
  have hw (p : Nat.Primes) : 0 < w p := by
    change (0 : ℝ) < (p : ℕ)
    exact_mod_cast p.prop.pos
  have hsk : 0 < (s + k).re := by simp only [add_re, natCast_re]; have := Nat.cast_nonneg (α := ℝ) k; linarith
  have hsum : Summable (fun p => ‖a p‖ / w p ^ (s + k).re) := by
    apply (summable_norm_Q_terms hs).congr
    intro p
    have he := congrArg norm (prime_moment_cpow k p s)
    rw [norm_div, show ((p : ℕ) : ℂ) = ((w p : ℝ) : ℂ) by simp [w],
      norm_cpow_eq_rpow_re_of_pos (hw p)] at he
    exact he.symm
  have hF (x : ℝ) (hx : x ∈ Ioi 0) : HasSum
      (fun p => a p * Real.exp (-w p * x)) (primeMoment k x : ℂ) := by
    have h := (summable_primeMomentTerm k hx).hasSum
    rw [← Complex.hasSum_ofReal] at h
    convert h using 1
    · funext p
      simp [a, w, primeMomentTerm]
    · rfl
  have hc : ContinuousOn (fun x => (primeMoment k x : ℂ)) (Ioi 0) :=
    Complex.continuous_ofReal.comp_continuousOn (continuousOn_primeMoment k)
  obtain ⟨hconv, hval⟩ := TIdentity.mellin_convergent_and_hasSum_of_exp hw hsk hF hc hsum
  refine ⟨hconv, ?_⟩
  rw [← hval.tsum_eq, Q, ← tsum_mul_left]
  apply tsum_congr
  intro p
  have he := prime_moment_cpow k p s
  dsimp [a, w]
  change Gamma (s + k) * ((Real.log (p : ℕ) : ℂ) * ((p : ℕ) : ℂ) ^ k) /
    ((p : ℕ) : ℂ) ^ (s + k) = _
  rw [mul_div_assoc, he]

def pairMoment (i j : ℕ) (x : ℝ) : ℂ := (primeMoment i x * primeMoment j x : ℝ)

def pairWeight (i j : ℕ) (s : ℂ) (p : Nat.Primes × Nat.Primes) : ℂ :=
  (Real.log (p.1 : ℕ) : ℂ) * (Real.log (p.2 : ℕ) : ℂ) *
    (((p.1 : ℕ) : ℂ) ^ i * ((p.2 : ℕ) : ℂ) ^ j *
      (((p.1 : ℕ) + (p.2 : ℕ) : ℕ) : ℂ) ^ (-(s + i + j)))

lemma summable_norm_pairWeight (i j : ℕ) {s : ℂ} (hs : 2 < s.re) :
    Summable (fun p => ‖pairWeight i j s p‖) :=
  (M4b.A_rising_monomial M4b.primeWeight_log i j (s := s) (c := s.re / 2)
    (by linarith) (by linarith)).1

lemma mellin_pairMoment (i j : ℕ) {s : ℂ} (hs : 2 < s.re) :
    MellinConvergent (pairMoment i j) (s + i + j) ∧
      mellin (pairMoment i j) (s + i + j) = Gamma (s + i + j) * ∑' p, pairWeight i j s p := by
  let a (p : Nat.Primes × Nat.Primes) : ℂ :=
    (Real.log (p.1 : ℕ) : ℂ) * (Real.log (p.2 : ℕ) : ℂ) *
      (((p.1 : ℕ) : ℂ) ^ i * ((p.2 : ℕ) : ℂ) ^ j)
  let w (p : Nat.Primes × Nat.Primes) : ℝ := (p.1 : ℕ) + (p.2 : ℕ)
  have hw (p : Nat.Primes × Nat.Primes) : 0 < w p := by
    dsimp [w]
    have hp : (0 : ℝ) < (p.1 : ℕ) := by exact_mod_cast p.1.prop.pos
    have hq : (0 : ℝ) < (p.2 : ℕ) := by exact_mod_cast p.2.prop.pos
    linarith
  have heq (p : Nat.Primes × Nat.Primes) :
      a p / (w p : ℂ) ^ (s + i + j) = pairWeight i j s p := by
    simp only [a, w, pairWeight, cpow_neg, div_eq_mul_inv]
    push_cast
    ring
  have hsum : Summable (fun p => ‖a p‖ / w p ^ (s + i + j).re) := by
    apply (summable_norm_pairWeight i j hs).congr
    intro p
    have h := congrArg norm (heq p)
    rw [norm_div, norm_cpow_eq_rpow_re_of_pos (hw p)] at h
    exact h.symm
  have hsk : 0 < (s + i + j).re := by
    simp only [add_re, natCast_re]
    have := Nat.cast_nonneg (α := ℝ) i
    have := Nat.cast_nonneg (α := ℝ) j
    linarith
  have hF (x : ℝ) (hx : x ∈ Ioi 0) :
      HasSum (fun p => a p * Real.exp (-w p * x)) (pairMoment i j x) := by
    have hi := summable_primeMomentTerm i hx
    have hj := summable_primeMomentTerm j hx
    have h := hi.hasSum.mul hj.hasSum (hi.mul_of_nonneg hj
      (primeMomentTerm_nonneg i x) (primeMomentTerm_nonneg j x))
    rw [← Complex.hasSum_ofReal] at h
    convert h using 1
    · funext p
      dsimp [a, w, primeMomentTerm]
      rw [show -((p.1 : ℕ) + (p.2 : ℕ) : ℝ) * x =
        -((p.1 : ℕ) * x) + -((p.2 : ℕ) * x) by ring, Real.exp_add]
      push_cast
      ring
    · rfl
  have hc : ContinuousOn (pairMoment i j) (Ioi 0) :=
    Complex.continuous_ofReal.comp_continuousOn ((continuousOn_primeMoment i).mul (continuousOn_primeMoment j))
  obtain ⟨hconv, hval⟩ := TIdentity.mellin_convergent_and_hasSum_of_exp hw hsk hF hc hsum
  refine ⟨hconv, ?_⟩
  rw [← hval.tsum_eq, ← tsum_mul_left]
  apply tsum_congr
  intro p
  rw [mul_div_assoc, heq]

end GoldbachBoundaries.T0HInf
