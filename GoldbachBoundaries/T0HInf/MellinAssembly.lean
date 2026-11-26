import GoldbachBoundaries.T0HInf.MomentMellin

/-! The filtered prime sum and its square have the required Mellin transforms. -/
noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
namespace GoldbachBoundaries.T0HInf
open GoldbachBoundaries Paper2

lemma mellin_sub_aux {f g : ℝ → ℂ} {s : ℂ}
    (hf : MellinConvergent f s) (hg : MellinConvergent g s) :
    MellinConvergent (fun x => f x - g x) s ∧
      mellin (fun x => f x - g x) s = mellin f s - mellin g s := by
  simp only [MellinConvergent, smul_eq_mul] at hf hg ⊢
  constructor
  · convert! hf.sub hg using 1
    ext t
    simp [mul_sub]
  · simp only [mellin, smul_eq_mul, mul_sub]
    exact integral_sub hf hg

lemma mellin_add_aux {f g : ℝ → ℂ} {s : ℂ}
    (hf : MellinConvergent f s) (hg : MellinConvergent g s) :
    MellinConvergent (fun x => f x + g x) s ∧
      mellin (fun x => f x + g x) s = mellin f s + mellin g s := by
  simp only [MellinConvergent, smul_eq_mul] at hf hg ⊢
  constructor
  · convert! hf.add hg using 1
    ext t
    simp [mul_add]
  · simp only [mellin, smul_eq_mul, mul_add]
    exact integral_add hf hg

lemma mellin_nat_mul_aux (k : ℕ) {f : ℝ → ℂ} {s : ℂ}
    (hf : MellinConvergent f (s + k)) :
    MellinConvergent (fun x => (x : ℂ) ^ k * f x) s ∧
      mellin (fun x => (x : ℂ) ^ k * f x) s = mellin f (s + k) := by
  simpa only [smul_eq_mul, cpow_natCast] using
    And.intro (MellinConvergent.cpow_smul.mpr hf) (mellin_cpow_smul f s (k : ℂ))

lemma L_mellin_aux {s : ℂ} (hs : 1 < s.re) :
    MellinConvergent L s ∧ mellin L s = (1 - s) * Gamma s * Qcont s := by
  obtain ⟨h0, hv0⟩ := mellin_primeMoment 0 hs
  simp only [Nat.cast_zero, add_zero] at h0 hv0
  obtain ⟨h1, hv1⟩ := mellin_primeMoment 1 hs
  obtain ⟨hi1, hi1val⟩ := mellin_nat_mul_aux 1 h1
  have heq : L = fun x => (primeMoment 0 x : ℂ) - (x : ℂ) ^ 1 * (primeMoment 1 x : ℂ) := by
    ext x
    simp [L, Fp_eq_primeMoment, FpPrime_eq_primeMoment, sub_eq_add_neg]
  rw [heq]
  obtain ⟨hi, hv⟩ := mellin_sub_aux h0 hi1
  refine ⟨hi, ?_⟩
  rw [hv, hi1val, hv0, hv1, Nat.cast_one, Gamma_add_one s (by intro he; subst s; norm_num at hs),
    TIdentity.Qcont_eq_Q_of_one_lt hs]
  ring

lemma pairWeight_T0 {s : ℂ} (p : Nat.Primes × Nat.Primes) :
    pairWeight 0 0 s p - s * pairWeight 0 1 s p - s * pairWeight 1 0 s p +
      (s + 1) * s * pairWeight 1 1 s p = W0log s p.1 p.2 := by
  let n : ℂ := ((p.1 : ℕ) + (p.2 : ℕ) : ℕ)
  have hn : n ≠ 0 := by
    dsimp [n]
    exact_mod_cast (show (p.1 : ℕ) + (p.2 : ℕ) ≠ 0 by have := p.1.prop.pos; omega)
  have h1 : n ^ (-(s + 1)) = n ^ (-s) / n := by
    rw [show -(s + 1) = -s - 1 by ring, cpow_sub _ _ hn, cpow_one]
  have h2 : n ^ (-(s + 1 + 1)) = n ^ (-s) / n ^ 2 := by
    rw [show -(s + 1 + 1) = -s - 2 by ring, cpow_sub _ _ hn, cpow_ofNat]
  simp only [pairWeight, Nat.cast_zero, Nat.cast_one, pow_zero, pow_one, add_zero,
    one_mul, mul_one, W0log, W0]
  change _ - _ * (_ * (_ * n ^ (-(s + 1)))) - _ * (_ * (_ * n ^ (-(s + 1)))) +
    _ * (_ * (_ * n ^ (-(s + 1 + 1)))) = _
  rw [h1, h2]
  simp only [Nat.cast_mul]
  have he : ((p.1 : ℕ) : ℂ) + ((p.2 : ℕ) : ℂ) = n := by simp [n]
  change _ = _ * (n ^ (-s) * (1 - s + s * (s + 1) * _ / n ^ 2))
  field_simp
  linear_combination -(Real.log (p.1 : ℕ) : ℂ) * (Real.log (p.2 : ℕ) : ℂ) * s * n ^ (-s) * n * he

set_option maxHeartbeats 300000 in
lemma t0_mellin_sq_aux {s : ℂ} (hs : 2 < s.re) :
    MellinConvergent (fun x => L x ^ 2) s ∧ mellin (fun x => L x ^ 2) s = Gamma s * T0 s := by
  obtain ⟨h00, hv00⟩ := mellin_pairMoment 0 0 hs
  obtain ⟨h01, hv01⟩ := mellin_pairMoment 0 1 hs
  obtain ⟨h10, hv10⟩ := mellin_pairMoment 1 0 hs
  obtain ⟨h11, hv11⟩ := mellin_pairMoment 1 1 hs
  simp only [Nat.cast_zero, Nat.cast_one, add_zero] at h00 h01 h10 h11 hv00 hv01 hv10 hv11
  have h11' : MellinConvergent (pairMoment 1 1) (s + (2 : ℕ)) := by
    rw [show s + (2 : ℕ) = s + 1 + 1 by push_cast; ring]
    exact h11
  obtain ⟨hi01, hi01val⟩ := mellin_nat_mul_aux 1 (f := pairMoment 0 1) (s := s) (by simpa only [Nat.cast_one] using h01)
  obtain ⟨hi10, hi10val⟩ := mellin_nat_mul_aux 1 (f := pairMoment 1 0) (s := s) (by simpa only [Nat.cast_one] using h10)
  obtain ⟨hi11, hi11val⟩ := mellin_nat_mul_aux 2 (f := pairMoment 1 1) (s := s) h11'
  have heq : (fun x => L x ^ 2) = fun x =>
      pairMoment 0 0 x - (x : ℂ) ^ 1 * pairMoment 0 1 x -
        (x : ℂ) ^ 1 * pairMoment 1 0 x + (x : ℂ) ^ 2 * pairMoment 1 1 x := by
    ext x
    simp only [pairMoment, L, Fp_eq_primeMoment, FpPrime_eq_primeMoment, ofReal_add,
      ofReal_mul, ofReal_neg, pow_one]
    ring
  obtain ⟨ha, hva⟩ := mellin_sub_aux h00 hi01
  obtain ⟨hb, hvb⟩ := mellin_sub_aux ha hi10
  obtain ⟨hc, hvc⟩ := mellin_add_aux hb hi11
  rw [heq]
  refine ⟨hc, ?_⟩
  have hv11' : mellin (pairMoment 1 1) (s + (2 : ℕ)) =
      Gamma (s + 1 + 1) * ∑' p, pairWeight 1 1 s p := by
    rw [show s + (2 : ℕ) = s + 1 + 1 by push_cast; ring]
    exact hv11
  simp only [Nat.cast_one] at hi01val hi10val
  rw [hvc, hvb, hva, hi01val, hi10val, hi11val, hv00, hv01, hv10, hv11']
  have hs0 : s ≠ 0 := by intro h; subst s; norm_num at hs
  have hs1 : s + 1 ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  rw [Gamma_add_one (s + 1) hs1, Gamma_add_one s hs0]
  have hsum (i j : ℕ) := (summable_norm_pairWeight i j hs).of_norm
  have ht : T0 s = (∑' p, pairWeight 0 0 s p) - s * (∑' p, pairWeight 0 1 s p) -
      s * (∑' p, pairWeight 1 0 s p) + (s + 1) * s * (∑' p, pairWeight 1 1 s p) := by
    simp only [T0, Dser, ← tsum_mul_left]
    rw [← (hsum 0 0).tsum_sub ((hsum 0 1).mul_left s),
      ← ((hsum 0 0).sub ((hsum 0 1).mul_left s)).tsum_sub ((hsum 1 0).mul_left s),
      ← (((hsum 0 0).sub ((hsum 0 1).mul_left s)).sub ((hsum 1 0).mul_left s)).tsum_add
        ((hsum 1 1).mul_left ((s + 1) * s))]
    exact tsum_congr (fun p => (pairWeight_T0 p).symm)
  rw [ht]
  ring

end GoldbachBoundaries.T0HInf
