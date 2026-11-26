import GoldbachBoundaries.Paper2.M5.TkLine

/-!
# M5 filler T3: shared helpers for the induction step of Theorem G

Bounds on the moving lines `cPlusK`, `cMinK`, a two-sided form of `TkLine_eq_of_no_pole` (both lines left of `m` and on
the same side of `σ - 1`), and the analyticity of `s ↦ r_m K_s(m)` and of `s ↦ Qcont(s - m)`. They live in the
sub-namespace `FillT3`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5.FillT3

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1 GoldbachBoundaries.Paper2.M5

lemma cPlusK_bounds (m : ℕ) {s : ℂ} (hs : (m : ℝ) + 1 / 2 < s.re) :
    (m : ℝ) - 1 / 2 < cPlusK m s ∧ cPlusK m s < m ∧ cPlusK m s < s.re - 1 := by
  unfold cPlusK
  have h1 := min_le_left (m : ℝ) (s.re - 1)
  have h2 := min_le_right (m : ℝ) (s.re - 1)
  have h3 : (m : ℝ) - 1 / 2 < min (m : ℝ) (s.re - 1) := lt_min (by linarith) (by linarith)
  refine ⟨by linarith, by linarith, by linarith⟩

lemma cPlusK_of_le (m : ℕ) {s : ℂ} (hs : (m : ℝ) + 1 ≤ s.re) : cPlusK m s = (m : ℝ) - 1 / 4 := by
  unfold cPlusK
  rw [min_eq_left (by linarith)]
  ring

lemma cPlusK_of_lt (m : ℕ) {s : ℂ} (hs : s.re < (m : ℝ) + 1) : cPlusK m s = ((m : ℝ) - 1 / 2 + (s.re - 1)) / 2 := by
  unfold cPlusK
  rw [min_eq_right (by linarith)]

lemma cMinK_bounds (m : ℕ) {s : ℂ} (hs : (m : ℝ) < s.re) (hs' : s.re < m + 1) :
    (m : ℝ) - 1 / 2 < cMinK m s ∧ s.re - 1 < cMinK m s ∧ cMinK m s < m ∧ cMinK m s + 1 / 2 < s.re := by
  unfold cMinK
  have h1 := le_max_left ((m : ℝ) - 1 / 2) (s.re - 1)
  have h2 := le_max_right ((m : ℝ) - 1 / 2) (s.re - 1)
  have h3 := min_le_left (m : ℝ) (s.re - 1 / 2)
  have h4 := min_le_right (m : ℝ) (s.re - 1 / 2)
  have h5 : max ((m : ℝ) - 1 / 2) (s.re - 1) < min (m : ℝ) (s.re - 1 / 2) :=
    max_lt (lt_min (by linarith) (by linarith)) (lt_min (by linarith) (by linarith))
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Two lines in `(m - 1/2, m)`, both with `c + 1/2 < σ` and on the same side of `σ - 1`, give the same integral. -/
lemma TkLine_eq_of_lines (hRH : RiemannHypothesis) {m : ℕ} (hm : 1 ≤ m) {F H : ℂ → ℂ} (hP : TkPack m F H)
    {s : ℂ} {a b : ℝ} (ha : (m : ℝ) - 1 / 2 < a) (hb : (m : ℝ) - 1 / 2 < b) (ha' : a + 1 / 2 < s.re)
    (hb' : b + 1 / 2 < s.re) (ham : a < m) (hbm : b < m)
    (hside : (a < s.re - 1 ∧ b < s.re - 1) ∨ (s.re - 1 < a ∧ s.re - 1 < b)) :
    TkLine F a s = TkLine F b s := by
  rcases le_total a b with hab | hab
  · refine (TkLine_eq_of_no_pole hRH hm hP ha hab hb' (fun h => by linarith [h.2]) ?_).symm
    rintro ⟨h1, h2⟩
    rcases hside with h | h <;> linarith [h.1, h.2]
  · refine TkLine_eq_of_no_pole hRH hm hP hb hab ha' (fun h => by linarith [h.2]) ?_
    rintro ⟨h1, h2⟩
    rcases hside with h | h <;> linarith [h.1, h.2]

/-- `Γ` is analytic at a point of positive real part. -/
lemma analyticAt_Gamma_of_re_pos {z : ℂ} (hz : 0 < z.re) : AnalyticAt ℂ Gamma z := by
  have hd : DifferentiableOn ℂ Gamma {w : ℂ | 0 < w.re} := fun w hw =>
    (Complex.differentiableAt_Gamma w fun n h => by
      have : w.re = -(n : ℝ) := by rw [h]; simp
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hw' : 0 < w.re := hw
      linarith).differentiableWithinAt
  exact hd.analyticAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz)

/-- `s ↦ r_m K_s(m)` is analytic on `σ > m` (`m ≥ 1`). -/
lemma analyticAt_rK_KerS {m : ℕ} {s : ℂ} (hs : (m : ℝ) < s.re) :
    AnalyticAt ℂ (fun t => rK m * KerS t m) s := by
  have hs0 : 0 < s.re := lt_of_le_of_lt (by exact_mod_cast (Nat.zero_le m)) hs
  have h1 : AnalyticAt ℂ (fun t => Gamma (t - m)) s := by
    have hre : 0 < (s - m).re := by simp; linarith
    exact (analyticAt_Gamma_of_re_pos hre).comp_of_eq (by fun_prop) rfl
  have h2 : AnalyticAt ℂ Gamma s := analyticAt_Gamma_of_re_pos hs0
  have h3 : Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs0
  unfold KerS
  exact analyticAt_const.mul ((analyticAt_const.mul h1).div h2 h3)

/-- `s ↦ Qcont(s - m)` is meromorphic on `σ > m`. -/
lemma meromorphicAt_Qcont_sub {m : ℕ} {s : ℂ} (hs : (m : ℝ) < s.re) :
    MeromorphicAt (fun t => Qcont (t - m)) s := by
  have hre : 0 < (s - m).re := by simp; linarith
  exact MeromorphicAt.comp_analyticAt (g := fun t : ℂ => t - m) (meromorphicAt_Qcont hre) (by fun_prop)

/-- `r_m K_s(m) = Γ(s - m)/Γ(s)` (`m ≥ 1`). -/
lemma rK_mul_KerS {m : ℕ} (hm : 1 ≤ m) (s : ℂ) : rK m * KerS s m = Gamma (s - m) / Gamma s := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hG : Gamma ((n + 1 : ℕ) : ℂ) = (n.factorial : ℂ) := by
    rw [Nat.cast_succ, Complex.Gamma_nat_eq_factorial]
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  unfold rK KerS
  rw [hG, show n + 1 - 1 = n by omega]
  field_simp

end GoldbachBoundaries.Paper2.M5.FillT3
