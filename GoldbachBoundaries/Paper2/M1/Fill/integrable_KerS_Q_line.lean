import GoldbachBoundaries.Paper2.M1.Fill.KernelCommon

/-!
# Fill: `integrable_KerS_Q_line` (Group C)

On `Re w = c` the two `Q` factors are bounded by the absolutely convergent sums `∑ log p p^{-c}`,
`∑ log p p^{-(σ - c)}`, and `y ↦ K_s(c + iy)` is integrable (`integrable_KerS_line`).
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M1

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- Absolute convergence of the Mellin–Barnes integral of `T` on the line `Re w = c`, `1 < c < σ - 1`: on the line
both `Q`'s are bounded by `Q(c)`, `Q(σ - c)` (absolutely convergent prime sums), and `K_s` is integrable
(`norm_KerS_mul_pow_le` with `n = 2`). Uses: `norm_KerS_mul_pow_le`. Size: 60–120 lines. -/
theorem integrable_KerS_Q_line {s : ℂ} (hs : 2 < s.re) {c : ℝ} (hc1 : 1 < c)
    (hc2 : c < s.re - 1) :
    Integrable (fun t : ℝ => KerS s (c + t * I) * Q (c + t * I) * Q (s - (c + t * I))) := by
  have hc0 : 0 < c := by linarith
  have hcs : c < s.re := by linarith
  have hK := integrable_KerS_line hc0 hcs
  have hre1 : ∀ t : ℝ, ((c : ℂ) + t * I).re = c := fun t => by simp
  have hre2 : ∀ t : ℝ, (s - ((c : ℂ) + t * I)).re = s.re - c := fun t => by simp
  set A : ℝ := ∑' p : Nat.Primes, ‖(Real.log (p : ℕ) : ℂ) * ((p : ℕ) : ℂ) ^ (-(c : ℂ))‖
  set B : ℝ := ∑' p : Nat.Primes,
    ‖(Real.log (p : ℕ) : ℂ) * ((p : ℕ) : ℂ) ^ (-((s.re - c : ℝ) : ℂ))‖
  have hQ1 : Continuous fun t : ℝ => Q (c + t * I) :=
    continuous_Q_comp (g := fun t : ℝ => (c : ℂ) + t * I) (by fun_prop)
      fun t => by rw [hre1]; exact hc1
  have hQ2 : Continuous fun t : ℝ => Q (s - (c + t * I)) :=
    continuous_Q_comp (g := fun t : ℝ => s - ((c : ℂ) + t * I)) (by fun_prop)
      fun t => by rw [hre2]; linarith
  refine Integrable.mono' (hK.norm.mul_const (A * B))
    (((continuous_KerS_line hc0 hcs).mul hQ1).mul hQ2).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  have h1 : ‖Q (c + t * I)‖ ≤ A := by
    have := norm_Q_le_re (z := (c : ℂ) + t * I) (by rw [hre1]; exact hc1)
    rwa [hre1] at this
  have h2 : ‖Q (s - (c + t * I))‖ ≤ B := by
    have := norm_Q_le_re (z := s - ((c : ℂ) + t * I)) (by rw [hre2]; linarith)
    rwa [hre2] at this
  rw [norm_mul, norm_mul, mul_assoc]
  gcongr

end GoldbachBoundaries.Paper2.M1
