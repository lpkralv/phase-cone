import GoldbachBoundaries.Paper2.M4a.Defs
import GoldbachBoundaries.SigmaFinite
import GoldbachBoundaries.Density

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
namespace GoldbachBoundaries.Paper2.M4a
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

private lemma A_scaled_inj (hRH : RiemannHypothesis) {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    {ρ σ : ℂ} (hρ : ρ ∈ NontrivialZeros) (hσ : σ ∈ NontrivialZeros)
    (h : ρ / (n : ℂ) = σ / (m : ℂ)) : n = m ∧ ρ = σ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hmR : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hre := congrArg Complex.re h
  simp only [Complex.div_natCast_re, sigmaFinite_re_eq_half hRH hρ,
    sigmaFinite_re_eq_half hRH hσ] at hre
  have hnm : n = m := by
    have := (div_eq_div_iff hnR.ne' hmR.ne').mp hre
    have : (n : ℝ) = m := by linarith
    exact_mod_cast this
  subst m
  exact ⟨rfl, (div_left_inj' (by exact_mod_cast hnR.ne' : (n : ℂ) ≠ 0)).mp h⟩

/-- **Scaled zeros near `iy`** (RH). Paper 1's `lem_density y hε` gives infinitely many pairs `(n, ρ)`, `n` prime,
with `‖ρ/n - iy‖ < ε`. Under RH the map `(n, ρ) ↦ ρ/n` is injective on them (`Re(ρ/n) = 1/(2n)` fixes `n`, then `ρ`;
paper 1's `catalogue_zero_inj` after adding `1`), so the image is infinite (`Set.Infinite.image`). For `0 ≤ y`: if
`y > 0`, use `ε' = min ε y`, so `Im(ρ/n) > y - ε' ≥ 0`, hence `γ > 0`; if `y = 0`, fix a zero with `γ > 0` (paper 1's
`exists_nontrivialZero_im_gt`) and let `n` run over the primes `> ‖ρ‖/ε` (`Nat.exists_infinite_primes`); the points
`ρ/n` are distinct. Size: 100–200 lines. -/
theorem infinite_scaledZeros_near (hRH : RiemannHypothesis) (y : ℝ) {ε : ℝ} (hε : 0 < ε) :
    {u : ℂ | (∃ ρ ∈ NontrivialZeros, ∃ n : ℕ, n.Prime ∧ u = ρ / (n : ℂ)) ∧ ‖u - (y : ℂ) * I‖ < ε}.Infinite ∧
      (0 ≤ y → {u : ℂ | (∃ ρ ∈ NontrivialZeros, 0 < ρ.im ∧ ∃ n : ℕ, n.Prime ∧ u = ρ / (n : ℂ)) ∧
        ‖u - (y : ℂ) * I‖ < ε}.Infinite) := by
  have key (v : ℝ) {δ : ℝ} (hδ : 0 < δ) :
      {u : ℂ | (∃ ρ ∈ NontrivialZeros, ∃ n : ℕ, n.Prime ∧ u = ρ / (n : ℂ)) ∧
        ‖u - (v : ℂ) * I‖ < δ}.Infinite := by
    have hi : Set.InjOn (fun p : ℕ × ℂ => p.2 / (p.1 : ℂ))
        {p : ℕ × ℂ | p.1.Prime ∧ p.2 ∈ NontrivialZeros ∧
          ‖p.2 / (p.1 : ℂ) - (v : ℂ) * I‖ < δ} := by
      intro p hp q hq heq
      obtain ⟨hn, hρ⟩ := A_scaled_inj hRH hp.1.one_lt.le hq.1.one_lt.le hp.2.1 hq.2.1 heq
      exact Prod.ext hn hρ
    refine ((lem_density_proof v hδ).image hi).mono ?_
    rintro u ⟨⟨n, ρ⟩, hp, rfl⟩
    exact ⟨⟨ρ, hp.2.1, n, hp.1, rfl⟩, hp.2.2⟩
  refine ⟨key y hε, fun hy => ?_⟩
  refine (key (y + ε / 2) (half_pos hε)).mono ?_
  rintro u ⟨⟨ρ, hρ, n, hn, rfl⟩, hdist⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn.pos
  have him := (Complex.abs_im_le_norm (ρ / (n : ℂ) - ((y + ε / 2 : ℝ) : ℂ) * I)).trans_lt hdist
  simp only [sub_im, Complex.div_natCast_im, mul_im, ofReal_re, I_im, mul_one,
    ofReal_im, I_re, mul_zero, add_zero] at him
  have hγ : 0 < ρ.im := by
    have := (abs_lt.mp him).1
    have : 0 < ρ.im / (n : ℝ) := by linarith
    exact (div_pos_iff_of_pos_right hnR).mp this
  refine ⟨⟨ρ, hρ, hγ, n, hn, rfl⟩, ?_⟩
  have heq : ρ / (n : ℂ) - (y : ℂ) * I =
      (ρ / (n : ℂ) - ((y + ε / 2 : ℝ) : ℂ) * I) + ((ε / 2 : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [heq]
  have hnorm : ‖((ε / 2 : ℝ) : ℂ) * I‖ = ε / 2 := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (half_pos hε)]
  have := norm_add_le (ρ / (n : ℂ) - ((y + ε / 2 : ℝ) : ℂ) * I) (((ε / 2 : ℝ) : ℂ) * I)
  rw [hnorm] at this
  linarith

end GoldbachBoundaries.Paper2.M4a
