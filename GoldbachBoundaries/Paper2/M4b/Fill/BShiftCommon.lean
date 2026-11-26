import GoldbachBoundaries.Paper2.M4b.Fill.differentiableOn_Ilog

/-!
# Fill, group B: the common frame of the three line moves of `Ilog`

`Ilog_shift` is M1's `verticalIntegral'_eq_add_sum_of_simplePoles` for the integrand `k(z,s)Q(z)Q(L(s)-z)` with the
horizontal tails (`norm_integrand_le_far` with `K = {s}`, `tendsto_hInt_of_bound`) and the integrability on both
lines (`differentiableOn_Ilog`) already discharged; the caller supplies the poles, holomorphy off them, and the
pole conditions.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M4b

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- The integrand is differentiable in `z` at every point off its poles in `1/2 < Re z < Re L(s) - 1/2`. -/
lemma differentiableAt_integrand_slice (hRH : RiemannHypothesis) (A : Aff) (k : ℂ → ℂ → ℂ)
    (hK1 : K1 A k) {z s : ℂ} (hs : s ∈ A.DL) (hz : 1 / 2 < z.re) (hzs : 1 / 2 < (A.app s - z).re)
    (hz1 : z ≠ 1) (hzs1 : A.app s - z ≠ 1) :
    DifferentiableAt ℂ (fun z => k z s * Qcont z * Qcont (A.app s - z)) z :=
  DifferentiableAt.comp (f := fun z : ℂ => (z, s)) z
    (differentiableAt_integrand hRH A k hK1 hs hz hzs hz1 hzs1) (by fun_prop)

/-- `z ↦ k(z, s)` is differentiable at points of `Str(s)`. -/
lemma differentiableAt_k_slice {A : Aff} {k : ℂ → ℂ → ℂ} (hK1 : K1 A k) {z s : ℂ} (hs : s ∈ A.DL)
    (hz0 : 0 < z.re) (hzs : z.re < (A.app s).re) : DifferentiableAt ℂ (fun z => k z s) z :=
  DifferentiableAt.comp (f := fun z : ℂ => (z, s)) z (differentiableAt_k_of_K1B hK1 hs hz0 hzs)
    (by fun_prop)

lemma Ilog_shift (hRH : RiemannHypothesis) (A : Aff) (k : ℂ → ℂ → ℂ) (hK1 : K1 A k) (hK2 : K2 A k)
    {s : ℂ} (hs : s ∈ A.DL) {c c' : ℝ} (hc : 1 / 2 < c) (hcc' : c ≤ c')
    (hc' : c' + 1 / 2 < (A.app s).re) (hc1 : c ≠ 1) (hc'1 : c' ≠ 1) (hcL : (A.app s).re - c ≠ 1)
    (hc'L : (A.app s).re - c' ≠ 1) (S : Finset ℂ) (Af : ℂ → ℂ)
    (hS : ∀ p ∈ S, c < p.re ∧ p.re < c')
    (hf : DifferentiableOn ℂ (fun z => k z s * Qcont z * Qcont (A.app s - z))
      (Icc c c' ×ℂ univ \ (S : Set ℂ)))
    (hpole : ∀ p ∈ S, ((fun z => k z s * Qcont z * Qcont (A.app s - z)) - fun z => Af p / (z - p))
      =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    Ilog A k c' s = ∑ p ∈ S, Af p + Ilog A k c s := by
  obtain ⟨M, Y, hMY⟩ := norm_integrand_le_far hRH A k hK2 isCompact_singleton
    (singleton_subset_iff.mpr hs) hc hcc' (by rintro _ rfl; exact hc')
  have htails := tendsto_hInt_of_bound (f := fun z => k z s * Qcont z * Qcont (A.app s - z)) hcc'
    (fun z h1 h2 h3 => hMY s rfl z h1 h2 h3)
  have hleft := (differentiableOn_Ilog hRH A k hK1 hK2 hc hc1).2 s hs (by linarith) hcL
  have hright := (differentiableOn_Ilog hRH A k hK1 hK2 (by linarith) hc'1).2 s hs hc' hc'L
  exact M1.verticalIntegral'_eq_add_sum_of_simplePoles S Af hcc' hS hf hpole htails.1 htails.2
    hleft hright

end GoldbachBoundaries.Paper2.M4b
