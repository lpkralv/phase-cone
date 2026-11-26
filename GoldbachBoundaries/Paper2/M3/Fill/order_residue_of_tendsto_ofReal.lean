import GoldbachBoundaries.Paper2.M3.Real

noncomputable section
open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory
namespace GoldbachBoundaries.Paper2.M3
open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **A real one-sided limit determines a simple pole** (general complex analysis). If `meromorphicOrderAt f a = ⊤`,
`f = 0` on a punctured neighbourhood and the limit is `0 ≠ c`. Otherwise `f = (z - a)^n g` near `a` with `g` analytic,
`g(a) ≠ 0` (`MeromorphicAt.meromorphicOrderAt_eq_int_iff`); `(x - a)^{n+1}g(x) → c ≠ 0` along real `x ↓ a` forces
`n + 1 = 0` (it tends to `0` if `n + 1 > 0` and its norm to `∞` if `n + 1 < 0`), then `g(a) = c` by continuity, and
`(z - a)f(z) = g(z) → c` on `𝓝[≠] a`. Size: 100–200 lines. -/
theorem order_residue_of_tendsto_ofReal {f : ℂ → ℂ} {a : ℝ} {c : ℂ} (hf : MeromorphicAt f a) (hc : c ≠ 0)
    (h : Tendsto (fun x : ℝ => ((x : ℂ) - a) * f x) (𝓝[>] a) (𝓝 c)) :
    meromorphicOrderAt f a = -1 ∧ HasResidue f a c := by
  set g : ℂ → ℂ := fun z => (z - a) * f z with hgdef
  have hlin : MeromorphicAt (fun z : ℂ => z - a) a := by fun_prop
  have hg : MeromorphicAt g a := hlin.mul hf
  -- the real approach `x ↓ a` maps into the punctured neighbourhood of `a`
  have hι : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[>] a) (𝓝[≠] (a : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact (Complex.continuous_ofReal.tendsto a).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      simp only [mem_compl_iff, mem_singleton_iff, Complex.ofReal_inj]
      exact ne_of_gt hx
  have hgc : Tendsto (g ∘ fun x : ℝ => (x : ℂ)) (𝓝[>] a) (𝓝 c) := h
  -- the order of `g` is not negative
  have hnn : 0 ≤ meromorphicOrderAt g a := by
    by_contra hneg
    have hneg' : meromorphicOrderAt g a < 0 := lt_of_not_ge hneg
    have hcob := (tendsto_cobounded_of_meromorphicOrderAt_neg hneg').comp hι
    exact hgc.not_tendsto (disjoint_nhds_cobounded c) hcob
  obtain ⟨L, hL⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg hg hnn
  have hLc : L = c := tendsto_nhds_unique (hL.comp hι) hgc
  subst hLc
  have hres : HasResidue f a L := hL
  have hg0 : meromorphicOrderAt g a = 0 :=
    (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero hg).1 ⟨L, hc, hL⟩
  refine ⟨?_, hres⟩
  have hmul : meromorphicOrderAt g a = 1 + meromorphicOrderAt f a := by
    rw [hgdef, fun_meromorphicOrderAt_mul hlin hf, meromorphicOrderAt_id_sub_const]
  rw [hg0] at hmul
  cases hfo : meromorphicOrderAt f a with
  | top => rw [hfo] at hmul; simp at hmul
  | coe n =>
    rw [hfo] at hmul
    have : (0 : ℤ) = 1 + n := by exact_mod_cast hmul
    have hn : n = -1 := by omega
    simp [hn]

end GoldbachBoundaries.Paper2.M3
