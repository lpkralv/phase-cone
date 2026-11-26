import GoldbachBoundaries.Paper2.M4b.Fill.BShiftCommon
import GoldbachBoundaries.Paper2.M4b.Fill.isBigO_mul_sub_residue

/-!
# Fill: `Ilog_step_one`

`Ilog_shift` with `S = {1}` and `A(1) = k(1,s)Q(L(s)-1)`. Between the lines the only pole is `z = 1`
(`Re(L(s) - z) ≥ Re L(s) - c' > 1`). The pole condition is `isBigO_mul_sub_residue` with `f = Qcont` (order `≥ -1`,
residue `Rcoef 1 = 1` at `1`, M1) and `g z = k(z,s)Q(L(s)-z)`, holomorphic on the open set
`{0 < Re z, 1 < Re(L(s) - z)}` containing `1`, hence analytic at `1`.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M4b

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **Step 2: across `z = 1`** (RH, (K1), (K2)). `1/2 < c < 1 < c' < Re L(s) - 1`: between the lines the only pole is
`z = 1` (`L(s) - 1` has real part `> c'`). M1's `verticalIntegral'_eq_add_sum_of_simplePoles` with `S = {1}`,
`A(1) = k(1,s)Q(L(s)-1)`: the pole condition is `isBigO_mul_sub_residue` with `f = Qcont` (M1's
`meromorphicAt`/`meromorphicOrderAt_Qcont_ge`, `hasResidue_Qcont_Rcoef` at `1`, `Rcoef_one'`) and
`g z = k(z,s)Q(L(s)-z)` analytic at `1` (`differentiableAt_integrand`-type argument for the slice). Tails and
integrability as in `Ilog_eq_of_no_pole`. Size: 150–250 lines. -/
theorem Ilog_step_one (hRH : RiemannHypothesis) (A : Aff) (k : ℂ → ℂ → ℂ) (hK1 : K1 A k)
    (hK2 : K2 A k) {s : ℂ} (hs : s ∈ A.DL) {c c' : ℝ} (hc : 1 / 2 < c) (hc1 : c < 1) (hc'1 : 1 < c')
    (hc' : c' < (A.app s).re - 1) :
    Ilog A k c' s = k 1 s * Qcont (A.app s - 1) + Ilog A k c s := by
  have hf : DifferentiableOn ℂ (fun z => k z s * Qcont z * Qcont (A.app s - z))
      (Icc c c' ×ℂ univ \ (({1} : Finset ℂ) : Set ℂ)) := by
    intro z hz
    obtain ⟨⟨hz1, hz2⟩, -⟩ := Complex.mem_reProdIm.mp hz.1
    have hz1' : z ≠ 1 := by simpa using hz.2
    refine (differentiableAt_integrand_slice hRH A k hK1 hs (by linarith) (by simp; linarith)
      hz1' ?_).differentiableWithinAt
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  -- `g z = k(z,s)Q(L(s)-z)` is analytic at `1`
  set V : Set ℂ := {z | 0 < z.re ∧ 1 < (A.app s - z).re} with hV
  have hVo : IsOpen V := by
    refine (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const (Complex.continuous_re.comp ?_))
    unfold Aff.app; fun_prop
  have h1V : (1 : ℂ) ∈ V := ⟨by simp, by simp; linarith⟩
  have hg : AnalyticAt ℂ (fun z => k z s * Qcont (A.app s - z)) 1 := by
    refine DifferentiableOn.analyticAt (s := V) ?_ (hVo.mem_nhds h1V)
    intro z hz
    obtain ⟨hz0, hzL⟩ := hz
    have hzs : z.re < (A.app s).re := by simp at hzL; linarith
    have hQ : DifferentiableAt ℂ (fun z => Qcont (A.app s - z)) z := by
      refine DifferentiableAt.comp (f := fun z => A.app s - z) z
        (TIdentity.analyticAt_Qcont_of_RH hRH (by linarith) ?_).differentiableAt (by fun_prop)
      intro h; rw [h] at hzL; simp at hzL
    exact ((differentiableAt_k_slice hK1 hs hz0 hzs).mul hQ).differentiableWithinAt
  have hpole1 := isBigO_mul_sub_residue (meromorphicAt_Qcont (a := 1) (by simp))
    (M1.meromorphicOrderAt_Qcont_ge (a := 1) (by simp))
    (M1.hasResidue_Qcont_Rcoef (a := 1) (Or.inl (Or.inl rfl))) hg
  have hpole : ∀ p ∈ ({1} : Finset ℂ),
      ((fun z => k z s * Qcont z * Qcont (A.app s - z)) -
        fun z => (fun _ => k 1 s * Qcont (A.app s - 1)) p / (z - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
    intro p hp
    rw [Finset.mem_singleton] at hp
    subst hp
    refine hpole1.congr' (Eventually.of_forall fun z => ?_) EventuallyEq.rfl
    simp only [Pi.sub_apply, M1.Rcoef_one', mul_one]
    ring
  have := Ilog_shift hRH A k hK1 hK2 hs hc (by linarith) (by linarith) hc1.ne
    (ne_of_gt hc'1) (by linarith) (by linarith) {1} (fun _ => k 1 s * Qcont (A.app s - 1))
    (by intro p hp; rw [Finset.mem_singleton] at hp; subst hp; simp; exact ⟨hc1, hc'1⟩) hf hpole
  simpa using this

end GoldbachBoundaries.Paper2.M4b
