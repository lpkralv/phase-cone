import GoldbachBoundaries.Paper2.M4b.Fill.BShiftCommon

/-!
# Fill: `Ilog_step_sub_one`

`Ilog_shift` from `c` to `c'` with `S = {z_*}`, `z_* = L(s) - 1`, and `A(z_*) = -k(z_*,s)Q(z_*)`. Between the lines
the only pole is `z_*` (`Re z ≤ c' < 1`, so `z ≠ 1`). Near `z_*`: `(w - 1)Q(w) = H(w)` near `w = 1` with `H`
differentiable at `1`, `H(1) = Rcoef 1 = 1` (`exists_numerator_of_simplePole` with M1's facts at `1`); with
`w = L(s) - z`, `(z - z_*)Q(L(s) - z) = -H(L(s) - z)`, so `isBigO_mul_sub_of_numerator` with `g z = k(z,s)Q(z)`
(differentiable at `z_*`: `Re z_* > 1/2`, `z_* ≠ 1`) gives the pole condition with residue `-g(z_*)`.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M4b

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **Step 3: across `z = L(s) - 1`** (RH, (K1), (K2)). `1/2 < c < Re L(s) - 1 < c' < 1`, `c' + 1/2 < Re L(s)`: between
the lines the only pole is `z_* = L(s) - 1` (`z = 1` is to the right of `c'`). Near `z_*`,
`Q(L(s) - z) = Qcont(1 - (z - z_*)) = -1/(z - z_*) + O(1)`: `isBigO_mul_sub_residue` with `f(z) = Qcont(L(s) - z)`
(order `≥ -1` and residue `-R_1 = -1` at `z_*`, from M1's facts at `1` composed with `z ↦ L(s) - z`) and
`g(z) = k(z,s)Q(z)`, analytic at `z_*` (`Re z_* > 1/2`, `z_* ≠ 1`). So
`I_{c'}(s) = -k(z_*,s)Q(z_*) + I_c(s)`. Tails and integrability as in `Ilog_eq_of_no_pole`. Size: 150–250 lines. -/
theorem Ilog_step_sub_one (hRH : RiemannHypothesis) (A : Aff) (k : ℂ → ℂ → ℂ) (hK1 : K1 A k)
    (hK2 : K2 A k) {s : ℂ} (hs : s ∈ A.DL) {c c' : ℝ} (hc : 1 / 2 < c) (hcx : c < (A.app s).re - 1)
    (hxc' : (A.app s).re - 1 < c') (hc'1 : c' < 1) (hc' : c' + 1 / 2 < (A.app s).re) :
    Ilog A k c s = Ilog A k c' s + k (A.app s - 1) s * Qcont (A.app s - 1) := by
  set zs : ℂ := A.app s - 1 with hzs
  have hzsre : zs.re = (A.app s).re - 1 := by simp [hzs]
  have hf : DifferentiableOn ℂ (fun z => k z s * Qcont z * Qcont (A.app s - z))
      (Icc c c' ×ℂ univ \ (({zs} : Finset ℂ) : Set ℂ)) := by
    intro z hz
    obtain ⟨⟨hz1, hz2⟩, -⟩ := Complex.mem_reProdIm.mp hz.1
    have hzz : z ≠ zs := by simpa using hz.2
    refine (differentiableAt_integrand_slice hRH A k hK1 hs (by linarith) (by simp; linarith)
      ?_ ?_).differentiableWithinAt
    · rintro rfl; simp at hz2; linarith
    · intro h; apply hzz; rw [hzs, ← h]; ring
  -- the numerator of `Qcont` at `1`
  obtain ⟨H, hH, hH1, hev⟩ := exists_numerator_of_simplePole (meromorphicAt_Qcont (a := 1) (by simp))
    (M1.meromorphicOrderAt_Qcont_ge (a := 1) (by simp))
    (M1.hasResidue_Qcont_Rcoef (a := 1) (Or.inl (Or.inl rfl)))
  rw [M1.Rcoef_one'] at hH1
  have hφ : Tendsto (fun z => A.app s - z) (𝓝[≠] zs) (𝓝[≠] 1) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun z => A.app s - z) (𝓝 zs) (𝓝 (A.app s - zs)) :=
        (continuous_const.sub continuous_id).tendsto zs
      rw [hzs, sub_sub_cancel] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      intro h; apply hz; simp only [mem_singleton_iff] at h ⊢; rw [hzs, ← h]; ring
  have hev' : ∀ᶠ z in 𝓝[≠] zs, (z - zs) * Qcont (A.app s - z) = (fun z => -H (A.app s - z)) z := by
    filter_upwards [hφ.eventually hev] with z hz
    rw [← hz, hzs]; ring
  have hH' : DifferentiableAt ℂ (fun z => -H (A.app s - z)) zs := by
    have hHz : DifferentiableAt ℂ H (A.app s - zs) := by rwa [hzs, sub_sub_cancel]
    exact (DifferentiableAt.comp (f := fun z => A.app s - z) zs hHz (by fun_prop)).neg
  have hzs1 : zs ≠ 1 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have hg : DifferentiableAt ℂ (fun z => k z s * Qcont z) zs :=
    (differentiableAt_k_slice hK1 hs (by linarith) (by linarith)).mul
      (TIdentity.analyticAt_Qcont_of_RH hRH (by linarith) hzs1).differentiableAt
  have hpole1 := isBigO_mul_sub_of_numerator hH' hg hev'
  have hpole : ∀ p ∈ ({zs} : Finset ℂ),
      ((fun z => k z s * Qcont z * Qcont (A.app s - z)) -
        fun z => (fun _ => -(k zs s * Qcont zs)) p / (z - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
    intro p hp
    rw [Finset.mem_singleton] at hp
    subst hp
    refine hpole1.congr' (Eventually.of_forall fun z => ?_) EventuallyEq.rfl
    have : H (A.app s - zs) = 1 := by rw [hzs, sub_sub_cancel, hH1]
    simp only [Pi.sub_apply, this]
    ring
  have := Ilog_shift hRH A k hK1 hK2 hs hc (by linarith) hc' (by linarith) hc'1.ne (by linarith)
    (by linarith) {zs} (fun _ => -(k zs s * Qcont zs))
    (by intro p hp; rw [Finset.mem_singleton] at hp; subst hp; rw [hzsre]; exact ⟨hcx, hxc'⟩) hf hpole
  rw [Finset.sum_singleton] at this
  rw [this]; ring

end GoldbachBoundaries.Paper2.M4b
