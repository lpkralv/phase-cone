import GoldbachBoundaries.Paper2.M5.Fill.T2Common

/-!
# Fill: `TkLine_step_sub_one`

`T2.shift` with `S = {z_*}`, `z_* = s - 1`, and `A(z_*) = -K_s(z_*) F(z_*)`. On the strip the only pole is `z_*`
(`Re w ≤ c' < m`, so `w ≠ m`). Near `z_*`: `(v - 1) Qcont(v) = H(v)` near `v = 1` with `H` differentiable at `1`,
`H(1) = Rcoef 1 = 1` (M4b's `exists_numerator_of_simplePole` with M1's facts at `1`); with `v = s - w`,
`(w - z_*) Qcont(s - w) = -H(s - w)`, so M4b's `isBigO_mul_sub_of_numerator` with `g = K_s F` (differentiable at `z_*`)
gives the pole condition with residue `-g(z_*)`. Finally `K_s(s - 1) = Γ(s-1)Γ(1)/Γ(s) = 1/(s - 1)`.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2

theorem TkLine_step_sub_one (hRH : RiemannHypothesis) {m : ℕ} (hm : 1 ≤ m) {F H : ℂ → ℂ} (hP : TkPack m F H) {s : ℂ}
    {c c' : ℝ} (hc : (m : ℝ) - 1 / 2 < c) (hcx : c < s.re - 1) (hxc' : s.re - 1 < c') (hc'm : c' < m)
    (hc' : c' + 1 / 2 < s.re) :
    TkLine F c' s = TkLine F c s - F (s - 1) / (s - 1) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  set zs : ℂ := s - 1 with hzs
  have hzsre : zs.re = s.re - 1 := by simp [hzs]
  have hf : DifferentiableOn ℂ (fun w => KerS s w * F w * Qcont (s - w))
      (Icc c c' ×ℂ univ \ (({zs} : Finset ℂ) : Set ℂ)) := by
    intro w hw
    obtain ⟨⟨hw1, hw2⟩, -⟩ := Complex.mem_reProdIm.mp hw.1
    have hwz : w ≠ zs := by simpa using hw.2
    refine (T2.differentiableAt_integrand_slice hRH hm hP (by linarith) ?_ (by simp; linarith)
      ?_).differentiableWithinAt
    · rintro rfl; simp at hw2; linarith
    · intro h; apply hwz; rw [hzs, ← h]; ring
  -- the numerator of `Qcont` at `1`
  obtain ⟨H1, hH, hH1, hev⟩ := M4b.exists_numerator_of_simplePole
    (meromorphicAt_Qcont (a := 1) (by simp))
    (M1.meromorphicOrderAt_Qcont_ge (a := 1) (by simp))
    (M1.hasResidue_Qcont_Rcoef (a := 1) (Or.inl (Or.inl rfl)))
  rw [M1.Rcoef_one'] at hH1
  have hφ : Tendsto (fun w => s - w) (𝓝[≠] zs) (𝓝[≠] 1) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun w => s - w) (𝓝 zs) (𝓝 (s - zs)) :=
        (continuous_const.sub continuous_id).tendsto zs
      rw [hzs, sub_sub_cancel] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with w hw
      intro h; apply hw; simp only [mem_singleton_iff] at h ⊢; rw [hzs, ← h]; ring
  have hev' : ∀ᶠ w in 𝓝[≠] zs, (w - zs) * Qcont (s - w) = (fun w => -H1 (s - w)) w := by
    filter_upwards [hφ.eventually hev] with w hw
    rw [← hw, hzs]; ring
  have hH' : DifferentiableAt ℂ (fun w => -H1 (s - w)) zs := by
    have hHz : DifferentiableAt ℂ H1 (s - zs) := by rwa [hzs, sub_sub_cancel]
    exact (DifferentiableAt.comp (f := fun w => s - w) zs hHz (by fun_prop)).neg
  have hzsm : zs ≠ m := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hszs : s - zs = 1 := by rw [hzs]; ring
  have hg : DifferentiableAt ℂ (fun w => KerS s w * F w) zs :=
    (T2.differentiableAt_KerS_slice (by linarith) (by rw [hszs]; simp)).mul
      (hP.2.2.2.2.1 zs (by linarith) hzsm).differentiableAt
  have hpole1 := M4b.isBigO_mul_sub_of_numerator hH' hg hev'
  have hpole : ∀ p ∈ ({zs} : Finset ℂ),
      ((fun w => KerS s w * F w * Qcont (s - w)) -
        fun w => (fun _ => -(KerS s zs * F zs)) p / (w - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
    intro p hp
    rw [Finset.mem_singleton] at hp
    subst hp
    refine hpole1.congr' (Eventually.of_forall fun w => ?_) EventuallyEq.rfl
    have : H1 (s - zs) = 1 := by rw [hszs, hH1]
    simp only [Pi.sub_apply, this]
    ring
  have := T2.shift hRH hm hP hc (by linarith) hc' (by linarith) hc'm.ne (by linarith)
    (by linarith) {zs} (fun _ => -(KerS s zs * F zs))
    (by intro p hp; rw [Finset.mem_singleton] at hp; subst hp; rw [hzsre]; exact ⟨hcx, hxc'⟩) hf hpole
  rw [Finset.sum_singleton] at this
  -- `K_s(s - 1) = 1/(s - 1)`
  have hs1 : 0 < (s - 1).re := by simp; linarith
  have hKzs : KerS s zs = 1 / (s - 1) := by
    have hne : Gamma (s - 1) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs1
    have hne1 : s - 1 ≠ 0 := by intro h; rw [h] at hs1; simp at hs1
    have hG : Gamma s = (s - 1) * Gamma (s - 1) := by
      have := Complex.Gamma_add_one (s - 1) hne1
      rw [sub_add_cancel] at this
      exact this
    rw [KerS, hszs, Complex.Gamma_one, hG, hzs]
    field_simp
  rw [this, hKzs]
  ring

end GoldbachBoundaries.Paper2.M5
