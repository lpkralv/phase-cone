import GoldbachBoundaries.Paper2.M5.Fill.T2Common

/-!
# Fill: `TkLine_step_pole`

`T2.shift` with `S = {m}` and `A(m) = r_m K_s(m) Qcont(s - m)`. On the strip `c ≤ Re w ≤ c'` the only pole is `w = m`
(`Re(s - w) ≥ σ - c' > 1`, so `s - w ≠ 1`). The pole condition is M4b's `isBigO_mul_sub_residue` with `f = F`
(fields 1, 6, 7 of the package: meromorphic at `m`, order `-1`, residue `1/(m-1)! = r_m`) and
`g(w) = K_s(w) Qcont(s - w)`, holomorphic on the open set `{0 < Re w, 1 < Re(s - w)}` containing `m`.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2

theorem TkLine_step_pole (hRH : RiemannHypothesis) {m : ℕ} (hm : 1 ≤ m) {F H : ℂ → ℂ} (hP : TkPack m F H)
    {s : ℂ} {c c' : ℝ} (hc : (m : ℝ) - 1 / 2 < c) (hcm : c < m) (hmc' : (m : ℝ) < c')
    (hc' : c' + 1 < s.re) :
    TkLine F c' s = rK m * KerS s m * Qcont (s - m) + TkLine F c s := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hf : DifferentiableOn ℂ (fun w => KerS s w * F w * Qcont (s - w))
      (Icc c c' ×ℂ univ \ (({(m : ℂ)} : Finset ℂ) : Set ℂ)) := by
    intro w hw
    obtain ⟨⟨hw1, hw2⟩, -⟩ := Complex.mem_reProdIm.mp hw.1
    have hwm : w ≠ m := by simpa using hw.2
    refine (T2.differentiableAt_integrand_slice hRH hm hP (by linarith) hwm (by simp; linarith)
      ?_).differentiableWithinAt
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  -- `g w = K_s(w) Qcont(s - w)` is analytic at `m`
  set V : Set ℂ := {z | 0 < z.re ∧ 1 < (s - z).re} with hV
  have hVo : IsOpen V :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_const.sub continuous_id)))
  have hmV : (m : ℂ) ∈ V := ⟨by simp; linarith, by simp; linarith⟩
  have hg : AnalyticAt ℂ (fun w => KerS s w * Qcont (s - w)) m := by
    refine DifferentiableOn.analyticAt (s := V) ?_ (hVo.mem_nhds hmV)
    intro z hz
    obtain ⟨hz0, hzs⟩ := hz
    have hQ : DifferentiableAt ℂ (fun z => Qcont (s - z)) z := by
      refine DifferentiableAt.comp (f := fun z => s - z) z
        (TIdentity.analyticAt_Qcont_of_RH hRH (by linarith) ?_).differentiableAt (by fun_prop)
      intro h; rw [h] at hzs; simp at hzs
    exact ((T2.differentiableAt_KerS_slice hz0 (by linarith)).mul hQ).differentiableWithinAt
  have hmero : MeromorphicAt F m := hP.1 m (by show (m : ℝ) - 1 < (m : ℂ).re; simp)
  have hord : -1 ≤ meromorphicOrderAt F m := by rw [hP.2.2.2.2.2.1]
  have hpole1 := M4b.isBigO_mul_sub_residue hmero hord hP.2.2.2.2.2.2.1 hg
  have hpole : ∀ p ∈ ({(m : ℂ)} : Finset ℂ),
      ((fun w => KerS s w * F w * Qcont (s - w)) -
        fun w => (fun _ => rK m * KerS s m * Qcont (s - m)) p / (w - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
    intro p hp
    rw [Finset.mem_singleton] at hp
    subst hp
    refine hpole1.congr' (Eventually.of_forall fun z => ?_) EventuallyEq.rfl
    simp only [Pi.sub_apply, rK]
    ring
  have := T2.shift hRH hm hP hc (by linarith) (by linarith) hcm.ne hmc'.ne' (by linarith)
    (by linarith) {(m : ℂ)} (fun _ => rK m * KerS s m * Qcont (s - m))
    (by intro p hp; rw [Finset.mem_singleton] at hp; subst hp; simp; exact ⟨hcm, hmc'⟩) hf hpole
  simpa using this

end GoldbachBoundaries.Paper2.M5
