import GoldbachBoundaries.Paper2.M4b.Fill.DCommon

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M4b

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/- Filler for `K4_kernels` (`Kernels.lean`). Each kernel is `u/v` with `u, v` built from `g = 1/Γ` and affine maps;
the identity `k = u/v` holds everywhere (`Γ = (1/Γ)⁻¹` in a field with `0⁻¹ = 0`), and `v ≠ 0` at any point of a
ball whose two `Γ` arguments are non-real (`FillD.exists_ball_im`). -/

namespace FillD

lemma K4_kerG : K4 kerG := by
  refine isMeromorphic₂_of_global (u := fun q => (Gamma q.2)⁻¹)
    (v := fun q => (Gamma q.1)⁻¹ * (Gamma (q.2 - q.1))⁻¹) ?_ ?_ ?_ ?_
  · intro q _; exact analyticAt_invGamma_comp analyticAt_snd
  · intro q _
    exact (analyticAt_invGamma_comp analyticAt_fst).mul
      (analyticAt_invGamma_comp (analyticAt_snd.sub analyticAt_fst))
  · intro p r hr
    obtain ⟨q, hq, h1, h2⟩ := exists_ball_im p hr 0 id
    refine ⟨q, hq, mul_ne_zero (invGamma_ne_zero_of_im h1) (invGamma_ne_zero_of_im ?_)⟩
    simp only [sub_im, id] at h2 ⊢
    exact sub_ne_zero.2 h2
  · intro q _
    simp only [kerG, KerS]
    simp only [div_eq_mul_inv, mul_inv, inv_inv]
    ring

lemma K4_k0 : K4 k0 := by
  refine isMeromorphic₂_of_global (u := fun q => (Gamma q.2)⁻¹ * (q.1 - 1) * (q.2 - 1 - q.1))
    (v := fun q => (Gamma q.1)⁻¹ * (Gamma (q.2 - q.1))⁻¹) ?_ ?_ ?_ ?_
  · intro q _
    exact ((analyticAt_invGamma_comp analyticAt_snd).mul (analyticAt_fst.sub analyticAt_const)).mul
      ((analyticAt_snd.sub analyticAt_const).sub analyticAt_fst)
  · intro q _
    exact (analyticAt_invGamma_comp analyticAt_fst).mul
      (analyticAt_invGamma_comp (analyticAt_snd.sub analyticAt_fst))
  · intro p r hr
    obtain ⟨q, hq, h1, h2⟩ := exists_ball_im p hr 0 id
    refine ⟨q, hq, mul_ne_zero (invGamma_ne_zero_of_im h1) (invGamma_ne_zero_of_im ?_)⟩
    simp only [sub_im, id] at h2 ⊢
    exact sub_ne_zero.2 h2
  · intro q _
    simp only [k0, KerS]
    simp only [div_eq_mul_inv, mul_inv, inv_inv]
    ring

lemma K4_kerSq : K4 kerSq := by
  refine isMeromorphic₂_of_global (u := fun q => (1 / 2 : ℂ) * (Gamma q.2)⁻¹)
    (v := fun q => (Gamma (q.1 / 2))⁻¹ * (Gamma (q.2 - q.1 / 2))⁻¹) ?_ ?_ ?_ ?_
  · intro q _; exact analyticAt_const.mul (analyticAt_invGamma_comp analyticAt_snd)
  · intro q _
    have hf : AnalyticAt ℂ (fun q : ℂ × ℂ => q.1 / 2) q := analyticAt_fst.div_const
    exact (analyticAt_invGamma_comp hf).mul (analyticAt_invGamma_comp (analyticAt_snd.sub hf))
  · intro p r hr
    obtain ⟨q, hq, h1, h2⟩ := exists_ball_im p hr 0 (fun a => a / 2)
    refine ⟨q, hq, mul_ne_zero (invGamma_ne_zero_of_im ?_) (invGamma_ne_zero_of_im ?_)⟩
    · simp only [div_ofNat_im]
      exact div_ne_zero h1 two_ne_zero
    · simp only [sub_im, div_ofNat_im]
      exact sub_ne_zero.2 h2
  · intro q _
    simp only [kerSq]
    simp only [div_eq_mul_inv, mul_inv, inv_inv]
    ring

lemma K4_kerS : K4 kerS := by
  refine isMeromorphic₂_of_global (u := fun _ => (1 / 2 : ℂ))
    (v := fun q => (Gamma ((q.1 - q.2 + 1) / 2))⁻¹ * (Gamma (2 - (q.1 - q.2 + 1) / 2))⁻¹) ?_ ?_ ?_ ?_
  · intro q _; exact analyticAt_const
  · intro q _
    have hf : AnalyticAt ℂ (fun q : ℂ × ℂ => (q.1 - q.2 + 1) / 2) q :=
      ((analyticAt_fst.sub analyticAt_snd).add analyticAt_const).div_const
    exact (analyticAt_invGamma_comp hf).mul (analyticAt_invGamma_comp (analyticAt_const.sub hf))
  · intro p r hr
    obtain ⟨q, hq, -, h2⟩ := exists_ball_im p hr 0 id
    have hw : ((q.1 - q.2 + 1) / 2).im ≠ 0 := by
      simp only [div_ofNat_im, add_im, sub_im, one_im, add_zero]
      exact div_ne_zero (sub_ne_zero.2 (Ne.symm h2)) two_ne_zero
    refine ⟨q, hq, mul_ne_zero (invGamma_ne_zero_of_im hw) (invGamma_ne_zero_of_im ?_)⟩
    rw [sub_im]
    simpa using hw
  · intro q _
    simp only [kerS, KS]
    simp only [div_eq_mul_inv, mul_inv, inv_inv]

end FillD

/-- **(K4) for the four kernels.** `g = (Γ ·)⁻¹` is entire (`Complex.differentiable_one_div_Gamma`), hence analytic
(`Differentiable.analyticAt`), and so are its compositions with affine maps `ℂ × ℂ → ℂ`. Write
`kerG z s = u/v` with `u = g(s)`, `v = g(z)g(s - z)`; `k₀`: `u = g(s)(z - 1)(s - 1 - z)`, same `v`; `kerSq`:
`u = ½g(s)`, `v = g(z/2)g(s - z/2)`; `kerS`: `u = ½`, `v = g(w)g(2 - w)`, `w = (z - s + 1)/2`. Where `v ≠ 0`, `Γ = 1/g` at
both arguments and `u/v` is the kernel (also where `Γ(s) = 0` in Lean, both sides being `0`). `v` is non-zero somewhere
in every ball: `g` vanishes only on `{0, -1, -2, …}`, so a point of the ball whose two arguments are non-real works
(perturb the imaginary parts of `(z, s)` by `(iδ, 3iδ)` with small `δ` avoiding two values). Conclude with
`isMeromorphic₂_of_global`. Size: 150–250 lines. -/
theorem K4_kernels : K4 kerG ∧ K4 kerSq ∧ K4 kerS ∧ K4 k0 :=
  ⟨FillD.K4_kerG, FillD.K4_kerSq, FillD.K4_kerS, FillD.K4_k0⟩

end GoldbachBoundaries.Paper2.M4b
