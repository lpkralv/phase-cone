import GoldbachBoundaries.ResidueClass.LFunctionGrowth
import Zeta.Gamma.DigammaStirling

/-! # Reflection for the local Dirichlet log-derivative estimate -/

noncomputable section

open Complex Filter Set
open scoped Topology Classical

namespace GoldbachBoundaries.ResidueClass

variable {m : ℕ} [NeZero m] (ψ : DirichletCharacter ℂ m)

private theorem nonreal_ne_neg_nat {z : ℂ} (hz : z.im ≠ 0) (n : ℕ) : z ≠ -(n : ℂ) := by
  intro h
  exact hz (by rw [h]; simp)

private theorem analyticAt_const_cpow_comp {g : ℂ → ℂ} {a z : ℂ}
    (ha : a ≠ 0) (hg : AnalyticAt ℂ g z) : AnalyticAt ℂ (fun w ↦ a ^ g w) z := by
  simp only [cpow_def_of_ne_zero ha]
  exact (analyticAt_const.mul hg).cexp

private theorem gammaReal_nonreal {z : ℂ} (hz : z.im ≠ 0) :
    Gammaℝ z ≠ 0 ∧ AnalyticAt ℂ Gammaℝ z := by
  have hn : Gammaℝ z ≠ 0 := by
    intro hz₀
    obtain ⟨n, h⟩ := Gammaℝ_eq_zero_iff.mp hz₀
    exact hz (by simpa using congrArg Complex.im h)
  exact ⟨hn, by
    have ha := (differentiable_Gammaℝ_inv.analyticAt z).inv (inv_ne_zero hn)
    change AnalyticAt ℂ (fun w ↦ (Gammaℝ w)⁻¹⁻¹) z at ha
    simpa only [inv_inv] using ha⟩

omit [NeZero m] in
private theorem gammaFactor_nonreal {z : ℂ} (hz : z.im ≠ 0) :
    ψ.gammaFactor z ≠ 0 ∧ AnalyticAt ℂ ψ.gammaFactor z := by
  rcases ψ.even_or_odd with he | ho
  · have heq : ψ.gammaFactor = Gammaℝ := funext he.gammaFactor_def
    rw [heq]
    exact gammaReal_nonreal hz
  · have heq : ψ.gammaFactor = Gammaℝ ∘ (fun w ↦ w + 1) := funext ho.gammaFactor_def
    rw [heq]
    obtain ⟨hn, ha⟩ := gammaReal_nonreal (z := z + 1) (by simpa using hz)
    exact ⟨hn, ha.comp (f := fun w : ℂ ↦ w + 1) (x := z) (by fun_prop)⟩

private theorem rootNumber_ne_zero (hψ : ψ.IsPrimitive) : ψ.rootNumber ≠ 0 := by
  intro hzero
  have h := hψ.completedLFunction_one_sub (-1)
  have htwo : ψ.completedLFunction 2 = 0 := by
    simpa [show (1 : ℂ) - (-1) = 2 by ring, hzero] using h
  apply ψ.LFunction_ne_zero_of_one_le_re (s := 2) (.inr (by norm_num)) (by norm_num)
  rw [ψ.LFunction_eq_completed_div_gammaFactor _ (.inl (by norm_num)), htwo, zero_div]

private def reflectionFactor (z : ℂ) : ℂ :=
  (m : ℂ) ^ (1 / 2 - z) * ψ.rootNumber * (ψ⁻¹).gammaFactor (1 - z) / ψ.gammaFactor z

private theorem reflectionFactor_nonreal (hψ : ψ.IsPrimitive) {z : ℂ} (hz : z.im ≠ 0) :
    reflectionFactor ψ z ≠ 0 ∧ AnalyticAt ℂ (reflectionFactor ψ) z := by
  have hflip : (1 - z).im ≠ 0 := by simpa using hz
  have h₁ := gammaFactor_nonreal ψ hz
  have h₂ := gammaFactor_nonreal ψ⁻¹ hflip
  have hm : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  refine ⟨div_ne_zero (mul_ne_zero (mul_ne_zero (cpow_ne_zero_iff.mpr (.inl hm))
    (rootNumber_ne_zero ψ hψ)) h₂.1) h₁.1, ?_⟩
  apply AnalyticAt.div _ h₁.2 h₁.1
  refine ((analyticAt_const_cpow_comp hm (by fun_prop)).mul analyticAt_const).mul ?_
  exact h₂.2.comp (show AnalyticAt ℂ (fun w : ℂ ↦ 1 - w) z by fun_prop)

private theorem lFunction_reflection (hψ : ψ.IsPrimitive) {z : ℂ} (hz : z.im ≠ 0) :
    ψ.LFunction z = reflectionFactor ψ z * (ψ⁻¹).LFunction (1 - z) := by
  have hflip : (1 - z).im ≠ 0 := by simpa using hz
  rw [ψ.LFunction_eq_completed_div_gammaFactor _ (.inl (by simpa using nonreal_ne_neg_nat hz 0)),
    (ψ⁻¹).LFunction_eq_completed_div_gammaFactor _ (.inl (by
      intro h
      exact hflip (by rw [h]; simp)))]
  have heq := hψ.completedLFunction_one_sub (1 - z)
  rw [show (1 : ℂ) - (1 - z) = z by ring, show (1 : ℂ) - z - 1 / 2 = 1 / 2 - z by ring] at heq
  rw [heq, reflectionFactor]
  field_simp [(gammaFactor_nonreal ψ hz).1, (gammaFactor_nonreal ψ⁻¹ hflip).1]

/-- Reflection identifies the zeros of a primitive L-function with those of its inverse
character at nonreal points. -/
theorem lFunction_reflection_zero_iff (hψ : ψ.IsPrimitive) {z : ℂ} (hz : z.im ≠ 0) :
    ψ.LFunction z = 0 ↔ (ψ⁻¹).LFunction (1 - z) = 0 := by
  rw [lFunction_reflection ψ hψ hz, mul_eq_zero,
    or_iff_right (reflectionFactor_nonreal ψ hψ hz).1]

private theorem eventuallyEq_lFunction_reflection (hψ : ψ.IsPrimitive) {z : ℂ} (hz : z.im ≠ 0) :
    ψ.LFunction =ᶠ[𝓝 z] fun w ↦ reflectionFactor ψ w * (ψ⁻¹).LFunction (1 - w) := by
  filter_upwards [(isOpen_ne_fun continuous_im continuous_const).mem_nhds hz]
    with w hw using lFunction_reflection ψ hψ hw

/-- At a nonreal point the reflection factor is analytic and nonvanishing,
so reflection also preserves analytic order. -/
theorem lFunction_reflection_order (hψ : ψ.IsPrimitive) (hn : ψ ≠ 1) {z : ℂ} (hz : z.im ≠ 0) :
    analyticOrderNatAt ψ.LFunction z = analyticOrderNatAt (ψ⁻¹).LFunction (1 - z) := by
  have hg : AnalyticAt ℂ (fun w : ℂ ↦ 1 - w) z := by fun_prop
  have hn' : ψ⁻¹ ≠ 1 := by simpa using hn
  have hf := (DirichletCharacter.differentiable_LFunction hn').analyticAt (1 - z)
  obtain ⟨hfactor, ha⟩ := reflectionFactor_nonreal ψ hψ hz
  unfold analyticOrderNatAt
  congr 1
  rw [analyticOrderAt_congr (eventuallyEq_lFunction_reflection ψ hψ hz)]
  change analyticOrderAt (reflectionFactor ψ * ((ψ⁻¹).LFunction ∘ (fun w ↦ 1 - w))) z = _
  rw [analyticOrderAt_mul ha (hf.comp hg), ha.analyticOrderAt_eq_zero.mpr hfactor, zero_add]
  exact analyticOrderAt_comp_of_deriv_ne_zero hg (by simp)

omit [NeZero m] in
private theorem logDeriv_gammaFactor {z : ℂ} (hz : z.im ≠ 0) :
    logDeriv ψ.gammaFactor z =
      (digamma ((z + if ψ.Even then 0 else 1) / 2) - log (Real.pi : ℂ)) / 2 := by
  classical
  let a : ℂ := if ψ.Even then 0 else 1
  have ha : a.im = 0 := by dsimp [a]; split_ifs <;> simp
  have heq : ψ.gammaFactor = fun w ↦ Gammaℝ (w + a) := by
    funext w
    unfold DirichletCharacter.gammaFactor a
    split_ifs <;> simp
  have harg : ∀ n : ℕ, (z + a) / 2 ≠ -(n : ℂ) :=
    nonreal_ne_neg_nat (by simpa [div_ofNat_im, add_im, ha] using hz)
  have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [heq]
  change logDeriv (fun w ↦ (Real.pi : ℂ) ^ (-(w + a) / 2) * Gamma ((w + a) / 2)) z = _
  have hA : HasDerivAt (fun w : ℂ ↦ -(w + a) / 2) (-1 / 2) z := by
    simpa using (((hasDerivAt_id z).add_const a).neg.div_const (2 : ℂ))
  have hB : HasDerivAt (fun w : ℂ ↦ (w + a) / 2) (1 / 2) z :=
    ((hasDerivAt_id z).add_const a).div_const 2
  rw [logDeriv_fun_mul (f := fun w ↦ (Real.pi : ℂ) ^ (-(w + a) / 2))
    (g := fun w ↦ Gamma ((w + a) / 2)) z
    (cpow_ne_zero_iff.mpr (.inl hπ)) (Gamma_ne_zero harg)
    (hA.const_cpow (.inl hπ)).differentiableAt
    ((differentiableAt_Gamma _ harg).comp z hB.differentiableAt),
    hB.logDeriv_Gamma harg]
  have hp := logDeriv_comp (f := fun w : ℂ ↦ (Real.pi : ℂ) ^ w)
    (g := fun w : ℂ ↦ -(w + a) / 2)
    ((hasDerivAt_id _).const_cpow (.inl hπ)).differentiableAt hA.differentiableAt
  rw [Complex.logDeriv_const_cpow hπ, hA.deriv] at hp
  change logDeriv (fun w : ℂ ↦ (Real.pi : ℂ) ^ (-(w + a) / 2)) z = _ at hp
  rw [hp]
  ring

private theorem logDeriv_reflectionFactor (hψ : ψ.IsPrimitive) {z : ℂ} (hz : z.im ≠ 0) :
    logDeriv (reflectionFactor ψ) z =
      -log (m : ℂ) - logDeriv (ψ⁻¹).gammaFactor (1 - z) - logDeriv ψ.gammaFactor z := by
  have hflip : (1 - z).im ≠ 0 := by simpa using hz
  obtain ⟨hg, hga⟩ := gammaFactor_nonreal ψ hz
  obtain ⟨hg', hga'⟩ := gammaFactor_nonreal ψ⁻¹ hflip
  have hm : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  have hroot := rootNumber_ne_zero ψ hψ
  have hExp : HasDerivAt (fun w : ℂ ↦ 1 / 2 - w) (-1) z :=
    (hasDerivAt_id z).const_sub _
  have hArg : HasDerivAt (fun w : ℂ ↦ 1 - w) (-1) z :=
    (hasDerivAt_id z).const_sub _
  have hp : (m : ℂ) ^ (1 / 2 - z) ≠ 0 := cpow_ne_zero_iff.mpr (.inl hm)
  have hd := (hExp.const_cpow (.inl hm)).differentiableAt.mul_const ψ.rootNumber
  have hG : DifferentiableAt ℂ (fun w ↦ (ψ⁻¹).gammaFactor (1 - w)) z :=
    hga'.differentiableAt.comp z hArg.differentiableAt
  unfold reflectionFactor
  have hcomp : logDeriv (fun w ↦ (ψ⁻¹).gammaFactor (1 - w)) z =
      logDeriv (ψ⁻¹).gammaFactor (1 - z) * (-1) := by
    change logDeriv ((ψ⁻¹).gammaFactor ∘ (fun w ↦ 1 - w)) z = _
    rw [logDeriv_comp hga'.differentiableAt hArg.differentiableAt, hArg.deriv]
  rw [logDeriv_fun_div (f := fun w ↦ (m : ℂ) ^ (1 / 2 - w) * ψ.rootNumber *
      (ψ⁻¹).gammaFactor (1 - w)) (g := ψ.gammaFactor) z
      (mul_ne_zero (mul_ne_zero hp hroot) hg') hg (hd.mul hG) hga.differentiableAt,
    logDeriv_fun_mul (f := fun w ↦ (m : ℂ) ^ (1 / 2 - w) * ψ.rootNumber)
      (g := fun w ↦ (ψ⁻¹).gammaFactor (1 - w)) z (mul_ne_zero hp hroot) hg' hd hG,
    logDeriv_mul_const _ _ hroot, hcomp]
  have he := logDeriv_comp (f := fun w : ℂ ↦ (m : ℂ) ^ w)
    (g := fun w : ℂ ↦ 1 / 2 - w)
    ((hasDerivAt_id _).const_cpow (.inl hm)).differentiableAt hExp.differentiableAt
  rw [Complex.logDeriv_const_cpow hm, hExp.deriv] at he
  change logDeriv (fun w : ℂ ↦ (m : ℂ) ^ (1 / 2 - w)) z = _ at he
  rw [he]
  ring

private theorem norm_digamma_half_le {u : ℂ} (hr₀ : 0 ≤ u.re) (hr₁ : u.re ≤ 1)
    (hi : 1 ≤ |u.im|) :
    ‖digamma u‖ ≤ Real.log (2 + 2 * |u.im|) + Real.pi + (1 / 12 + 3 / (2 * Real.pi ^ 2)) + 2 := by
  let v := u + 1
  let D : ℝ := 1 / 12 + 3 / (2 * Real.pi ^ 2)
  have hvre : 1 ≤ v.re := by simpa [v] using hr₀
  have hv : 1 ≤ ‖v‖ := hvre.trans (re_le_norm v)
  have hu : 1 ≤ ‖u‖ := hi.trans (abs_im_le_norm u)
  have hlog : ‖log v‖ ≤ Real.log (2 + 2 * |u.im|) + Real.pi := by
    have hv' : ‖v‖ ≤ 2 + 2 * |u.im| := by
      refine (norm_le_abs_re_add_abs_im v).trans ?_
      rw [abs_of_nonneg (by linarith : 0 ≤ v.re)]
      simp only [v, add_re, add_im, one_re, one_im, add_zero]
      linarith
    refine (norm_le_abs_re_add_abs_im (log v)).trans ?_
    rw [log_re, abs_of_nonneg (Real.log_nonneg hv), log_im]
    exact add_le_add (Real.log_le_log (by positivity) hv') (abs_arg_le_pi _)
  have hD : 0 ≤ D := by positivity
  have herr := Complex.Stirling.norm_digamma_sub_log_le' (a := 1) one_pos v hvre
  rw [mul_one] at herr
  have hzpow : ‖v‖ ^ (-(2 : ℤ)) ≤ 1 := by
    rw [zpow_neg, zpow_ofNat]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ hv)
  have herr' : ‖digamma v - log v + (2 * v)⁻¹‖ ≤ D :=
    herr.trans (mul_le_of_le_one_right hD hzpow)
  have hinvv : ‖(2 * v)⁻¹‖ ≤ 1 := by
    rw [norm_inv, norm_mul, norm_ofNat]
    exact inv_le_one_of_one_le₀ (by linarith)
  have hinvu : ‖u⁻¹‖ ≤ 1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ hu
  have hn := nonreal_ne_neg_nat (z := u) (by intro h; norm_num [h] at hi)
  have he : digamma u = (digamma v - log v + (2 * v)⁻¹) + log v - (2 * v)⁻¹ - u⁻¹ := by
    rw [show digamma v = digamma u + u⁻¹ from digamma_apply_add_one u hn]
    ring
  rw [he]
  dsimp [D] at herr'
  linarith [norm_sub_le ((digamma v - log v + (2 * v)⁻¹) + log v - (2 * v)⁻¹) u⁻¹,
    norm_sub_le ((digamma v - log v + (2 * v)⁻¹) + log v) (2 * v)⁻¹,
    norm_add_le (digamma v - log v + (2 * v)⁻¹) (log v)]

omit [NeZero m] in
private theorem norm_logDeriv_gammaFactor_le {z : ℂ} (hr₀ : 0 ≤ z.re) (hr₁ : z.re ≤ 1)
    (hi : 2 ≤ |z.im|) :
    ‖logDeriv ψ.gammaFactor z‖ ≤
      (Real.log (2 + |z.im|) + Real.pi + (1 / 12 + 3 / (2 * Real.pi ^ 2)) + 2 +
        ‖log (Real.pi : ℂ)‖) / 2 := by
  classical
  have him : z.im ≠ 0 := by intro h; norm_num [h] at hi
  let a : ℂ := if ψ.Even then 0 else 1
  have ha₀ : 0 ≤ a.re := by dsimp [a]; split_ifs <;> simp
  have ha₁ : a.re ≤ 1 := by dsimp [a]; split_ifs <;> simp
  have hai : a.im = 0 := by dsimp [a]; split_ifs <;> simp
  let u := (z + a) / 2
  have hu₀ : 0 ≤ u.re := by
    rw [show u.re = (z.re + a.re) / 2 by simp [u, div_ofNat_re]]
    linarith
  have hu₁ : u.re ≤ 1 := by
    rw [show u.re = (z.re + a.re) / 2 by simp [u, div_ofNat_re]]
    linarith
  have hui : |u.im| = |z.im| / 2 := by simp [u, div_ofNat_im, hai, abs_div]
  have hdu := norm_digamma_half_le hu₀ hu₁ (show 1 ≤ |u.im| by rw [hui]; linarith)
  rw [hui, show 2 + 2 * (|z.im| / 2) = 2 + |z.im| by ring] at hdu
  rw [logDeriv_gammaFactor ψ him]
  change ‖(digamma u - log (Real.pi : ℂ)) / 2‖ ≤ _
  rw [norm_div, norm_ofNat]
  gcongr
  exact (norm_sub_le _ _).trans (add_le_add hdu le_rfl)

/-- On the open strip the reflected logarithmic derivative has the opposite sign,
up to an archimedean and conductor term of logarithmic size. -/
theorem exists_lFunction_reflection_logDeriv_bound (hψ : ψ.IsPrimitive) (hn : ψ ≠ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, 0 < z.re → z.re < 1 → 2 ≤ |z.im| → ψ.LFunction z ≠ 0 →
      ‖logDeriv ψ.LFunction z + logDeriv (ψ⁻¹).LFunction (1 - z)‖ ≤ C * Real.log (2 + |z.im|) := by
  let A : ℝ := ‖log (m : ℂ)‖ + Real.pi + (1 / 12 + 3 / (2 * Real.pi ^ 2)) + 2 +
    ‖log (Real.pi : ℂ)‖
  have hA : 0 ≤ A := by positivity
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  refine ⟨1 + A / Real.log 4, by positivity, fun z hr₀ hr₁ hi hf ↦ ?_⟩
  have him : z.im ≠ 0 := by intro h; norm_num [h] at hi
  have hflip : |(1 - z).im| = |z.im| := by simp
  have hg : (ψ⁻¹).LFunction (1 - z) ≠ 0 :=
    fun h ↦ hf ((lFunction_reflection_zero_iff ψ hψ him).mpr h)
  have hn' : ψ⁻¹ ≠ 1 := by simpa using hn
  have hgd := DirichletCharacter.differentiable_LFunction hn' (1 - z)
  have harg : HasDerivAt (fun w : ℂ ↦ 1 - w) (-1) z :=
    (hasDerivAt_id z).const_sub _
  obtain ⟨hR, hRa⟩ := reflectionFactor_nonreal ψ hψ him
  have heq := eventuallyEq_lFunction_reflection ψ hψ him
  have hld : logDeriv ψ.LFunction z =
      logDeriv (fun w ↦ reflectionFactor ψ w * (ψ⁻¹).LFunction (1 - w)) z := by
    rw [logDeriv_apply, logDeriv_apply, heq.deriv_eq, heq.self_of_nhds]
  rw [hld]
  change ‖logDeriv (fun w ↦ reflectionFactor ψ w * ((ψ⁻¹).LFunction ∘ (fun v ↦ 1 - v)) w) z + _‖ ≤ _
  rw [logDeriv_fun_mul z hR hg hRa.differentiableAt (hgd.comp z harg.differentiableAt),
    logDeriv_comp hgd harg.differentiableAt, harg.deriv]
  have hcancel (a b : ℂ) : a + b * (-1) + b = a := by ring
  rw [hcancel, logDeriv_reflectionFactor ψ hψ him]
  have hΓ := norm_logDeriv_gammaFactor_le ψ hr₀.le hr₁.le hi
  have hΓ' := norm_logDeriv_gammaFactor_le ψ⁻¹ (z := 1 - z)
    (by simp [sub_nonneg, hr₁.le]) (by simp [hr₀.le]) (by rwa [hflip])
  rw [hflip] at hΓ'
  have hlog := Real.log_le_log (show (0 : ℝ) < 4 by norm_num)
    (show 4 ≤ 2 + |z.im| by linarith)
  have hscale : A ≤ A / Real.log 4 * Real.log (2 + |z.im|) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog4]
    exact mul_le_mul_of_nonneg_left hlog hA
  have hb := norm_sub_le (-log (m : ℂ) - logDeriv (ψ⁻¹).gammaFactor (1 - z))
    (logDeriv ψ.gammaFactor z)
  have hc := norm_sub_le (-log (m : ℂ)) (logDeriv (ψ⁻¹).gammaFactor (1 - z))
  rw [norm_neg] at hc
  dsimp [A] at hscale
  linarith

end GoldbachBoundaries.ResidueClass
