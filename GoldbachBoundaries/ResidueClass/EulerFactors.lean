import GoldbachBoundaries.ResidueClass.Series

/-! # Change of level and its contribution to the logarithmic derivative -/

noncomputable section

open Complex Filter Set
open scoped Topology

namespace GoldbachBoundaries.ResidueClass

variable {q : ℕ} (χ : DirichletCharacter ℂ q)

/-- The factor associated to a prime dividing the raised level. -/
def eulerFactor (p : ℕ) (s : ℂ) : ℂ :=
  1 - χ.primitiveCharacter p * (p : ℂ) ^ (-s)

/-- The finite product relating the continued L-functions before and after induction. -/
def eulerProduct (s : ℂ) : ℂ := ∏ p ∈ q.primeFactors, eulerFactor χ p s

theorem eulerFactor_eq_one_of_dvd {p : ℕ} (hp : p.Prime) (h : p ∣ χ.conductor) (s : ℂ) :
    eulerFactor χ p s = 1 := by
  have hnu : ¬ IsUnit (p : ZMod χ.conductor) := by
    exact fun hu ↦ (ZMod.isUnit_prime_iff_not_dvd hp).mp hu h
  simp [eulerFactor, χ.primitiveCharacter.map_nonunit hnu]

theorem norm_eulerTerm_le {p : ℕ} (hp : 0 < p) (s : ℂ) :
    ‖χ.primitiveCharacter p * (p : ℂ) ^ (-s)‖ ≤ (p : ℝ) ^ (-s.re) := by
  rw [norm_mul, norm_natCast_cpow_of_pos hp, neg_re]
  exact mul_le_of_le_one_left (by positivity) (DirichletCharacter.norm_le_one _ _)

theorem one_sub_rpow_le_norm_eulerFactor {p : ℕ} (hp : p.Prime) {d : ℝ} {s : ℂ}
    (hs : d ≤ s.re) : 1 - (p : ℝ) ^ (-d) ≤ ‖eulerFactor χ p s‖ := by
  have hp₁ : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hterm := (norm_eulerTerm_le χ hp.pos s).trans
    (Real.rpow_le_rpow_of_exponent_le hp₁ (neg_le_neg hs))
  have htriangle := norm_add_le (eulerFactor χ p s) (χ.primitiveCharacter p * (p : ℂ) ^ (-s))
  rw [eulerFactor, sub_add_cancel, norm_one] at htriangle
  unfold eulerFactor
  linarith

theorem eulerFactor_ne_zero {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 0 < s.re) :
    eulerFactor χ p s ≠ 0 := by
  have hp₁ : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have h := Real.rpow_lt_rpow_of_exponent_lt hp₁ (neg_lt_zero.mpr hs)
  rw [Real.rpow_zero] at h
  exact norm_pos_iff.mp (lt_of_lt_of_le (sub_pos.mpr h)
    (one_sub_rpow_le_norm_eulerFactor χ hp le_rfl))

theorem eulerProduct_ne_zero {s : ℂ} (hs : 0 < s.re) : eulerProduct χ s ≠ 0 := by
  rw [eulerProduct, Finset.prod_ne_zero_iff]
  exact fun p hp ↦ eulerFactor_ne_zero χ (Nat.prime_of_mem_primeFactors hp) hs

theorem hasDerivAt_eulerFactor {p : ℕ} (hp : 0 < p) (s : ℂ) :
    HasDerivAt (eulerFactor χ p)
      (χ.primitiveCharacter p * (p : ℂ) ^ (-s) * (Real.log p : ℂ)) s := by
  have hp₀ : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  have hpow := ((hasDerivAt_id s).neg.const_cpow (Or.inl hp₀)).const_mul
    (χ.primitiveCharacter p)
  have hlog : Complex.log (p : ℂ) = (Real.log p : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_log (by positivity : (0 : ℝ) ≤ p)]
  have hsub :
      HasDerivAt (eulerFactor χ p)
        (0 - χ.primitiveCharacter p * ((p : ℂ) ^ (-s) * Complex.log p * (-1))) s :=
    (hasDerivAt_const s (1 : ℂ)).sub hpow
  convert hsub using 1
  rw [hlog]
  ring

theorem analyticAt_eulerProduct (s : ℂ) : AnalyticAt ℂ (eulerProduct χ) s := by
  apply Differentiable.analyticAt
  unfold eulerProduct
  exact fun z ↦ DifferentiableAt.fun_finsetProd (fun p hp ↦
    (hasDerivAt_eulerFactor χ (Nat.prime_of_mem_primeFactors hp).pos z).differentiableAt)

variable [NeZero q]

theorem lFunction_eq_primitive_mul {s : ℂ} (hs : s ≠ 1 ∨ χ ≠ 1) :
    χ.LFunction s = primitiveL χ s * eulerProduct χ s := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have h : χ.primitiveCharacter ≠ 1 ∨ s ≠ 1 := hs.elim Or.inr fun hχ ↦ Or.inl fun hprim ↦
    hχ (χ.changeLevel_primitiveCharacter.symm.trans
      ((congrArg (DirichletCharacter.changeLevel χ.conductor_dvd_level) hprim).trans
        (DirichletCharacter.changeLevel_one _)))
  simpa only [χ.changeLevel_primitiveCharacter, primitiveL, eulerProduct, eulerFactor] using
    DirichletCharacter.LFunction_changeLevel χ.conductor_dvd_level χ.primitiveCharacter h

theorem primitiveL_one : primitiveL (1 : DirichletCharacter ℂ q) = riemannZeta := by
  have h (n : ℕ) [NeZero n] (ψ : DirichletCharacter ℂ n) (hn : n = 1) :
      ψ.LFunction = riemannZeta := by
    subst n
    exact DirichletCharacter.LFunction_modOne_eq
  let : NeZero ((1 : DirichletCharacter ℂ q).conductor) := ⟨DirichletCharacter.conductor_ne_zero _⟩
  exact h _ _ DirichletCharacter.conductor_one

theorem lFunction_zero_iff_primitive_zero {s : ℂ} (hs : 0 < s.re) (hs₁ : s ≠ 1) :
    χ.LFunction s = 0 ↔ primitiveL χ s = 0 := by
  rw [lFunction_eq_primitive_mul χ (.inl hs₁), mul_eq_zero, or_iff_left (eulerProduct_ne_zero χ hs)]

theorem analyticOrderNatAt_lFunction_eq_primitiveMult {s : ℂ} (hs : 0 < s.re) (hs₁ : s ≠ 1) :
    analyticOrderNatAt χ.LFunction s = primitiveMult χ s := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have heq : χ.LFunction =ᶠ[𝓝 s] fun z ↦ primitiveL χ z * eulerProduct χ z := by
    filter_upwards [isOpen_compl_singleton.mem_nhds (show s ∈ ({1} : Set ℂ)ᶜ from hs₁)]
      with z hz using lFunction_eq_primitive_mul χ (.inl hz)
  have ha : AnalyticAt ℂ (primitiveL χ) s :=
    DifferentiableOn.analyticAt (s := ({1} : Set ℂ)ᶜ)
      (fun z hz ↦ (χ.primitiveCharacter.differentiableAt_LFunction z (.inl hz)).differentiableWithinAt)
      (isOpen_compl_singleton.mem_nhds hs₁)
  have hprod := analyticAt_eulerProduct χ s
  have horder := hprod.analyticOrderAt_eq_zero.mpr (eulerProduct_ne_zero χ hs)
  unfold analyticOrderNatAt primitiveMult
  rw [analyticOrderAt_congr heq, ← Pi.mul_def, analyticOrderAt_mul ha hprod, horder, add_zero]
  rfl

/-- The negative logarithmic derivative at level `q` is the primitive one minus
the sum of the logarithmic derivatives of the extra Euler factors. -/
theorem negLogDeriv_lFunction_eq {s : ℂ} (hs : 0 < s.re) (hs₁ : s ≠ 1)
    (hne : primitiveL χ s ≠ 0) :
    -logDeriv χ.LFunction s = -logDeriv (primitiveL χ) s -
      ∑ p ∈ q.primeFactors,
        χ.primitiveCharacter p * (p : ℂ) ^ (-s) * (Real.log p : ℂ) / eulerFactor χ p s := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have heq : χ.LFunction =ᶠ[𝓝 s] fun z ↦ primitiveL χ z * eulerProduct χ z := by
    filter_upwards [isOpen_compl_singleton.mem_nhds (show s ∈ ({1} : Set ℂ)ᶜ from hs₁)]
      with z hz using lFunction_eq_primitive_mul χ (.inl hz)
  have hlogs : logDeriv (eulerProduct χ) s = ∑ p ∈ q.primeFactors, logDeriv (eulerFactor χ p) s :=
    logDeriv_fun_prod (fun p hp ↦ eulerFactor_ne_zero χ (Nat.prime_of_mem_primeFactors hp) hs)
      (fun p hp ↦
        (hasDerivAt_eulerFactor χ (Nat.prime_of_mem_primeFactors hp).pos s).differentiableAt)
  have hsum : (∑ p ∈ q.primeFactors, logDeriv (eulerFactor χ p) s) =
      ∑ p ∈ q.primeFactors,
        χ.primitiveCharacter p * (p : ℂ) ^ (-s) * (Real.log p : ℂ) / eulerFactor χ p s := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [logDeriv_apply, (hasDerivAt_eulerFactor χ (Nat.prime_of_mem_primeFactors hp).pos s).deriv]
  rw [(logDeriv_congr_nhds heq).self_of_nhds, logDeriv_fun_mul _ hne (eulerProduct_ne_zero χ hs)
    (χ.primitiveCharacter.differentiableAt_LFunction s (.inl hs₁))
    (analyticAt_eulerProduct χ s).differentiableAt, hlogs, hsum]
  abel

/-- On the regular part of the positive half-plane, equation (1) of the binary proof. -/
theorem D_eq_primitive_average {s : ℂ} (hs : 0 < s.re) (hs₁ : s ≠ 1)
    (hne : ∀ χ : DirichletCharacter ℂ q, primitiveL χ s ≠ 0) :
    D q s = (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
      (-logDeriv (primitiveL χ) s - ∑ p ∈ q.primeFactors,
        χ.primitiveCharacter p * (p : ℂ) ^ (-s) * (Real.log p : ℂ) / eulerFactor χ p s) := by
  unfold D
  simp_rw [negLogDeriv_lFunction_eq _ hs hs₁ (hne _)]

end GoldbachBoundaries.ResidueClass
