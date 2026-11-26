import GoldbachBoundaries.Paper2.Defs
import GoldbachBoundaries.Statements
import GoldbachBoundaries.Paper2.M1.Skeleton
import GoldbachBoundaries.Paper2.M2.Skeleton
import GoldbachBoundaries.Paper2.M3.Skeleton
import GoldbachBoundaries.Paper2.M4a.Skeleton
import GoldbachBoundaries.Paper2.M4b.Skeleton
import GoldbachBoundaries.Paper2.M5.Skeleton
import GoldbachBoundaries.Paper2.M6.Skeleton

/-!
Reading guide:

* Section 1: sanity lemmas with real proofs (the definitions mean what they should; hypotheses can be met).
* Section 2: preliminaries, `nr:lem:Q`, `nr:lem:MB`.
* Section 3: `T` without RH: `nr:lem:B`, `nr:lem:growthQ`, `nr:thm:cont`, `nr:thm:residue`, `nr:cor:1+u`,
  `nr:lem:rigidity`, `nr:thm:single`, `nr:cor:LW`, `nr:lem:far`, `nr:thm:boundary` (Theorem B), `nr:lem:A`,
  `nr:thm:real`, `nr:lem:hsq`, `nr:lem:Landau`, `nr:thm:test`, `nr:cor:test`, `nr:rem:classical`(ii), (iii),
  `nr:prop:dichotomy`(i), (ii), `nr:prop:Lambda`.
* Section 4: the class: the two sufficient conditions for (H2-log), `cl:prop:catalogue`, `cl:lem:J`, `cl:thm:class`
  (Theorem D), `cl:thm:mero` (Theorem E), `cl:lem:P`, `cl:cor:domain`, the examples (with Theorem E for `T`, from the
  introduction), `cl:prop:T0`, `cl:rem:order` (`G₀` and the `r`-th power kernels `k_r`), `cl:lem:Qleft`,
  `cl:thm:filter` (Theorem F) with `D_H` as a double prime series, `cl:lem:kernelt`, `cl:thm:Tk` (Theorem G).
* Section 5: the introduction's Theorems A, C, D, F assembled from their parts by real (one-line) proofs.
  Theorems B, E and G are the same statements as `nr:thm:boundary`, `cl:thm:mero` and `cl:thm:Tk`.

Statements proved from sorried parts (their own proofs are real): `intro_thm_A`, `intro_thm_C`, `intro_thm_D`,
`intro_thm_F`, `rem_dichotomy_i`, `intro_T_strip`, `rem_order_G0`, `cor_one_add_values`, `rem_order_kr_coeff_ne`,
`rem_order_kr_model`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2

open GoldbachBoundaries

/-! ## 1. Sanity lemmas -/

/-- Sanity: RH implies `(H_∞)` (the paper: "`(H_∞)` follows from RH"). So `(H_∞)` is consistent with RH. -/
theorem hinf_of_RH (hRH : RiemannHypothesis) : Hinf := by
  intro δ hδ
  convert Set.finite_empty
  ext ρ
  simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_lt]
  intro hρ
  rw [re_eq_half_of_mem_nontrivialZeros hRH hρ]
  linarith

/-- Sanity (non-vacuity of `IsQCont`, the hypothesis of every statement that quantifies over continuations of
`Q`): paper 1's `Qcont z = ∑ μ(n) (-ζ'/ζ)(nz)` is one, unconditionally. -/
theorem exists_isQCont : ∃ Qc : ℂ → ℂ, IsQCont Qc := by
  refine ⟨Qcont, fun z hz => meromorphicAt_Qcont hz, fun z hz => ?_, fun z hz => ?_⟩
  · have hz' : 1 < z.re := hz
    show Qcont z = Q z
    rw [Q_eq_tsum_moebius_zeta hz']
    simp only [Qcont, sigmaTerm, negLogDerivZeta, neg_div]
  · have h0 : 0 < z.re := hz.1
    have h := analyticAt_Qcont_sub_sum h0 ∅
      (fun n _ hmu => regular_of_not_mem_poleSetQ h0 hz.2 hmu)
    simpa using h

/-- Sanity: a function analytic at a point of `Ω ∩ S` is an admissible germ of itself there (constant path), so
`IsAdmissibleGermOn` is not vacuous. -/
theorem isAdmissibleGermOn_self {F : ℂ → ℂ} {Ω S : Set ℂ} {s : ℂ} (hF : AnalyticAt ℂ F s)
    (hΩ : s ∈ Ω) (hS : s ∈ S) : IsAdmissibleGermOn F Ω S F s :=
  ⟨ContinuousMap.const _ s, fun _ => hΩ, hS, rfl, fun _ => F,
    ⟨fun _ => hF, fun _ => Eventually.of_forall (fun _ => EventuallyEq.rfl)⟩,
    EventuallyEq.rfl, EventuallyEq.rfl⟩

lemma two_notMem_poleSetQ : (2 : ℂ) ∉ PoleSetQ := by
  rintro ((h | ⟨k, hk, -, h⟩) | ⟨n, hn, -, ρ, hρ, h⟩)
  · norm_num at h
  · have hre := congrArg Complex.re h
    have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
    have : (1 / (k : ℂ)).re = 1 / (k : ℝ) := by simp [Complex.normSq_natCast]
    rw [this] at hre
    have : 1 / (k : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hk'
    rw [one_div] at this
    norm_num at hre
    linarith
  · have hre := congrArg Complex.re h
    simp only [Complex.div_natCast_re] at hre
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hρre : ρ.re = 2 * n := by
      have : ρ.re / n = 2 := by norm_num at hre; linarith
      field_simp at this; linarith
    linarith [hρ.2.2]

/-- Sanity: the series `P` itself, at `z₁ = 2`, is a branch of `P` (non-vacuity of `IsPBranch`). -/
theorem isPBranch_P_two : IsPBranch P 2 := by
  refine isAdmissibleGermOn_self ?_ ⟨?_, two_notMem_poleSetQ⟩ ?_
  · exact P_differentiableOn.analyticAt
      ((isOpen_halfPlane 1).mem_nhds (by show (1 : ℝ) < (2 : ℂ).re; norm_num))
  · show (0 : ℝ) < (2 : ℂ).re; norm_num
  · show (1 : ℝ) < (2 : ℂ).re; norm_num

/-- Sanity: `R_1 = 1` from the definition (eq. `(nr:eq:Ra)`): only `k = 1` contributes, with `ord_1 ζ = -1`. -/
theorem Rcoef_one : Rcoef 1 = 1 := by
  have hz : ∀ k : ℕ, k ≠ 0 →
      mu (k + 1) / ((k + 1 : ℕ) : ℂ) * (ordZeta (((k + 1 : ℕ) : ℂ) * 1) : ℂ) = 0 := by
    intro k hk
    have h1 : ((k + 1 : ℕ) : ℂ) * 1 ≠ 1 := by
      rw [mul_one]; exact_mod_cast (by omega : k + 1 ≠ 1)
    have h2 : ((k + 1 : ℕ) : ℂ) * 1 ∉ NontrivialZeros := by
      rintro ⟨-, -, h⟩
      simp only [mul_one, Complex.natCast_re] at h
      have : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ k + 1)
      linarith
    simp only [mul_one, Nat.cast_add, Nat.cast_one] at h2
    simp [ordZeta, hk, h2]
  rw [Rcoef, tsum_eq_single 0 hz]
  simp [ordZeta]

/-- Sanity: `c₁ = -1`. -/
theorem cP_one : cP 1 = -1 := by rw [cP, Rcoef_one]

/-- Sanity: the class instance `L(s) = s` with the kernel `K_s` and the weight `(p+q)^{-s}` gives paper 1's `G`. -/
theorem Dser_WG : Dser WG = G := rfl

/-- Sanity: the log weight gives paper 1's `T`. -/
theorem Dser_WT : Dser WT = T := rfl

/-- Sanity: `T₁ = Q` (the paper: "so that `T₁ = Q`"). -/
theorem Tk_one : Tk 1 = Q := by
  funext s
  rw [Tk, Q, ← (Equiv.funUnique (Fin 1) Nat.Primes).symm.tsum_eq]
  congr 1
  funext p
  simp [Equiv.funUnique]

/-- Sanity: `T₂ = T` (the paper: "and `T₂ = T`"). -/
theorem Tk_two : Tk 2 = T := by
  funext s
  rw [Tk, T, ← (finTwoArrowEquiv Nat.Primes).symm.tsum_eq]
  congr 1
  funext p
  simp [finTwoArrowEquiv, Fin.prod_univ_two, Fin.sum_univ_two]

/-- The polynomial `H₀(z, w) = (z - 1)(w - 1)` of `T₀`. -/
def H0 : MvPolynomial (Fin 2) ℂ := (MvPolynomial.X 0 - 1) * (MvPolynomial.X 1 - 1)

/-- Sanity: `H₀` gives the kernel `k₀` of `W₀` (the paper: "For `H₀(z,w) = (z-1)(w-1)` the kernel is `k₀`"). -/
theorem kH_H0 : kH H0 = k0 := by
  funext z s
  simp [kH, k0, evalH, H0]
  ring

/-- Sanity: `H₀` satisfies the conditions of Section 4.9 (non-zero, symmetric, `H(1, w) ≡ 0`). -/
theorem H0_conditions :
    H0 ≠ 0 ∧ (∀ z w, evalH H0 z w = evalH H0 w z) ∧ ∀ w, evalH H0 1 w = 0 := by
  refine ⟨?_, fun z w => by simp [evalH, H0]; ring, fun w => by simp [evalH, H0]⟩
  intro h
  have := congrArg (MvPolynomial.eval ![(2 : ℂ), 2]) h
  norm_num [H0] at this

/-- Sanity: the bracket of `k₀` vanishes identically (part of `cl:prop:T0`, proved here). -/
theorem bracket_k0 (s : ℂ) : bracket Aff.idL k0 s = 0 := by
  simp [bracket, k0, Aff.app, Aff.idL]

/-- Sanity: the bracket of the Goldbach kernel is `2/(s-1)` on `σ > 1` (part of `cl:ex:G`, proved here). -/
theorem bracket_kerG {s : ℂ} (hs : 1 < s.re) : bracket Aff.idL kerG s = 2 / (s - 1) := by
  have hre : 0 < (s - 1).re := by simp; linarith
  have hne : s - 1 ≠ 0 := fun h => by rw [h] at hre; simp at hre
  have hΓ : Gamma s = (s - 1) * Gamma (s - 1) := by
    have := Complex.Gamma_add_one (s - 1) hne
    rwa [sub_add_cancel] at this
  have hΓ0 : Gamma (s - 1) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hre
  simp only [bracket, kerG, KerS, Aff.app, Aff.idL]
  rw [hΓ]
  simp only [Complex.ofReal_one, Complex.ofReal_zero, one_mul, add_zero]
  rw [show s - (s - 1) = 1 by ring, Complex.Gamma_one]
  field_simp
  norm_num

/-- Sanity (the counting function `N(t)` of (Z2) is not a junk `∑ᶠ`): the zeros with `0 < γ ≤ t` form a finite
set (Mathlib's `IsCompact.inter_riemannZetaZeros_finite`). `N₀(t)` counts a subset. -/
theorem nzero_set_finite (t : ℝ) :
    {ρ : ℂ | ρ ∈ NontrivialZeros ∧ 0 < ρ.im ∧ ρ.im ≤ t}.Finite := by
  refine ((isCompact_Icc.reProdIm isCompact_Icc :
    IsCompact ((Icc (0 : ℝ) 1) ×ℂ (Icc 0 t))).inter_riemannZetaZeros_finite).subset ?_
  rintro ρ ⟨hρ, h0, ht⟩
  exact ⟨by simp [mem_reProdIm, hρ.2.1.le, hρ.2.2.le, h0.le, ht], hρ.1⟩

/-- Sanity (the sum in (Z3) is not a junk `∑ᶠ`): finitely many zeros have `|γ - Im z| ≤ 1`. -/
theorem z3_set_finite (z : ℂ) :
    {ρ : ℂ | ρ ∈ NontrivialZeros ∧ |ρ.im - z.im| ≤ 1}.Finite := by
  refine ((isCompact_Icc.reProdIm isCompact_Icc :
    IsCompact ((Icc (0 : ℝ) 1) ×ℂ (Icc (z.im - 1) (z.im + 1)))).inter_riemannZetaZeros_finite).subset ?_
  rintro ρ ⟨hρ, h⟩
  rw [abs_le] at h
  refine ⟨?_, hρ.1⟩
  simp only [mem_reProdIm, mem_Icc]
  exact ⟨⟨hρ.2.1.le, hρ.2.2.le⟩, by linarith, by linarith⟩

/-- Sanity ((Z7) "has positive terms"): `m(ρ) Re(1/ρ) > 0` at every non-trivial zero, so the `HasSum` of (Z7) is
over positive terms and `C₀ > 0` is forced. -/
theorem z7_terms_pos {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) : 0 < (zetaMult ρ : ℝ) * (1 / ρ).re := by
  have hm : (1 : ℝ) ≤ zetaMult ρ := by exact_mod_cast one_le_zetaMult hρ
  have hne : ρ ≠ 0 := ne_zero_of_mem_nontrivialZeros hρ
  have hre : 0 < (1 / ρ).re := by
    rw [one_div, Complex.inv_re]
    exact div_pos hρ.2.1 (Complex.normSq_pos.mpr hne)
  positivity

/-- The Goldbach kernel `K_s(z)` is jointly holomorphic on `{0 < Re z < Re s}`. -/
lemma differentiableOn_kerG :
    DifferentiableOn ℂ (fun p : ℂ × ℂ => kerG p.1 p.2) {p | 0 < p.1.re ∧ p.1.re < p.2.re} := by
  intro p hp
  obtain ⟨h1, h2⟩ := hp
  have hG : ∀ w : ℂ, 0 < w.re → DifferentiableAt ℂ Gamma w := fun w hw =>
    differentiableAt_Gamma _ (fun m h => by rw [h] at hw; simp at hw; linarith [(m.cast_nonneg : (0:ℝ) ≤ m)])
  have hs : 0 < p.2.re := by linarith
  have hsz : 0 < (p.2 - p.1).re := by simp; linarith
  have hd1 : DifferentiableAt ℂ (fun q : ℂ × ℂ => Gamma q.1) p :=
    (hG _ h1).comp p differentiableAt_fst
  have hd2 : DifferentiableAt ℂ (fun q : ℂ × ℂ => Gamma (q.2 - q.1)) p :=
    (hG _ hsz).comp p (differentiableAt_snd.sub differentiableAt_fst)
  have hd3 : DifferentiableAt ℂ (fun q : ℂ × ℂ => Gamma q.2) p := (hG _ hs).comp p differentiableAt_snd
  have hne : Gamma p.2 ≠ 0 := Gamma_ne_zero_of_re_pos hs
  refine DifferentiableAt.differentiableWithinAt ?_
  show DifferentiableAt ℂ (fun q : ℂ × ℂ => Gamma q.1 * Gamma (q.2 - q.1) / Gamma q.2) p
  simp only [div_eq_mul_inv]
  exact (hd1.mul hd2).mul (hd3.inv hne)

/-- Sanity (non-vacuity of (K1)): the Goldbach kernel satisfies (K1) (part of `cl:ex:G`, proved here). -/
theorem K1_kerG : K1 Aff.idL kerG := by
  refine differentiableOn_kerG.mono ?_
  rintro ⟨z, s⟩ ⟨-, hz0, hz1⟩
  simp [Aff.app, Aff.idL] at hz1 ⊢
  exact ⟨hz0, hz1⟩

/-- Sanity: the Goldbach kernel satisfies (H2a) (part of `cl:ex:G`, proved here). -/
theorem H2a_kerG : H2a Aff.idL kerG := by
  refine differentiableOn_kerG.mono ?_
  rintro ⟨z, s⟩ ⟨-, hz0, hz1⟩
  simp [Aff.app, Aff.idL] at hz1 ⊢
  exact ⟨hz0, hz1⟩

/-- Sanity (non-vacuity of (K3)): the Goldbach kernel satisfies (K3) (part of `cl:ex:G`, proved here). -/
theorem K3_kerG : K3 Aff.idL kerG := by
  intro s _ z _
  simp only [kerG, KerS, map_div₀, map_mul, ← Complex.Gamma_conj, map_sub]

/-- Sanity: the bracket of the kernel of `∑(p²+q²)^{-s}` is `√π Γ(s - 1/2)/Γ(s)` and non-zero on `ℍ_L = {σ > 1/2}`
(part of `cl:ex:squares`, proved here). At `s = 1/2` the paper's `𝔟` has a pole and Lean's value is the junk
`Γ(0) = 0`, which is why the statement is on `ℍ_L` only. -/
theorem bracket_kerSq {s : ℂ} (hs : 1 / 2 < s.re) :
    bracket Aff.twoL kerSq s = (Real.sqrt Real.pi : ℂ) * Gamma (s - 1 / 2) / Gamma s ∧
      bracket Aff.twoL kerSq s ≠ 0 := by
  have hform :
      bracket Aff.twoL kerSq s = (Real.sqrt Real.pi : ℂ) * Gamma (s - 1 / 2) / Gamma s := by
    simp only [bracket, kerSq, Aff.app, Aff.twoL]
    have e1 : ((2 : ℝ) : ℂ) * s + ((0 : ℝ) : ℂ) - 1 = 2 * s - 1 := by push_cast; ring
    rw [e1, show s - (2 * s - 1) / 2 = 1 / 2 by ring, show (2 * s - 1) / 2 = s - 1 / 2 by ring,
      Complex.Gamma_one_half_eq]
    have : ((Real.sqrt Real.pi : ℝ) : ℂ) = (Real.pi : ℂ) ^ (1 / 2 : ℂ) := by
      rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (le_of_lt Real.pi_pos)]
      push_cast; ring_nf
    rw [this]
    ring
  refine ⟨hform, ?_⟩
  rw [hform]
  have h1 : Gamma (s - 1 / 2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have h2 : Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
  have h3 : (Real.sqrt Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  exact div_ne_zero (mul_ne_zero h3 h1) h2

lemma idL_app (s : ℂ) : Aff.idL.app s = s := by simp [Aff.app, Aff.idL]

lemma idL_HL : Aff.idL.HL = HH := by ext s; simp [Aff.HL, idL_app, halfPlane]

lemma idL_RL : Aff.idL.RL = halfPlane 2 := by ext s; simp [Aff.RL, idL_app, halfPlane]

/-- Sanity: the kernel `k₀` of `W₀` satisfies (H2a) (it is `K_s(z)` times a polynomial; used for `G₀`,
`cl:rem:order`). -/
theorem H2a_k0 : H2a Aff.idL k0 := by
  have h := H2a_kerG
  unfold H2a at h ⊢
  have : (fun p : ℂ × ℂ => k0 p.1 p.2) = fun p => kerG p.1 p.2 * (p.1 - 1) * (p.2 - 1 - p.1) := by
    funext p; simp [k0, kerG]
  rw [this]
  exact (h.mul (differentiable_fst.sub_const 1).differentiableOn).mul
    ((differentiable_snd.sub_const 1).sub differentiable_fst).differentiableOn

/-- Sanity: the `r`-th power kernel of `cl:rem:order` at `r = 1` is `k₀`. -/
theorem kr_one : kr 1 = k0 := by
  funext z s; simp [kr, k0]; ring

/-- Sanity: the `r`-th power kernel `k_r` satisfies (H2a) (`K_s(z)` times a polynomial), for every `r`. -/
theorem H2a_kr (r : ℕ) : H2a Aff.idL (kr r) := by
  have h := H2a_kerG
  unfold H2a at h ⊢
  have : (fun p : ℂ × ℂ => kr r p.1 p.2) =
      fun p => kerG p.1 p.2 * ((p.1 - 1) * (p.2 - 1 - p.1)) ^ r := by
    funext p; simp [kr, kerG]
  rw [this]
  exact h.mul (((differentiable_fst.sub_const 1).mul
    ((differentiable_snd.sub_const 1).sub differentiable_fst)).pow r).differentiableOn

/-- Sanity: `k_r` satisfies (K1) (from (H2a), since `D_L ⊆ ℍ_L`). -/
theorem K1_kr (r : ℕ) : K1 Aff.idL (kr r) := by
  refine (H2a_kr r).mono ?_
  rintro ⟨z, s⟩ ⟨hs, hz⟩
  exact ⟨hs.1, hz⟩

/-- Sanity: `k_r` satisfies (K3). -/
theorem K3_kr (r : ℕ) : K3 Aff.idL (kr r) := by
  intro s _ z _
  simp only [kr, KerS, map_div₀, map_mul, map_pow, ← Complex.Gamma_conj, map_sub, map_one]

/-- The points of `Σ_Q` are non-zero. -/
lemma ne_zero_of_mem_poleSetQ {b : ℂ} (hb : b ∈ PoleSetQ) : b ≠ 0 := by
  rintro rfl
  rcases hb with ((h | ⟨k, hk, -, h⟩) | ⟨n, hn, -, ρ, hρ, h⟩)
  · norm_num at h
  · have : (k : ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    exact one_div_ne_zero this h.symm
  · have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    exact div_ne_zero (ne_zero_of_mem_nontrivialZeros hρ) hn0 h.symm

/-- Non-trivial zeros are not real (`ζ(x) ≠ 0` on `(0,1)`, paper 1's library). -/
lemma im_ne_zero_of_mem_nontrivialZeros {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) : ρ.im ≠ 0 := by
  intro h
  have hρeq : ρ = (ρ.re : ℂ) := by apply Complex.ext <;> simp [h]
  apply riemannZeta_ne_zero_of_mem_Ioo ⟨hρ.2.1, hρ.2.2⟩
  rw [← hρeq]; exact hρ.1

/-- Sanity: at `r = 1` the leading coefficient `2c₁c_b(b-1)^r/(b(r+1))` of `rem_order_kr_coeff` is the coefficient
`c₁c_b(b-1)/b` of `rem_order_coeff` (and `k_1 = k₀`, `kr_one`), so the `r`-family extends the `k₀` statement. -/
theorem rem_order_kr_const_one (b : ℂ) (hb : b ≠ 0) :
    2 * cP 1 * cP b * (b - 1) ^ 1 / (b * (((1 : ℕ) : ℂ) + 1)) = cP 1 * cP b * ((b - 1) / b) := by
  push_cast; field_simp; ring

/-- Sanity: `H₀ = (z-1)(w-1) = z^{(1)}w^{(1)} - z^{(1)} - w^{(1)} + 1` in the rising-factorial basis, i.e.
`h_{ij} = (-1)^{i+j}` for `i, j < 2` (non-vacuity of `IsRisingRep`). -/
theorem isRisingRep_H0 : IsRisingRep H0 2 (fun i j => (-1 : ℂ) ^ (i + j)) := by
  intro z w
  simp [evalH, H0, Finset.sum_range_succ]
  ring

/-- Sanity: for `H₀` the weight `W_H` is `W₀` (at `σ > 0`, where `Γ(s) ≠ 0`, and `p + q > 0`), as the remark after
`cl:thm:filter` implies. -/
theorem WH_H0 {s : ℂ} (hs : 0 < s.re) {p q : ℕ} (hpq : 0 < p + q) :
    WH 2 (fun i j => (-1 : ℂ) ^ (i + j)) s p q = W0 s p q := by
  have hs0 : s ≠ 0 := fun h => by rw [h] at hs; simp at hs
  have hs1 : s + 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hΓ : Gamma s ≠ 0 := Gamma_ne_zero_of_re_pos hs
  have g1 : Gamma (s + 1) = s * Gamma s := Gamma_add_one s hs0
  have g2 : Gamma (s + 1 + 1) = (s + 1) * (s * Gamma s) := by rw [Gamma_add_one _ hs1, g1]
  have hN : (p : ℂ) + q ≠ 0 := by exact_mod_cast hpq.ne'
  have c1 : ((p : ℂ) + q) ^ (-(s + 1)) = ((p : ℂ) + q) ^ (-s) / ((p : ℂ) + q) := by
    rw [show -(s + 1) = -s - 1 by ring, cpow_sub _ _ hN, cpow_one]
  have c2 : ((p : ℂ) + q) ^ (-(s + 1 + 1)) = ((p : ℂ) + q) ^ (-s) / ((p : ℂ) + q) ^ 2 := by
    rw [show -(s + 1 + 1) = -s - 2 by ring, cpow_sub _ _ hN]
    norm_cast
  simp only [WH, W0, Finset.sum_range_succ, Finset.sum_range_zero]
  push_cast
  simp only [add_zero, zero_add, pow_zero, pow_one, mul_one, one_mul]
  rw [c1, c2, g1, g2]
  field_simp
  ring

/-- Sanity: `Λ₀ > 0` (the terms of the sum are non-negative; this does not need summability). -/
theorem Lambda0_pos : 0 < Lambda0 := by
  have : 0 ≤ ∑' ρ, lambda0Term ρ := tsum_nonneg fun ρ => by unfold lambda0Term; positivity
  unfold Lambda0
  have := Real.pi_pos
  positivity

/-! ## 2. Preliminaries: `nr:lem:Q`, `nr:lem:MB` -/

/-- **`nr:lem:Q` (i)** (paper, verbatim; unconditional):

\textup{(i)} $Q$ is a single-valued meromorphic function on $\{\Re z>0\}$, real on $(0,\infty)$
off its poles, with $Q(\bar z)=\overline{Q(z)}$. Its poles are simple and lie in $\Sigma_Q$; for
$a\in\Sigma_Q$, $\Res_{z=a}Q=R_a$, so the poles of $Q$ are exactly the points of $\Sigma_Q^*$.
Each $R_a$ is real, $R_{\bar a}=R_a$, $R_1=1$ and $R_{1/k}=\mu(k)/k$; for non-real $a$ the sum
\eqref{nr:eq:Ra} runs over the squarefree $k<1/\Re a$ for which $ka$ is a zero.

Lean: for *every* continuation `Qc` of `Q` (`IsQCont`: meromorphic on `Re z > 0`, the series on `Re z > 1`,
analytic off `Σ_Q`; one exists, `exists_isQCont`): conjugation symmetry off `Σ_Q` (which gives "real on
`(0,∞)` off its poles", since the real points of `Σ_Q` are poles), order `≥ -1` and residue `R_a` at each
`a ∈ Σ_Q`, and a pole at `a ∈ Σ_Q` exactly when `R_a ≠ 0`. Then the facts about the numbers `R_a`. `R_1 = 1`
is also proved outright (`Rcoef_one`). Hypothesis (Z1) for the reality statements (multiplicity of `ρ̄`). -/
theorem lem_Q_i (hZ1 : Z1) :
    (∀ Qc : ℂ → ℂ, IsQCont Qc →
      (∀ z ∈ halfPlane 0 \ PoleSetQ, Qc (conj z) = conj (Qc z)) ∧
      ∀ a ∈ PoleSetQ, -1 ≤ meromorphicOrderAt Qc a ∧ HasResidue Qc a (Rcoef a) ∧
        (meromorphicOrderAt Qc a < 0 ↔ Rcoef a ≠ 0)) ∧
    (∀ a ∈ PoleSetQ, (Rcoef a).im = 0 ∧ Rcoef (conj a) = Rcoef a) ∧
    Rcoef 1 = 1 ∧
    (∀ k : ℕ, 2 ≤ k → Squarefree k → Rcoef (1 / (k : ℂ)) = mu k / k) ∧
    ∀ a ∈ PoleSetQ, a.im ≠ 0 →
      Rcoef a = -∑ᶠ k ∈ {k : ℕ | 1 ≤ k ∧ Squarefree k ∧ (k : ℝ) < 1 / a.re ∧
          (k : ℂ) * a ∈ NontrivialZeros}, mu k / k * (zetaMult ((k : ℂ) * a) : ℂ) := by
  exact M1.lem_Q_i_proof hZ1

/-- **`nr:lem:Q` (ii)** (paper, verbatim; unconditional):

\textup{(ii)} $\Sigma_Q$ is locally finite in $\{\Re z>0\}$. Every point of
$\Sigma_Q\setminus\{1\}$ has real part at most $B:=\sup_\rho\beta$, and every point of
$\Sigma_Q$ that is not $1$ and not a zero $\rho$ has real part at most $\frac12$.

Lean: (Z1) is a premise because the bound `1/k ≤ 1/2 ≤ B` needs a zero with `β ≥ 1/2` (from `1 - ρ̄`). -/
theorem lem_Q_ii (hZ1 : Z1) :
    (∀ z ∈ halfPlane 0, ∃ U ∈ 𝓝 z, (U ∩ PoleSetQ).Finite) ∧
    (∀ a ∈ PoleSetQ, a ≠ 1 → a.re ≤ Bsup) ∧
    ∀ a ∈ PoleSetQ, a ≠ 1 → a ∉ NontrivialZeros → a.re ≤ 1 / 2 := by
  exact M1.lem_Q_ii_proof hZ1

/-- **`nr:lem:Q` (iii)** (paper, verbatim; unconditional):

\textup{(iii)} For $\varepsilon\in(0,1)$ there is $C(\varepsilon)$ such that $|R_a|\le
C(\varepsilon)\log(|\Im a|+3)$ for every $a\in\Sigma_Q$ with $\Re a\ge\varepsilon$, and such that
for every real $t$ at most $C(\varepsilon)\log(|t|+3)$ points $a\in\Sigma_Q$ have $\Re a\ge\varepsilon$
and $t\le\Im a\le t+1$.

Lean: "at most `N` points" is stated as `Set.Finite` plus a bound on `Set.ncard` (a bare `ncard` bound would be
vacuous for an infinite set). Hypotheses (Z2), and (Z1): the proof uses the multiplicity bound
`m(ρ) ≤ 2C₁ log(|γ|+3)` that the paper derives from (Z2) at negative heights as well, while Lean's `Z2` counts only
zeros with `0 < γ ≤ t`, so the bound at `γ < 0` needs `m(ρ̄) = m(ρ)`, which is (Z1). -/
theorem lem_Q_iii (hZ1 : Z1) (hZ2 : Z2) :
    ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ C : ℝ,
      (∀ a ∈ PoleSetQ, ε ≤ a.re → ‖Rcoef a‖ ≤ C * Real.log (|a.im| + 3)) ∧
      ∀ t : ℝ, {a | a ∈ PoleSetQ ∧ ε ≤ a.re ∧ t ≤ a.im ∧ a.im ≤ t + 1}.Finite ∧
        ({a | a ∈ PoleSetQ ∧ ε ≤ a.re ∧ t ≤ a.im ∧ a.im ≤ t + 1}.ncard : ℝ) ≤
          C * Real.log (|t| + 3) := by
  exact M2.lem_Q_iii_proof hZ1 hZ2

/-- **`nr:lem:MB`** (paper, verbatim; unconditional):

For $\sigma>2$ and $1<c<\sigma-1$,
\begin{equation}\label{nr:eq:MB}
  T(s)=\frac1{2\pi i}\int_{(c)}K_s(w)\,Q(w)\,Q(s-w)\,dw,
\end{equation}
the integral over the line $\Re w=c$, absolutely convergent.

Lean: absolute convergence is `Integrable` of the integrand along the line; the integral is PNT+'s
`VerticalIntegral'` (which includes the factor `1/(2πi)`). On the line both `Q`'s are the convergent series.
Hypothesis (Z6) (the paper's proof uses it for the kernel). -/
theorem lem_MB (hZ6 : Z6) {s : ℂ} (hs : 2 < s.re) {c : ℝ} (hc1 : 1 < c) (hc2 : c < s.re - 1) :
    Integrable (fun t : ℝ => KerS s (c + t * I) * Q (c + t * I) * Q (s - (c + t * I))) ∧
      T s = VerticalIntegral' (fun w => KerS s w * Q w * Q (s - w)) c := by
  exact M1.lem_MB_proof hZ6 hs hc1 hc2

/-! ## 3. The weighted series `T` without RH -/

/-- **`nr:lem:B` (i)** (paper, verbatim; unconditional):

\textup{(i)} $\frac12\le B_\infty\le B\le1$, and for every $\delta>0$ only finitely many zeros have
$\beta>B_\infty+\delta$.

Hypothesis (Z1) (the proof pairs `ρ` with `1 - ρ̄`). -/
theorem lem_B_i (hZ1 : Z1) :
    1 / 2 ≤ Binf ∧ Binf ≤ Bsup ∧ Bsup ≤ 1 ∧
      ∀ δ : ℝ, 0 < δ → {ρ | ρ ∈ NontrivialZeros ∧ Binf + δ < ρ.re}.Finite := by
  exact M1.lem_B_i_proof hZ1

/-- **`nr:lem:B` (ii)** (paper, verbatim):

\textup{(ii)} For every $\delta>0$ the set $F_\delta$ is finite, and every point of
$\Sigma_Q\setminus F_\delta$ has real part at most $B_\infty+\delta$. For $0<\delta<1-B_\infty$,
$F_\delta=\{1\}\cup\{\rho:\ \beta>B_\infty+\delta\}$.

Hypothesis (Z1) (through (i) and `nr:lem:Q`(ii)). -/
theorem lem_B_ii (hZ1 : Z1) :
    ∀ δ : ℝ, 0 < δ → (Fdelta δ).Finite ∧ (∀ a ∈ PoleSetQ \ Fdelta δ, a.re ≤ Binf + δ) ∧
      (δ < 1 - Binf → Fdelta δ = {1} ∪ {ρ | ρ ∈ NontrivialZeros ∧ Binf + δ < ρ.re}) := by
  exact M1.lem_B_ii_proof hZ1

/-- **`nr:lem:B` (iii)** (paper, verbatim):

\textup{(iii)} $(\mathrm H_\infty)$ implies $B<1$. -/
theorem lem_B_iii (hH : Hinf) : Bsup < 1 := by
  exact M1.lem_B_iii_proof hH

/-- **`nr:lem:B` (iv)** (paper, verbatim):

\textup{(iv)} If $B>B_\infty$, then $\frac12<B<1$, and $\beta=B$ for finitely many zeros, at least one.

Hypothesis (Z1) (through (i)). -/
theorem lem_B_iv (hZ1 : Z1) (h : Binf < Bsup) :
    1 / 2 < Bsup ∧ Bsup < 1 ∧ {ρ | ρ ∈ NontrivialZeros ∧ ρ.re = Bsup}.Finite ∧
      {ρ | ρ ∈ NontrivialZeros ∧ ρ.re = Bsup}.Nonempty := by
  exact M1.lem_B_iv_proof hZ1 h

/-- **`nr:lem:growthQ`** (paper, verbatim; unconditional):

Let $\delta>0$ and let $H\ge2$ be such that every zero with $|\gamma|\ge H-1$ has
$\beta\le B_\infty+\delta$. There is a constant $C_\delta$, depending only on $\delta$, such that
\[
  |Q(w)|\le C_\delta\log|\Im w|\qquad\text{for }\Re w\ge B_\infty+2\delta,\ |\Im w|\ge H .
\]

Lean: `C` is chosen after `δ` and before `H` ("depending only on `δ`"). `Q` is any continuation `Qc` (`IsQCont`);
the region contains no point of `Σ_Q` (asserted, so the bound is about genuine values of `Qc`). Hypotheses (Z2),
(Z3) (the proof's), and (Z1) (through `B_∞ ≥ 1/2`, `nr:lem:B`(i), used for the terms `k ≥ 2`). -/
theorem lem_growthQ (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) :
    ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ H : ℝ, 2 ≤ H →
      (∀ ρ ∈ NontrivialZeros, H - 1 ≤ |ρ.im| → ρ.re ≤ Binf + δ) →
      ∀ Qc : ℂ → ℂ, IsQCont Qc → ∀ w : ℂ, Binf + 2 * δ ≤ w.re → H ≤ |w.im| →
        w ∉ PoleSetQ ∧ ‖Qc w‖ ≤ C * Real.log |w.im| := by
  exact M1.lem_growthQ_proof hZ1 hZ2 hZ3

/-- **`nr:thm:cont`** (paper, verbatim; unconditional):

The function $T$ continues to a single-valued meromorphic function on the half-plane
$\{\sigma>2B_\infty\}$, real on the real axis, with $T(\bar s)=\overline{T(s)}$. Its poles there are
simple and lie in $\Pi$. More precisely, let $0<\delta<\frac12(1-B_\infty)$, $F=F_\delta$, and let
$c\in(B_\infty+2\delta,1)$ with $c\neq\Re a$ for every $a\in F$. Then for every $s$ with
\begin{equation}\label{nr:eq:region}
  \sigma>c+B_\infty+2\delta\qquad\text{and}\qquad \sigma\neq c+\Re a\ \ (a\in F),
\end{equation}
\begin{gather}\label{nr:eq:cont}
  T(s)=I_c(s)+\sum_{a\in F}\Big([\Re a>c]+[\sigma-\Re a<c]\Big)\,R_a\,K_s(a)\,Q(s-a),\\
  I_c(s)=\frac1{2\pi i}\int_{(c)}K_s(w)Q(w)Q(s-w)\,dw ,\notag
\end{gather}
where $I_c$ is holomorphic on the set \eqref{nr:eq:region} and each term of the sum is meromorphic
on $\{\sigma>\Re a\}\supset\{\sigma>2B_\infty\}$.

Lean: some `F`, meromorphic on `σ > 2B_∞`, equal to the series `T` on `σ > 2`, analytic off `Π`, of order
`≥ -1` everywhere (poles simple), with `F(s̄) = conj F(s)` off `Π` ("real on the real axis" is this at real
points). The representation is part of the same `∃ F`, so it is asserted pointwise only where every function in
it is analytic: `F` off `Π`, and the continuation `Qc` of `Q` (any `IsQCont`) off `Σ_Q` (for `s ∉ Π` in the
region, `s - a ∉ Σ_Q` and the line integrand avoids `Σ_Q`). Hypotheses (Z1), (Z2), (Z3) (growth of `Q`,
`nr:lem:growthQ`), (Z6) (kernel bound). -/
theorem thm_cont (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6) :
    ∃ F : ℂ → ℂ, MeromorphicOn F (halfPlane (2 * Binf)) ∧ EqOn F T (halfPlane 2) ∧
      AnalyticOnNhd ℂ F (halfPlane (2 * Binf) \ Pinch) ∧
      (∀ s ∈ halfPlane (2 * Binf), -1 ≤ meromorphicOrderAt F s) ∧
      (∀ s ∈ halfPlane (2 * Binf) \ Pinch, F (conj s) = conj (F s)) ∧
      ∀ δ : ℝ, 0 < δ → δ < (1 - Binf) / 2 → ∀ c : ℝ, Binf + 2 * δ < c → c < 1 →
        (∀ a ∈ Fdelta δ, c ≠ a.re) → ∀ Qc : ℂ → ℂ, IsQCont Qc →
        DifferentiableOn ℂ (fun s => VerticalIntegral' (fun w => KerS s w * Qc w * Qc (s - w)) c)
            {s | c + Binf + 2 * δ < s.re ∧ ∀ a ∈ Fdelta δ, s.re ≠ c + a.re} ∧
        (∀ a ∈ Fdelta δ, MeromorphicOn (fun s => Rcoef a * KerS s a * Qc (s - a)) (halfPlane a.re) ∧
          halfPlane (2 * Binf) ⊆ halfPlane a.re) ∧
        ∀ s : ℂ, c + Binf + 2 * δ < s.re → (∀ a ∈ Fdelta δ, s.re ≠ c + a.re) → s ∉ Pinch →
          F s = VerticalIntegral' (fun w => KerS s w * Qc w * Qc (s - w)) c +
            ∑ᶠ a ∈ Fdelta δ, (iverson (c < a.re) + iverson (s.re - a.re < c)) *
              Rcoef a * KerS s a * Qc (s - a) := by
  exact M1.thm_cont_proof hZ1 hZ2 hZ3 hZ6

/-- **`nr:thm:residue`** (paper, verbatim; unconditional):

Let $\Re s_0>2B_\infty$. Then the set of ordered pairs $(a,b)\in\Sigma_Q\times\Sigma_Q$ with
$a+b=s_0$ is finite, and
\begin{equation}\label{nr:eq:residue}
  \Res_{s=s_0}T=\sum_{\substack{(a,b)\in\Sigma_Q^2\\ a+b=s_0}}R_aR_b\,\mathrm B(a,b),
  \qquad \mathrm B(a,b)=\frac{\Gamma(a)\Gamma(b)}{\Gamma(s_0)},
\end{equation}
the pair $(a,a)$, if present, counted once. In particular $s_0$ is a regular point of $T$ when
$s_0\notin\Pi$.

Lean: "`T`" is every meromorphic `F` on `σ > 2B_∞` agreeing with the series off a discrete subset of `σ > 2`
(such `F` exist by `thm_cont`; residues and orders do not depend on the choice). "Regular" is order `≥ 0`.
Hypotheses as for `thm_cont`. -/
theorem thm_residue (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6) {s₀ : ℂ} (hs₀ : 2 * Binf < s₀.re) :
    (pinchPairs s₀).Finite ∧
      ∀ F : ℂ → ℂ, MeromorphicOn F (halfPlane (2 * Binf)) →
        F =ᶠ[codiscreteWithin (halfPlane 2)] T →
        HasResidue F s₀ (pairSum s₀) ∧ (s₀ ∉ Pinch → 0 ≤ meromorphicOrderAt F s₀) := by
  exact M1.thm_residue_proof hZ1 hZ2 hZ3 hZ6 hs₀

/-- **`nr:cor:1+u`**, first sentence (paper, verbatim; unconditional):

Let $u\in\Sigma_Q$ with $1+\Re u>2B_\infty$, and suppose that $(1,u)$ and $(u,1)$ are the only
ordered pairs in $\Sigma_Q^2$ with sum $1+u$ \textup{(}one pair if $u=1$\textup{)}. Then
\[
  \Res_{s=1+u}T=\frac{2R_u}{u}\quad(u\neq1),\qquad \Res_{s=2}T=1 .
\]
[...]

Hypotheses as for `thm_residue`. -/
theorem cor_one_add (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6) {u : ℂ} (hu : u ∈ PoleSetQ)
    (hu2 : 2 * Binf < 1 + u.re) (hpairs : pinchPairs (1 + u) ⊆ {(1, u), (u, 1)})
    (F : ℂ → ℂ) (hF : MeromorphicOn F (halfPlane (2 * Binf)))
    (hFT : F =ᶠ[codiscreteWithin (halfPlane 2)] T) :
    (u ≠ 1 → HasResidue F (1 + u) (2 * Rcoef u / u)) ∧ (u = 1 → HasResidue F 2 1) := by
  exact M1.cor_one_add_proof hZ1 hZ2 hZ3 hZ6 hu hu2 hpairs F hF hFT

/-- **`nr:cor:1+u`**, second sentence (paper, verbatim):

[...] The hypothesis on the pairs holds whenever $1+\Re u>2B$; [...]

Hypothesis (Z1) (through `nr:lem:Q`(ii)). -/
theorem cor_one_add_pairs (hZ1 : Z1) {u : ℂ} (hu : u ∈ PoleSetQ) (h : 2 * Bsup < 1 + u.re) :
    pinchPairs (1 + u) ⊆ {(1, u), (u, 1)} := by
  exact M1.cor_one_add_pairs_proof hZ1 hu h

/-- **`nr:cor:1+u`**, the RH consequences (paper, verbatim):

[...] so it holds for every $u\in\Sigma_Q$ under
RH. In particular, whenever the hypotheses of the corollary hold (so under RH),
$\Res_{1+1/k}T=2\mu(k)$ for squarefree $k\ge2$, and, when $\rho/n$ has the single representation
$(\rho,n)$, $\Res_{1+\rho/n}T=-2\mu(n)m(\rho)/\rho$.

Lean: under RH, for every `F` meromorphic on `ℍ` (which is `{σ > 2B_∞}` under RH) agreeing with the series off a
discrete subset of `σ > 2`, the residues on paper 1's catalogue `𝒞` have paper 1's catalogue values
(`HasCatalogueValues`: `1` at `2`, `2μ(k)` at `1 + 1/k`, `-2μ(n)m(ρ)/ρ` at `1 + ρ/n`); under RH every `ρ/n` has a
single representation. This ties the statement to paper 1's `cor:T-poles`. -/
theorem cor_one_add_RH (hRH : RiemannHypothesis) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6)
    (F : ℂ → ℂ) (hF : MeromorphicOn F HH) (hFT : F =ᶠ[codiscreteWithin (halfPlane 2)] T) :
    ∃ res : ℂ → ℂ, HasCatalogueValues res ∧ ∀ α ∈ catalogue, HasResidue F α (res α) := by
  exact M3.cor_one_add_RH_proof hRH hZ1 hZ2 hZ3 hZ6 F hF hFT

/-- **`nr:cor:1+u`**, the values without RH (paper, verbatim):

[...] In particular, whenever the hypotheses of the corollary hold (so under RH),
$\Res_{1+1/k}T=2\mu(k)$ for squarefree $k\ge2$, and, when $\rho/n$ has the single representation
$(\rho,n)$, $\Res_{1+\rho/n}T=-2\mu(n)m(\rho)/\rho$.

Lean: under the corollary's hypotheses (`1 + Re u > 2B_∞` and the pair condition), with no RH: residue `2μ(k)` at
`1 + 1/k` (`k ≥ 2` squarefree), and `-2μ(n)m(ρ)/ρ` at `1 + ρ/n` when `(ρ, n)` is the only representation of `ρ/n`
(`IsSingleRep`). For every `F` as in `cor_one_add`. Proved from `cor_one_add` and `lem_Q_i` (`R_{1/k} = μ(k)/k`; for
the non-real `ρ/n` the sum `(nr:eq:Ra)` has the single term `k = n`). Hypotheses as for `cor_one_add`. -/
theorem cor_one_add_values (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6)
    (F : ℂ → ℂ) (hF : MeromorphicOn F (halfPlane (2 * Binf)))
    (hFT : F =ᶠ[codiscreteWithin (halfPlane 2)] T) :
    (∀ k : ℕ, 2 ≤ k → Squarefree k → 2 * Binf < 1 + (1 / (k : ℂ)).re →
      pinchPairs (1 + 1 / (k : ℂ)) ⊆ {(1, 1 / (k : ℂ)), (1 / (k : ℂ), 1)} →
      HasResidue F (1 + 1 / (k : ℂ)) (2 * mu k)) ∧
    ∀ n : ℕ, 1 ≤ n → Squarefree n → ∀ ρ ∈ NontrivialZeros, IsSingleRep ρ n →
      2 * Binf < 1 + (ρ / (n : ℂ)).re →
      pinchPairs (1 + ρ / (n : ℂ)) ⊆ {(1, ρ / (n : ℂ)), (ρ / (n : ℂ), 1)} →
      HasResidue F (1 + ρ / (n : ℂ)) (-2 * mu n * (zetaMult ρ : ℂ) / ρ) := by
  obtain ⟨-, -, -, hRk, hRρ⟩ := lem_Q_i hZ1
  refine ⟨fun k hk hsq h2 hp => ?_, fun n hn hsq ρ hρ hsing h2 hp => ?_⟩
  · have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    have hu : 1 / (k : ℂ) ∈ PoleSetQ := Or.inl (Or.inr ⟨k, hk, hsq, rfl⟩)
    have hu1 : 1 / (k : ℂ) ≠ 1 := by
      intro h
      rw [div_eq_one_iff_eq hk0] at h
      have : k = 1 := by exact_mod_cast h.symm
      omega
    have := (cor_one_add hZ1 hZ2 hZ3 hZ6 hu h2 hp F hF hFT).1 hu1
    rw [hRk k hk hsq] at this
    convert this using 1
    field_simp
  · have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    have hρ0 : ρ ≠ 0 := ne_zero_of_mem_nontrivialZeros hρ
    have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hu : ρ / (n : ℂ) ∈ PoleSetQ := Or.inr ⟨n, hn, hsq, ρ, hρ, rfl⟩
    have hre : (ρ / (n : ℂ)).re = ρ.re / n := by simp
    have hu1 : ρ / (n : ℂ) ≠ 1 := by
      intro h
      have h' : ρ = n := by rw [div_eq_one_iff_eq hn0] at h; exact h
      have := congrArg Complex.re h'
      simp only [Complex.natCast_re] at this
      have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith [hρ.2.2]
    have him : (ρ / (n : ℂ)).im ≠ 0 := by
      have : (ρ / (n : ℂ)).im = ρ.im / n := by simp
      rw [this]; exact div_ne_zero (im_ne_zero_of_mem_nontrivialZeros hρ) hnR.ne'
    have hset : {k : ℕ | 1 ≤ k ∧ Squarefree k ∧ (k : ℝ) < 1 / (ρ / (n : ℂ)).re ∧
        (k : ℂ) * (ρ / (n : ℂ)) ∈ NontrivialZeros} = {n} := by
      ext k
      simp only [mem_ofPred_eq, mem_singleton_iff]
      constructor
      · rintro ⟨hk1, hksq, -, hkz⟩
        have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
        exact (hsing _ k ⟨hkz, hk1, hksq, by field_simp⟩).2
      · rintro rfl
        refine ⟨hn, hsq, ?_, ?_⟩
        · rw [hre, one_div_div, lt_div_iff₀ hρ.2.1]
          nlinarith [hρ.2.2]
        · rwa [mul_div_cancel₀ _ hn0]
    have hR := hRρ _ hu him
    rw [hset, finsum_mem_singleton, mul_div_cancel₀ _ hn0] at hR
    have := (cor_one_add hZ1 hZ2 hZ3 hZ6 hu h2 hp F hF hFT).1 hu1
    rw [hR] at this
    convert this using 1
    field_simp

/-- **`nr:lem:rigidity`**, first part (paper, verbatim; unconditional):

Let $\rho=\frac12+i\gamma$ be a zero with $\gamma>0$, let $q$ be a prime, and $u=\rho/q$. Every
representation $(\rho',k)\neq(\rho,q)$ of $u$ has $\gcd(k,q)=1$, $1\le k<2q$, $k\neq q$, and
$\Re\rho'=k/(2q)\neq\frac12$. Put $\zeta^*=\rho'$ if $k>q$ and $\zeta^*=1-\bar\rho'$ if $k<q$. Then
$\zeta^*$ is a zero with $\Re\zeta^*>\frac12$ and $0<\Im\zeta^*<2\gamma$, and the reduced denominator
$d$ of the rational number $\Re\zeta^*$ lies in $\{q,2q\}$. [...]

Lean: `ζ* = zetaStar ρ' k q`. "The reduced denominator of the rational number `Re ζ*`" is `r.den` for a rational `r`
equal to `Re ζ*` (`ℚ` is normalised, so `r.den` is the reduced denominator; the existence of `r` is part of the
claim). Hypothesis (Z1) (`1 - ρ̄'` is a zero; `Re ρ' < 1`). -/
theorem lem_rigidity (hZ1 : Z1) {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) (hre : ρ.re = 1 / 2)
    (him : 0 < ρ.im) {q : ℕ} (hq : q.Prime) :
    ∀ ρ' : ℂ, ∀ k : ℕ, IsRep (ρ / (q : ℂ)) ρ' k → (ρ', k) ≠ (ρ, q) →
      Nat.Coprime k q ∧ 1 ≤ k ∧ k < 2 * q ∧ k ≠ q ∧ ρ'.re = (k : ℝ) / (2 * q) ∧ ρ'.re ≠ 1 / 2 ∧
      zetaStar ρ' k q ∈ NontrivialZeros ∧ 1 / 2 < (zetaStar ρ' k q).re ∧
      0 < (zetaStar ρ' k q).im ∧ (zetaStar ρ' k q).im < 2 * ρ.im ∧
      ∃ r : ℚ, (r : ℝ) = (zetaStar ρ' k q).re ∧ (r.den = q ∨ r.den = 2 * q) := by
  exact M2.lem_rigidity_proof hZ1 hρ hre him hq

/-- **`nr:lem:rigidity`**, the converse (paper, verbatim):

[...] Conversely, $\zeta^*$ determines $q$
\textup{(}$q=d$ if $d$ is odd, $q=d/2$ if $d$ is even\textup{)}, and then $(\rho,q)$ is one of at
most two pairs.

Lean: for a point `z` whose real part is the rational `r` (reduced denominator `d = r.den`), the set of pairs
`(ρ, q)` as in the first part (`ρ = 1/2 + iγ` a zero, `γ > 0`, `q` prime) having a representation
`(ρ', k) ≠ (ρ, q)` of `ρ/q` with `ζ* = z`: every such pair has `q = d` (`d` odd) or `q = d/2` (`d` even), and there
are at most two (finite, `ncard ≤ 2`). Hypothesis (Z1). -/
theorem lem_rigidity_converse (hZ1 : Z1) (z : ℂ) (r : ℚ) (hr : (r : ℝ) = z.re) :
    (∀ p ∈ {p : ℂ × ℕ | p.1 ∈ NontrivialZeros ∧ p.1.re = 1 / 2 ∧ 0 < p.1.im ∧ p.2.Prime ∧
        ∃ ρ' : ℂ, ∃ k : ℕ, IsRep (p.1 / (p.2 : ℂ)) ρ' k ∧ (ρ', k) ≠ p ∧ zetaStar ρ' k p.2 = z},
      p.2 = if Odd r.den then r.den else r.den / 2) ∧
    {p : ℂ × ℕ | p.1 ∈ NontrivialZeros ∧ p.1.re = 1 / 2 ∧ 0 < p.1.im ∧ p.2.Prime ∧
        ∃ ρ' : ℂ, ∃ k : ℕ, IsRep (p.1 / (p.2 : ℂ)) ρ' k ∧ (ρ', k) ≠ p ∧ zetaStar ρ' k p.2 = z}.Finite ∧
    {p : ℂ × ℕ | p.1 ∈ NontrivialZeros ∧ p.1.re = 1 / 2 ∧ 0 < p.1.im ∧ p.2.Prime ∧
        ∃ ρ' : ℂ, ∃ k : ℕ, IsRep (p.1 / (p.2 : ℂ)) ρ' k ∧ (ρ', k) ≠ p ∧ zetaStar ρ' k p.2 = z}.ncard ≤ 2 := by
  exact M2.lem_rigidity_converse_proof hZ1 z r hr

/-- **`nr:thm:single`** (paper, verbatim; unconditional):

Let $y>0$ and $0<\varepsilon<y$. Put $J=(y-\varepsilon/2,\ y+\varepsilon/2)$ and, for $X\ge3$,
$M=M(X)=\lceil2\log X/A_0\rceil$ with $A_0$ as in \textup{(Z4)}, and
\[
  \mathcal P(X)=\big\{(\rho,q):\ \rho=\tfrac12+i\gamma\text{ a zero},\ X/M<\gamma\le X,\ q\text{ prime},\ \gamma/q\in J\big\}.
\]
Call $(\rho,q)\in\mathcal P(X)$ \emph{good} if $(\rho,q)$ is the only representation of $u=\rho/q$.
There are $c_2=c_2(y,\varepsilon)>0$ and $X_0=X_0(y,\varepsilon)$ such that for $X\ge X_0$:
\begin{itemize}
\item[\textup{(a)}] $|\mathcal P(X)|\ge c_2X^2/\log^2X$, and at most $4X\log(2X)$ pairs in
$\mathcal P(X)$ are not good; so at least $\frac12c_2X^2/\log^2X$ pairs are good;
\item[\textup{(b)}] for every good pair, $u=\rho/q$ satisfies $|u-iy|<\varepsilon$, $\Re u=1/(2q)$,
$R_u=m(\rho)/q\neq0$, and $|2R_u/u|=2m(\rho)/|\rho|\ge2/(X+1)$;
\item[\textup{(c)}] distinct pairs in $\mathcal P(X)$ give distinct points $u$.
\end{itemize}
[...]

Lean: `A₀` and `t₀` are any witnesses of (Z4), passed explicitly (`hN0`), since `M` depends on `A₀`. Counts are
`Set.ncard` together with `Set.Finite`. Hypotheses (Z1) (the proof uses `1 - ρ̄`), (Z2), (Z5). -/
theorem thm_single (hZ1 : Z1) (hZ2 : Z2) (hZ5 : Z5) {A₀ t₀ : ℝ} (hA₀ : 0 < A₀)
    (hN0 : ∀ t ≥ t₀, A₀ * t ≤ (N0 t : ℝ)) {y ε : ℝ} (hy : 0 < y) (hε : 0 < ε) (hεy : ε < y) :
    ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → 3 ≤ X →
      (singlePairs A₀ y ε X).Finite ∧
      c₂ * X ^ 2 / Real.log X ^ 2 ≤ ((singlePairs A₀ y ε X).ncard : ℝ) ∧
      (({p | p ∈ singlePairs A₀ y ε X ∧ ¬ IsSingleRep p.1 p.2}.ncard : ℕ) : ℝ) ≤
        4 * X * Real.log (2 * X) ∧
      c₂ / 2 * X ^ 2 / Real.log X ^ 2 ≤
        (({p | p ∈ singlePairs A₀ y ε X ∧ IsSingleRep p.1 p.2}.ncard : ℕ) : ℝ) ∧
      (∀ p ∈ singlePairs A₀ y ε X, IsSingleRep p.1 p.2 →
        ‖p.1 / (p.2 : ℂ) - y * I‖ < ε ∧ (p.1 / (p.2 : ℂ)).re = 1 / (2 * p.2) ∧
        Rcoef (p.1 / (p.2 : ℂ)) = (zetaMult p.1 : ℂ) / p.2 ∧ Rcoef (p.1 / (p.2 : ℂ)) ≠ 0 ∧
        ‖2 * Rcoef (p.1 / (p.2 : ℂ)) / (p.1 / (p.2 : ℂ))‖ = 2 * zetaMult p.1 / ‖p.1‖ ∧
        2 / (X + 1) ≤ 2 * zetaMult p.1 / ‖p.1‖) ∧
      InjOn (fun p : ℂ × ℕ => p.1 / (p.2 : ℂ)) (singlePairs A₀ y ε X) := by
  exact M2.thm_single_proof hZ1 hZ2 hZ5 hA₀ hN0 hy hε hεy

/-- **`nr:thm:single`**, last sentence (paper, verbatim):

[...] In particular there are infinitely many points $u=\rho/q\in\disc(iy,\varepsilon)$, $\rho$ a zero on
the critical line and $q$ a prime, with the single representation $(\rho,q)$.

Hypotheses (Z1), (Z2), (Z4), (Z5). -/
theorem thm_single_infinite (hZ1 : Z1) (hZ2 : Z2) (hZ4 : Z4) (hZ5 : Z5) {y ε : ℝ} (hy : 0 < y)
    (hε : 0 < ε) (hεy : ε < y) :
    {u : ℂ | ∃ ρ ∈ NontrivialZeros, ρ.re = 1 / 2 ∧ ∃ q : ℕ, q.Prime ∧ IsSingleRep ρ q ∧
      u = ρ / (q : ℂ) ∧ ‖u - y * I‖ < ε}.Infinite := by
  exact M2.thm_single_infinite_proof hZ1 hZ2 hZ4 hZ5 hy hε hεy

/-- **`nr:cor:LW`** (paper, verbatim; the theorem of Landau–Walfisz):

Every point of the line $\Re z=0$ is a limit of poles of $Q$ lying in $\Re z>0$. Hence $Q$ is
meromorphic on $\{\Re z>0\}$ and on no connected open set properly containing it, and no branch of
$P$ extends meromorphically to any disc centred on a point of $\Re z=0$.

Lean: poles of `Q` are points of order `< 0` of a continuation `Qc` (any `IsQCont`). "Meromorphic on `W`" is a
meromorphic `f` on `W` agreeing with the series `Q` off a discrete subset of `Re z > 1`. A branch of `P` is
`IsPBranch` (continuation from `Re z > 1` along paths in `{Re z > 0} ∖ Σ_Q`), at a point `z₁` of the disc.
Hypotheses (Z1), (Z2), (Z4), (Z5): the paper proves the corollary through `nr:thm:single` and says so
("depends on the Hardy–Littlewood theorem (Z4), which the original proof does not need"). -/
theorem cor_LW (hZ1 : Z1) (hZ2 : Z2) (hZ4 : Z4) (hZ5 : Z5) :
    (∀ Qc : ℂ → ℂ, IsQCont Qc → ∀ y : ℝ, ∀ ε : ℝ, 0 < ε →
      {a | a ∈ halfPlane 0 ∧ ‖a - y * I‖ < ε ∧ meromorphicOrderAt Qc a < 0}.Infinite) ∧
    (∀ W : Set ℂ, IsOpen W → IsConnected W → halfPlane 0 ⊂ W →
      ¬ ∃ f : ℂ → ℂ, MeromorphicOn f W ∧ f =ᶠ[codiscreteWithin (halfPlane 1)] Q) ∧
    ∀ (g : ℂ → ℂ) (z₁ : ℂ), IsPBranch g z₁ → ∀ y r : ℝ, 0 < r → z₁ ∈ ball ((y : ℂ) * I) r →
      ¬ GermExtendsMeromorphically g z₁ (ball ((y : ℂ) * I) r) := by
  exact M2.cor_LW_proof hZ1 hZ2 hZ4 hZ5

/-- **`nr:lem:far`** (paper, verbatim; hypothesis `B < 1` in the statement):

Assume $B<1$ and let $Y>0$. Let $s_0=1+v$ with $0<\Re v\le1$ and $|\Im v|\le Y$. Every ordered pair
$(a,b)\in\Sigma_Q^2$ with $a+b=s_0$ other than $(1,v)$ and $(v,1)$ has $a,b\in\Sigma_Q\setminus\{1\}$
and $\Re a,\Re b\in(1-B,B]$. There is $H_0=H_0(B,Y)\ge2Y+2$ such that for every $H\ge H_0$ and
every such $s_0$,
\begin{equation}\label{nr:eq:far}
  \sum_{\substack{(a,b)\in\Sigma_Q^2,\ a+b=s_0\\ (a,b)\neq(1,v),(v,1)\\ |\Im a|>H}}\big|R_aR_b\,\mathrm B(a,b)\big|\le e^{-H}.
\end{equation}
[...]

Lean: `H₀` is chosen after `Y` and before `H` and `v` (uniform in `s₀`). The sum is a `tsum` of norms over the subtype
of such pairs, stated with its `Summable` (a non-summable `tsum` is `0`, which would make the bound vacuous).
`B(a, b) = betaB a b = Γ(a)Γ(b)/Γ(a+b)`, and `a + b = s₀` has real part `> 1`, so `Γ(s₀) ≠ 0`. Hypotheses (Z1), (Z2)
(through `nr:lem:Q`(ii), (iii)) and (Z6) (the proof's). -/
theorem lem_far (hZ1 : Z1) (hZ2 : Z2) (hZ6 : Z6) (hB : Bsup < 1) {Y : ℝ} (hY : 0 < Y) :
    (∀ v : ℂ, 0 < v.re → v.re ≤ 1 → |v.im| ≤ Y → ∀ p ∈ pinchPairs (1 + v), p ≠ (1, v) → p ≠ (v, 1) →
      p.1 ∈ PoleSetQ \ {1} ∧ p.2 ∈ PoleSetQ \ {1} ∧
        p.1.re ∈ Ioc (1 - Bsup) Bsup ∧ p.2.re ∈ Ioc (1 - Bsup) Bsup) ∧
    ∃ H₀ : ℝ, 2 * Y + 2 ≤ H₀ ∧ ∀ H : ℝ, H₀ ≤ H → ∀ v : ℂ, 0 < v.re → v.re ≤ 1 → |v.im| ≤ Y →
      Summable (fun p : {p : ℂ × ℂ // p ∈ pinchPairs (1 + v) ∧ p ≠ (1, v) ∧ p ≠ (v, 1) ∧ H < |p.1.im|} =>
        ‖Rcoef p.1.1 * Rcoef p.1.2 * betaB p.1.1 p.1.2‖) ∧
      ∑' p : {p : ℂ × ℂ // p ∈ pinchPairs (1 + v) ∧ p ≠ (1, v) ∧ p ≠ (v, 1) ∧ H < |p.1.im|},
        ‖Rcoef p.1.1 * Rcoef p.1.2 * betaB p.1.1 p.1.2‖ ≤ Real.exp (-H) := by
  exact M2.lem_far_proof hZ1 hZ2 hZ6 hB hY

/-- **`nr:lem:far`**, last sentence (paper, verbatim):

[...] In particular the full sum $\sum_{a+b=s_0}R_aR_b\mathrm B(a,b)$ converges absolutely.

Lean: for every `s₀ = 1 + v` with `0 < Re v ≤ 1` (every `Y`), `Summable` of the norms over all ordered pairs; this is
the absolute convergence of `𝓡(s₀) = pairSum s₀` (eq. `(nr:eq:Lambda)`). Hypotheses as for `lem_far`. -/
theorem lem_far_abs (hZ1 : Z1) (hZ2 : Z2) (hZ6 : Z6) (hB : Bsup < 1) :
    ∀ v : ℂ, 0 < v.re → v.re ≤ 1 →
      Summable fun p : pinchPairs (1 + v) => ‖Rcoef p.1.1 * Rcoef p.1.2 * betaB p.1.1 p.1.2‖ := by
  exact M2.lem_far_abs_proof hZ1 hZ2 hZ6 hB

/-- **`nr:thm:boundary`** = **Theorem B** (`intro:thm:B`, the same statement) (paper, verbatim):

Assume $(\mathrm H_\infty)$. Then $T$ is a single-valued meromorphic function on $\HH$, and for every
$y\in\R$ and $\varepsilon>0$ the disc $\disc(1+iy,\varepsilon)$ contains infinitely many poles of $T$.
Consequently, for no $y\in\R$ and $r>0$ is there a meromorphic function $f$ on $\disc(1+iy,r)$
with $f=T$ on $\disc(1+iy,r)\cap\HH$: the line $\sigma=1$ is a natural boundary of $T$.

Lean: as paper 1's `thm_T_boundary`, for every `F` meromorphic on `ℍ` agreeing with the series off a discrete
subset of `σ > 2` (non-vacuous by the first conjunct). Poles are points of `ℍ` of order `< 0`. "The same statement"
means the same content: `intro:thm:B`'s text differs from this one only in defining the disc inline,
"`\disc(1+iy,\varepsilon)=\{s:|s-1-iy|<\varepsilon\}`", which is `ball (1 + y * I) ε`.
Hypotheses `(H_∞)` (the paper's), and (Z1), (Z2), (Z3), (Z4), (Z5), (Z6) (through `nr:thm:cont`,
`nr:thm:residue`, `nr:thm:single`, `nr:lem:far`). -/
theorem thm_boundary (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ4 : Z4) (hZ5 : Z5) (hZ6 : Z6) :
    (∃ F : ℂ → ℂ, MeromorphicOn F HH ∧ EqOn F T (halfPlane 2)) ∧
    ∀ F : ℂ → ℂ, MeromorphicOn F HH → F =ᶠ[codiscreteWithin (halfPlane 2)] T →
      (∀ y ε : ℝ, 0 < ε →
        {s | s ∈ ball (1 + (y : ℂ) * I) ε ∧ s ∈ HH ∧ meromorphicOrderAt F s < 0}.Infinite) ∧
      IsNaturalBoundary F HH lineOne := by
  exact M2.thm_boundary_proof hH hZ1 hZ2 hZ3 hZ4 hZ5 hZ6

/-- **`nr:lem:A`** (paper, verbatim):

Suppose $\frac12<B<1$ and that some zero has $\beta=B$. Put
\[
  A=\frac1{\Gamma(2B)}\sum_{\rho:\ \beta=B}m(\rho)^2\,|\Gamma(\rho)|^2,
\]
the sum over the distinct zeros with $\beta=B$, in both half-planes. Then
\[
  0<A\le16\pi e\,C_0^2=0.0728\ldots<2,
\]
with $C_0$ as in \textup{(Z7)}.

Lean: "`= 0.0728…`" is read as `0.0728 < 16πeC₀² < 0.0729` (the value is `0.07288…`); this, with `A ≤ 16πeC₀²`,
gives `A < 0.073`, which `nr:thm:real`(b) uses. Hypothesis (Z7). -/
theorem lem_A (hZ7 : Z7) (h1 : 1 / 2 < Bsup) (h2 : Bsup < 1)
    (h3 : ∃ ρ ∈ NontrivialZeros, ρ.re = Bsup) :
    0 < Aconst ∧ Aconst ≤ 16 * Real.pi * Real.exp 1 * C0 ^ 2 ∧
      0.0728 < 16 * Real.pi * Real.exp 1 * C0 ^ 2 ∧ 16 * Real.pi * Real.exp 1 * C0 ^ 2 < 0.0729 := by
  exact M3.lem_A_proof hZ7 h1 h2 h3

/-- **`nr:thm:real` (a)** = **Theorem C (a)** (paper, verbatim):

\textup{(a)} Assume RH. Then $T$ is meromorphic on $\HH$, and its poles on the real interval $(1,2)$
are exactly the points $1+1/k$, $k\ge2$ squarefree, with residue $2\mu(k)$.

Hypotheses RH (the paper's), (Z1), (Z2), (Z3), (Z6) (through `nr:thm:cont`). -/
theorem thm_real_a (hRH : RiemannHypothesis) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6) :
    (∃ F : ℂ → ℂ, MeromorphicOn F HH ∧ EqOn F T (halfPlane 2)) ∧
    ∀ F : ℂ → ℂ, MeromorphicOn F HH → F =ᶠ[codiscreteWithin (halfPlane 2)] T →
      (∀ x : ℝ, x ∈ Ioo (1 : ℝ) 2 →
        (meromorphicOrderAt F x < 0 ↔ ∃ k : ℕ, 2 ≤ k ∧ Squarefree k ∧ (x : ℂ) = 1 + 1 / (k : ℂ))) ∧
      ∀ k : ℕ, 2 ≤ k → Squarefree k → HasResidue F (1 + 1 / (k : ℂ)) (2 * mu k) := by
  exact M3.thm_real_a_proof hRH hZ1 hZ2 hZ3 hZ6

/-- **`nr:thm:real` (b)** = **Theorem C (b)** (paper, verbatim):

\textup{(b)} Suppose $B>B_\infty$ \textup{(}for instance, $\zeta$ has at least one, but only
finitely many, zeros off the critical line\textup{)}. Then $\frac12<B<1$, $B$ is attained by finitely
many zeros, $T$ is meromorphic on $\{\sigma>2B_\infty\}\ni2B$, and
\[
  \Res_{s=2B}T=A+\begin{cases}2\mu(k)&\text{if }2B=1+1/k\text{ for an integer }k\ge2,\\ 0&\text{otherwise,}\end{cases}
\]
with $A$ as in Lemma~\ref{nr:lem:A}, $0<A<0.073$. So the residue lies in $(0,0.073)$, in
$(2,2.073)$ or in $(-2,-1.927)$; it is never $0$, and it differs from the value $2\mu(k)$, resp.\ $0$,
that \textup{(a)} assigns to the point $2B$ under RH.

Lean: the two cases of the residue formula are two conjuncts. The last sentence is arithmetic from
`0 < A < 0.073` and `μ(k) ∈ {-1, 0, 1}`; it is `thm_real_b_values` (real proof). Hypotheses (Z1), (Z2), (Z3), (Z6)
(through `nr:thm:cont`, `nr:thm:residue`) and (Z7) (through `nr:lem:A`). -/
theorem thm_real_b (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6) (hZ7 : Z7) (h : Binf < Bsup) :
    1 / 2 < Bsup ∧ Bsup < 1 ∧ {ρ | ρ ∈ NontrivialZeros ∧ ρ.re = Bsup}.Finite ∧
    {ρ | ρ ∈ NontrivialZeros ∧ ρ.re = Bsup}.Nonempty ∧
    (∃ F : ℂ → ℂ, MeromorphicOn F (halfPlane (2 * Binf)) ∧ EqOn F T (halfPlane 2)) ∧
    2 * Binf < 2 * Bsup ∧ 0 < Aconst ∧ Aconst < 0.073 ∧
    ∀ F : ℂ → ℂ, MeromorphicOn F (halfPlane (2 * Binf)) → F =ᶠ[codiscreteWithin (halfPlane 2)] T →
      (∀ k : ℕ, 2 ≤ k → 2 * Bsup = 1 + 1 / (k : ℝ) →
        HasResidue F ((2 * Bsup : ℝ) : ℂ) (Aconst + 2 * mu k)) ∧
      ((∀ k : ℕ, 2 ≤ k → 2 * Bsup ≠ 1 + 1 / (k : ℝ)) → HasResidue F ((2 * Bsup : ℝ) : ℂ) Aconst) := by
  exact M3.thm_real_b_proof hZ1 hZ2 hZ3 hZ6 hZ7 h

/-- The last sentence of `nr:thm:real`(b), from `0 < A < 0.073` (real proof): the residue `A + 2μ(k)`, resp.
`A`, lies in `(0, 0.073) ∪ (2, 2.073) ∪ (-2, -1.927)`, is not `0`, and differs from the RH value `2μ(k)`,
resp. `0`. -/
theorem thm_real_b_values {A : ℝ} (hA0 : 0 < A) (hA1 : A < 0.073) (k : ℕ) :
    let r : ℝ := A + 2 * (ArithmeticFunction.moebius k : ℝ)
    (r ∈ Ioo (0 : ℝ) 0.073 ∨ r ∈ Ioo (2 : ℝ) 2.073 ∨ r ∈ Ioo (-2 : ℝ) (-1.927)) ∧ r ≠ 0 ∧
      r ≠ 2 * (ArithmeticFunction.moebius k : ℝ) := by
  intro r
  have hμ : |(ArithmeticFunction.moebius k : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have hcases : (ArithmeticFunction.moebius k : ℤ) = -1 ∨ (ArithmeticFunction.moebius k : ℤ) = 0 ∨
      (ArithmeticFunction.moebius k : ℤ) = 1 := by
    have := ArithmeticFunction.abs_moebius_le_one (n := k)
    rw [abs_le] at this
    omega
  rcases hcases with h | h | h <;>
  · simp only [r, h, Int.cast_neg, Int.cast_one, Int.cast_zero, mem_Ioo]
    refine ⟨by norm_num; first | (right; right; constructor <;> linarith) |
      (left; constructor <;> linarith) | (right; left; constructor <;> linarith), ?_, ?_⟩ <;>
    linarith

/-- **`nr:lem:hsq`** (paper, verbatim; unconditional):

\textup{(i)} $E$ and $e$ are entire, and for $\sigma>2$ the integral $\mathcal M(s)$ converges absolutely and
\begin{equation}\label{nr:eq:hsq}
  \mathcal M(s)=\Gamma(s)T(s)-2\Gamma(s-1)Q(s-1)+\frac1{s-2}-E(s)+2e(s-1).
\end{equation}

\textup{(ii)} $t\,\Theta(t)\to1$ as $t\to0^+$, and $(s-2)\Gamma(s)T(s)\to1$ as $s\downarrow2$ through real values.
Consequently, if $f$ is meromorphic on a disc $\disc(2,r)$ and $f=T$ on $\disc(2,r)\cap\{\sigma>2\}$, then $f$
has a simple pole at $2$ with residue $1$.

Lean: no (Z) hypothesis. The proof of (ii) uses the prime number theorem `θ(x) ~ x`, which PNT+ proves sorry-free
(`chebyshev_asymptotic`, `PrimeNumberTheoremAnd/Consequences.lean`); it is not one of (Z1)–(Z7). "`f = T`" is
read off a discrete set (the weaker hypothesis). "`E` and `e` are entire" is `Differentiable` together with the
absolute convergence of the defining integrals for every `s`, resp. `z` (`IntegrableOn` on `(1, ∞)`), so that `Ecal`
and `ecal` are not junk Bochner integrals. -/
theorem lem_hsq :
    (Differentiable ℂ Ecal ∧ Differentiable ℂ ecal ∧
      (∀ s : ℂ, IntegrableOn (fun t : ℝ => ((Theta t ^ 2 : ℝ) : ℂ) * (t : ℂ) ^ (s - 1)) (Ioi (1 : ℝ))) ∧
      (∀ z : ℂ, IntegrableOn (fun t : ℝ => (Theta t : ℂ) * (t : ℂ) ^ (z - 1)) (Ioi (1 : ℝ))) ∧
      ∀ s : ℂ, 2 < s.re →
        IntegrableOn (fun t : ℝ => ((hErr t ^ 2 : ℝ) : ℂ) * (t : ℂ) ^ (s - 1)) (Ioc (0 : ℝ) 1) ∧
        Mcal s = Gamma s * T s - 2 * Gamma (s - 1) * Q (s - 1) + 1 / (s - 2) - Ecal s +
          2 * ecal (s - 1)) ∧
    (Tendsto (fun t : ℝ => t * Theta t) (𝓝[>] 0) (𝓝 1) ∧
      Tendsto (fun x : ℝ => ((x : ℂ) - 2) * Gamma x * T x) (𝓝[>] 2) (𝓝 1) ∧
      ∀ (f : ℂ → ℂ) (r : ℝ), 0 < r → MeromorphicOn f (ball 2 r) →
        f =ᶠ[codiscreteWithin (ball 2 r ∩ halfPlane 2)] T →
        meromorphicOrderAt f 2 = -1 ∧ HasResidue f 2 1) := by
  exact M3.lem_hsq_proof 

/-- **`nr:lem:Landau`** (paper, verbatim; classical, proof included in the paper):

Let $\varphi\ge0$ be measurable on $(0,\infty)$ and suppose that $\int_0^\infty\varphi(u)e^{-xu}du<\infty$ for some
real $x$; let $\sigma_c\in[-\infty,\infty)$ be the infimum of such $x$. Then
$\mathcal L(s)=\int_0^\infty\varphi(u)e^{-su}du$ converges absolutely and is holomorphic on $\{\Re s>\sigma_c\}$,
and if $\sigma_c>-\infty$ there is no $r>0$ and no function holomorphic on $\disc(\sigma_c,r)$ that agrees with
$\mathcal L$ on $\disc(\sigma_c,r)\cap\{\Re s>\sigma_c\}$.

Lean: `S = laplaceConvSet φ` is the set of such `x`; `{Re s > σ_c}` is `{s | ∃ x ∈ S, x < Re s}` (no extended
reals needed); `σ_c > -∞` is `BddBelow S`, and then `σ_c = sInf S`. "Measurable on `(0,∞)`" is measurability
of the restriction of `φ` to `(0,∞)`, as the paper says; nothing is asked of `φ` elsewhere. -/
theorem lem_Landau (φ : ℝ → ℝ) (hφm : Measurable ((Ioi (0 : ℝ)).domRestrict φ)) (hφ0 : ∀ u, 0 < u → 0 ≤ φ u)
    (hS : (laplaceConvSet φ).Nonempty) :
    (∀ s : ℂ, (∃ x ∈ laplaceConvSet φ, x < s.re) →
      IntegrableOn (fun u : ℝ => (φ u : ℂ) * exp (-(s * u))) (Ioi (0 : ℝ))) ∧
    DifferentiableOn ℂ (laplace φ) {s | ∃ x ∈ laplaceConvSet φ, x < s.re} ∧
    (BddBelow (laplaceConvSet φ) → ∀ r : ℝ, 0 < r →
      ¬ ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball ((sInf (laplaceConvSet φ) : ℝ) : ℂ) r) ∧
        EqOn g (laplace φ) (ball ((sInf (laplaceConvSet φ) : ℝ) : ℂ) r ∩
          {s | sInf (laplaceConvSet φ) < s.re})) := by
  exact M3.lem_Landau_proof φ hφm hφ0 hS

/-- **`nr:thm:test`** = **Theorem C (c)** (paper, verbatim):

The Riemann Hypothesis holds if and only if there are an open set $U\supset(1,2]$ and a function $\tilde T$
meromorphic on $U$ with $\tilde T=T$ on $U\cap\{\sigma>2\}$, whose poles on the real interval $(1,2)$ are exactly
the points $1+1/k$, $k\ge2$ squarefree, each simple with residue $2\mu(k)$.

Lean: `U ⊇ (1,2]` as a set of real points of `ℂ`; "`T̃ = T` on `U ∩ {σ > 2}`" pointwise (the literal reading;
`T` is the convergent series there). The paper says "no hypothesis on the zeros"; the classical inputs its proof
uses are premises: (Z1) (through `nr:lem:Q`) for sufficiency, and (Z1), (Z2), (Z3), (Z6) (through `nr:thm:cont`,
`nr:thm:real`(a)) for necessity. RH is Mathlib's `RiemannHypothesis`, which speaks of every zero of `ζ` other than
the trivial zeros and `1`, while the paper's RH speaks of the non-trivial zeros `0 < β < 1`. The two agree because
every zero that is not trivial lies in the strip (functional equation and Euler product); the sufficiency half has to
supply that argument. This is proof work, not a change of statement. -/
theorem thm_test (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6) :
    RiemannHypothesis ↔
      ∃ U : Set ℂ, IsOpen U ∧ (∀ x : ℝ, x ∈ Ioc (1 : ℝ) 2 → (x : ℂ) ∈ U) ∧
        ∃ Tt : ℂ → ℂ, MeromorphicOn Tt U ∧ EqOn Tt T (U ∩ halfPlane 2) ∧
          (∀ x : ℝ, x ∈ Ioo (1 : ℝ) 2 →
            (meromorphicOrderAt Tt x < 0 ↔ ∃ k : ℕ, 2 ≤ k ∧ Squarefree k ∧ (x : ℂ) = 1 + 1 / (k : ℂ))) ∧
          ∀ k : ℕ, 2 ≤ k → Squarefree k →
            meromorphicOrderAt Tt (1 + 1 / (k : ℂ)) = -1 ∧ HasResidue Tt (1 + 1 / (k : ℂ)) (2 * mu k) := by
  exact M3.thm_test_proof hZ1 hZ2 hZ3 hZ6

/-- **`nr:cor:test`** (paper, verbatim):

Assume $(\mathrm H_\infty)$. Then RH holds if and only if the poles of $T$ on the real interval
$(1,2)$, with their residues, are exactly the pairs $(1+1/k,\ 2\mu(k))$, $k\ge2$ squarefree.

Lean: for every `F` meromorphic on `ℍ` agreeing with the series off a discrete subset of `σ > 2` (such `F` exist
under `(H_∞)`, `thm_boundary`). Hypotheses `(H_∞)`, and (Z1), (Z2), (Z3), (Z6) (through `nr:thm:test`). As in
`thm_test`, the `←` direction concludes Mathlib's `RiemannHypothesis` and so needs the argument that every zero
that is not trivial lies in `0 < β < 1`. -/
theorem cor_test (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6)
    (F : ℂ → ℂ) (hF : MeromorphicOn F HH) (hFT : F =ᶠ[codiscreteWithin (halfPlane 2)] T) :
    RiemannHypothesis ↔
      (∀ x : ℝ, x ∈ Ioo (1 : ℝ) 2 →
        (meromorphicOrderAt F x < 0 ↔ ∃ k : ℕ, 2 ≤ k ∧ Squarefree k ∧ (x : ℂ) = 1 + 1 / (k : ℂ))) ∧
      ∀ k : ℕ, 2 ≤ k → Squarefree k →
        meromorphicOrderAt F (1 + 1 / (k : ℂ)) = -1 ∧ HasResidue F (1 + 1 / (k : ℂ)) (2 * mu k) := by
  exact M3.cor_test_proof hH hZ1 hZ2 hZ3 hZ6 F hF hFT

/-- **`nr:rem:classical` (ii)** (a Remark in the paper; verbatim):

(ii) The argument gives slightly more: Steps 3 and 4 with $\sigma_c$ in place of $1$, applied to a zero with
$\beta>\sigma_c/2$ and $\beta\ge\frac12$ (such a zero exists if $\sigma_c<2B$: any zero if $B=\frac12$, a zero with
$\beta>\max(\sigma_c/2,\frac12)$ if $B>\frac12$; Step 3 then gives the holomorphy of $Q$ on $\{\Re z>\max(\sigma_c/2,0)\}\setminus\{1\}$),
show that the abscissa of convergence of $\mathcal M$ satisfies $\sigma_c\ge2B$ unconditionally.

Lean: the convergence set `mellinConvSet` of `𝓜` (real `x` with `h(t)² t^{x-1}` integrable on `(0,1]`) and
`σ_c = sigmaC = sInf mellinConvSet`. The set contains every `x > 2` (`nr:lem:hsq`(i)), so it is non-empty; every
point of it is `≥ 2B`, which is the claim in junk-free form and makes the set bounded below; so `sInf` is genuine and
`σ_c ≥ 2B`. All four are asserted. "Unconditionally" means without a hypothesis on the zeros; the classical input
(Z1) is used (through Step 4 and `nr:lem:Q`(i)). -/
theorem rem_classical_ii (hZ1 : Z1) :
    (∀ x : ℝ, 2 < x → x ∈ mellinConvSet) ∧ (∀ x ∈ mellinConvSet, 2 * Bsup ≤ x) ∧
      BddBelow mellinConvSet ∧ 2 * Bsup ≤ sigmaC := by
  exact M3.rem_classical_ii_proof hZ1

/-- **`nr:rem:classical` (iii)** (a Remark in the paper; verbatim):

(iii) Theorem~\ref{nr:thm:real}(b) fits the mechanism. If $B>B_\infty$, then at $s=2B$ the residue of
$\Gamma(s)T(s)$ is $\Gamma(2B)\big(A+[2B=1+1/k]\,2\mu(k)\big)$, and the term $2\Gamma(s-1)Q(s-1)$ removes the bracket,
as in Step 1; so the right side of \eqref{nr:eq:hsq} is holomorphic near every real point $x>2B$ (the real poles of
$T$ above $2B$ are among the $1+1/k$, cancelled as in Step 1) and has at $2B$ a simple pole with residue
$\Gamma(2B)A=\sum_{\beta=B}m(\rho)^2|\Gamma(\rho)|^2>0$. It equals $\mathcal M$ for $\sigma>2$, so by Lemma~\ref{nr:lem:Landau}
the abscissa $\sigma_c$ cannot lie in $(2B,\infty)$; with (ii), $\sigma_c=2B$. So $2B$ is the first real singularity of
$\mathcal M$, and its residue is positive, as it must be: $\mathcal M(\sigma)>0$ for real $\sigma>\sigma_c$, so a simple pole
at $\sigma_c$ has positive residue.

Lean: under `B > B_∞`: `σ_c = 2B`, both in junk-free form (every `x > 2B` is in `mellinConvSet` and every point of
it is `≥ 2B`) and as `sigmaC = 2B`; `𝓜` continues to a meromorphic function on `σ > 2B_∞` (the right side of
`(nr:eq:hsq)`, with `T` continued); every such continuation (agreeing with `𝓜` off a discrete subset of `σ > 2`) has
a simple pole at `2B` with residue `Γ(2B)A`, and `Γ(2B)A > 0`. The intermediate claims about the right side of
`(nr:eq:hsq)` near real `x > 2B` are steps of the argument and are not restated. Hypotheses (Z1), (Z2), (Z3), (Z6),
(Z7) (through `nr:thm:real`(b), whose Lean statement carries them; (Z7) enters only through the bound `A < 0.073`,
which this remark does not need, choice 2). -/
theorem rem_classical_iii (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6) (hZ7 : Z7) (h : Binf < Bsup) :
    (∀ x : ℝ, 2 * Bsup < x → x ∈ mellinConvSet) ∧ (∀ x ∈ mellinConvSet, 2 * Bsup ≤ x) ∧
    sigmaC = 2 * Bsup ∧
    (∃ Mc : ℂ → ℂ, MeromorphicOn Mc (halfPlane (2 * Binf)) ∧ EqOn Mc Mcal (halfPlane 2)) ∧
    0 < Real.Gamma (2 * Bsup) * Aconst ∧
    ∀ Mc : ℂ → ℂ, MeromorphicOn Mc (halfPlane (2 * Binf)) →
      Mc =ᶠ[codiscreteWithin (halfPlane 2)] Mcal →
      meromorphicOrderAt Mc ((2 * Bsup : ℝ) : ℂ) = -1 ∧
        HasResidue Mc ((2 * Bsup : ℝ) : ℂ) ((Real.Gamma (2 * Bsup) * Aconst : ℝ) : ℂ) := by
  exact M3.rem_classical_iii_proof hZ1 hZ2 hZ3 hZ6 hZ7 h

/-- **`nr:prop:dichotomy` (i)** (a Remark in the paper; verbatim):

\textup{(i)} Suppose there were a proof that, whenever $T$ is meromorphic on $\HH$ with $\sigma=1$ as
a natural boundary in the sense of Theorem~\ref{nr:thm:boundary}, RH holds. Combined with
Theorem~\ref{nr:thm:boundary}, it would prove that $(\mathrm H_\infty)$ implies RH.

Lean: an ordinary implication. `TBoundaryOnHH` is the property "`T` is meromorphic on `ℍ` with `σ = 1` as a natural
boundary in the sense of `nr:thm:boundary`"; the "supposed proof" is the premise `TBoundaryOnHH → RH`. The classical
inputs that `nr:thm:boundary` uses to get `TBoundaryOnHH` from `(H_∞)` are premises: (Z1)–(Z6). Proved from
`thm_boundary` (as the paper's proof says). -/
theorem rem_dichotomy_i (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ4 : Z4) (hZ5 : Z5) (hZ6 : Z6) :
    (TBoundaryOnHH → RiemannHypothesis) → Hinf → RiemannHypothesis := fun h hH =>
  h ⟨(thm_boundary hH hZ1 hZ2 hZ3 hZ4 hZ5 hZ6).1,
    fun F hF hFT => ((thm_boundary hH hZ1 hZ2 hZ3 hZ4 hZ5 hZ6).2 F hF hFT).2⟩

/-- **`nr:prop:dichotomy` (ii)** (a Remark in the paper; verbatim):

\textup{(ii)} If $(\mathrm H_\infty)$ holds and RH fails, then $T$ is meromorphic on $\HH$, a half-plane
that contains the line $\sigma=2B$; so the domain of meromorphy of $T$ is not bounded by the line
$\sigma=2B$, although $T$ has a pole at the real point $2B$ by Theorem~\ref{nr:thm:real}(b).

Lean: "contains the line `σ = 2B`" is `1 < 2B`. Part (i) is `rem_dichotomy_i`. Hypotheses (Z1), (Z2), (Z3), (Z6), (Z7) (through `nr:thm:cont`,
`nr:thm:real`(b)). The premise "RH fails" is `¬ RiemannHypothesis`, the negation of Mathlib's RH, which speaks of
every zero of `ζ` other than the trivial zeros and `1`; the proof needs a zero in the strip `0 < β < 1` off the
critical line, so it has to supply the argument that every zero that is not trivial lies in the strip, as noted for
`thm_test` and `cor_test`. This is proof work, not a change of statement. -/
theorem rem_dichotomy_ii (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6) (hZ7 : Z7) (hH : Hinf)
    (hRH : ¬ RiemannHypothesis) :
    (∃ F : ℂ → ℂ, MeromorphicOn F HH ∧ EqOn F T (halfPlane 2)) ∧ 1 < 2 * Bsup ∧
      ∀ F : ℂ → ℂ, MeromorphicOn F HH → F =ᶠ[codiscreteWithin (halfPlane 2)] T →
        meromorphicOrderAt F ((2 * Bsup : ℝ) : ℂ) < 0 := by
  exact M3.rem_dichotomy_ii_proof hZ1 hZ2 hZ3 hZ6 hZ7 hH hRH

/-- **`nr:prop:Lambda`** (paper, verbatim):

Assume $B<1$. For every $y\in\R$ and $\varepsilon>0$ there are infinitely many points
$s_0=1+\rho/q\in\disc(1+iy,\varepsilon)$, with $\rho$ a zero on the critical line and $q$ a prime, at
which $\mathcal R(s_0)\neq0$.

Lean: `𝓡(s₀) = pairSum s₀`, a `tsum` over the ordered pairs; `≠ 0` forces its (absolute) summability, which the
paper gets from `nr:lem:far` (here `lem_far_abs`, for every `s₀ = 1 + v` with `0 < Re v ≤ 1`). Hypotheses `B < 1` (the paper's), and (Z1), (Z2), (Z4), (Z5) (through
`nr:thm:single`), (Z6) (through `nr:lem:far`). -/
theorem prop_Lambda (hZ1 : Z1) (hZ2 : Z2) (hZ4 : Z4) (hZ5 : Z5) (hZ6 : Z6) (hB : Bsup < 1)
    (y ε : ℝ) (hε : 0 < ε) :
    {s₀ : ℂ | ∃ ρ ∈ NontrivialZeros, ρ.re = 1 / 2 ∧ ∃ q : ℕ, q.Prime ∧ s₀ = 1 + ρ / (q : ℂ) ∧
      s₀ ∈ ball (1 + (y : ℂ) * I) ε ∧ pairSum s₀ ≠ 0}.Infinite := by
  exact M2.prop_Lambda_proof hZ1 hZ2 hZ4 hZ5 hZ6 hB y ε hε

/-! ## 4. A class of double prime series (RH assumed throughout the section)

The class data are an affine map `A : Aff` (`L(s) = ℓ s + ℓ₀`), a kernel `k` (`k z s` is the paper's `k(z, s)`),
and a weight `W` (`W s p q` is `W_s(p,q)`), whose series `Dser W` is `D` (resp. `D^log`) on `R_L`. -/

/-- **(H2-log)**, the first sufficient condition (paper, verbatim; item (H2-log) of the hypotheses in Section 4.1, no label):

[...] Two
sufficient conditions: (H2a) $k$ is holomorphic on $\{(z,s):s\in\HH_L,\ z\in\mathrm{Str}(s)\}$ (then $J_{ab}$
itself is defined and single-valued holomorphic on $\HH_L$, Lemma~\ref{cl:lem:J}); or [...]

Lean: (H2a) implies (H2-log). (H2a) contains (K1), since `D_L ⊆ ℍ_L`; the holomorphy of `J_{ab}` on `ℍ_L` is the
(H2a) clause of `lem_J_i`. No RH: the implication is the first part of `cl:lem:J`, which `cl:rem:RH` says does not use
RH (choice 23). -/
theorem H2log_of_H2a (A : Aff) (k : ℂ → ℂ → ℂ) (hH2a : H2a A k) : H2log A k := by
  exact M4a.H2log_of_H2a_proof A k hH2a

/-- **(H2-log)**, the second sufficient condition (paper, verbatim; item (H2-log) of the hypotheses in Section 4.1, no label):

[...] or (H2b)
$k(z,s)=g(z-\theta s)$ with $g$ meromorphic on $\C$ and $\theta\in\R$ (then
$J'_{ab}(s)=(\ell-\theta)g(L(s)-b-\theta s)+\theta g(a-\theta s)$ on $D_L$, and the right side is meromorphic on $\C$).

Lean: under (K1) (which gives `J_{ab}` and its derivative on `D_L`) and (H2b) with explicit `g` and `θ`: the derivative
formula at every `s ∈ D_L` (both points `L(s) - b - θs` and `a - θs` are where `g` is holomorphic, since the ends of
the segment lie in `Str(s)`, so the formula has no junk value), the right side meromorphic on `ℂ` as a function of
`s`, and (H2-log). No RH (choice 23). -/
theorem H2log_of_H2b (A : Aff) (k : ℂ → ℂ → ℂ) (hK1 : K1 A k) {g : ℂ → ℂ} {θ : ℝ}
    (hg : MeromorphicOn g univ) (hk : ∀ z s, k z s = g (z - θ * s)) :
    (∀ a ∈ PoleSetQ, ∀ b ∈ PoleSetQ, ∀ s ∈ A.DL,
      HasDerivAt (Jseg A k a b) (((A.ell : ℂ) - θ) * g (A.app s - b - θ * s) + θ * g (a - θ * s)) s) ∧
    (∀ a b : ℂ, MeromorphicOn (fun s => ((A.ell : ℂ) - θ) * g (A.app s - b - θ * s) + θ * g (a - θ * s)) univ) ∧
    H2log A k := by
  exact M4a.H2log_of_H2b_proof A k hK1 hg hk

/-- **`cl:prop:catalogue` (i)** (paper, verbatim):

Assume RH.
\begin{enumerate}
\item[(i)] $\cat_L=\{s\in\HH_L:\ L(s)\in\{2\}\cup\{1+1/j:\ j\ge2\text{ squarefree}\}\cup\{1+\rho/n:\ n\ge1\text{ squarefree}\}\}$.
At a pinch with $L(\alpha)=1+b$, $b\in\Sigma$, the ordered pairs $(a',b')\in\Sigma^2$ with $a'+b'=L(\alpha)$ are
$(1,b)$ and $(b,1)$, one pair when $b=1$. Distinct $b$ give distinct pinches, and $\cat_L$ is locally
finite in $\HH_L$.
[...]
\end{enumerate}

Lean: the set in braces is paper 1's `catalogue`. "Distinct `b` give distinct pinches" is stated as
`L(α) - 1 = L(α') - 1 → α = α'` for pinches `α, α'`: the `b` of a pinch is `L(α) - 1`, so the sentence amounts to the
injectivity of `L` on the catalogue (true for every affine `L` with `ℓ > 0`; harmless, and kept for fidelity). -/
theorem prop_catalogue_i (hRH : RiemannHypothesis) (A : Aff) :
    catalogueL A = {s | s ∈ A.HL ∧ A.app s ∈ catalogue} ∧
    (∀ α ∈ catalogueL A, ∀ b ∈ PoleSetQ, A.app α = 1 + b → pinchPairs (A.app α) = {(1, b), (b, 1)}) ∧
    (∀ α ∈ catalogueL A, ∀ α' ∈ catalogueL A, A.app α - 1 = A.app α' - 1 → α = α') ∧
    ∀ z ∈ A.HL, ∃ U ∈ 𝓝 z, (U ∩ catalogueL A).Finite := by
  exact M4a.prop_catalogue_i_proof hRH A

/-- **`cl:prop:catalogue` (ii)** (paper, verbatim):

Assume RH. [...]
\item[(ii)] For every $s_0$ with $\Re L(s_0)=1$ and every $r>0$ there are infinitely many scaled-zero
pinches $\alpha_{\rho,n}$, with $n$ prime, in $\disc(s_0,r)$. If $\Im s_0\ge0$ they can be taken with $\gamma>0$.

Lean: no (Z2) premise, although the paper's proof uses (Z2): the density statement it needs is paper 1's
`lem_density`, already proved without (Z2) (review notes, choice 9). -/
theorem prop_catalogue_ii (hRH : RiemannHypothesis) (A : Aff) :
    ∀ s₀ ∈ A.lineL, ∀ r : ℝ, 0 < r →
      {α | ∃ ρ ∈ NontrivialZeros, ∃ n : ℕ, n.Prime ∧ A.app α = 1 + ρ / (n : ℂ) ∧ α ∈ ball s₀ r}.Infinite ∧
      (0 ≤ s₀.im → {α | ∃ ρ ∈ NontrivialZeros, 0 < ρ.im ∧ ∃ n : ℕ, n.Prime ∧
        A.app α = 1 + ρ / (n : ℂ) ∧ α ∈ ball s₀ r}.Infinite) := by
  exact M4a.prop_catalogue_ii_proof hRH A

/-- **`cl:lem:J`**, first part (paper, verbatim; under (K1) alone, no RH):

Assume \textup{(K1)}. Let $a,b\in\Sigma$ and $s\in D_L$. Then the segment $[a,L(s)-b]$ lies in
$\mathrm{Str}(s)$, $J_{ab}(s)=(L(s)-a-b)\int_0^1k\big(a+t(L(s)-a-b),s\big)\,dt$, and $J_{ab}$ is holomorphic on
$D_L$; under \textup{(H2a)} the same holds on $\HH_L$. If $\alpha\in D_L$ and $L(\alpha)=a+b$ then $J_{ab}(\alpha)=0$ and
$J'_{ab}(\alpha)=\ell\,k(a,\alpha)$. [...]

Lean: `Σ = Σ_Q` (its points have real parts in `(0,1]` without RH). The parametrised formula is the definition
of `Jseg` (Mathlib has no segment integral), so that clause is not restated. -/
theorem lem_J_i (A : Aff) (k : ℂ → ℂ → ℂ) (hK1 : K1 A k) {a b : ℂ} (ha : a ∈ PoleSetQ)
    (hb : b ∈ PoleSetQ) :
    (∀ s ∈ A.DL, segment ℝ a (A.app s - b) ⊆ A.Str s) ∧
    DifferentiableOn ℂ (Jseg A k a b) A.DL ∧
    (H2a A k → (∀ s ∈ A.HL, segment ℝ a (A.app s - b) ⊆ A.Str s) ∧
      DifferentiableOn ℂ (Jseg A k a b) A.HL) ∧
    ∀ α ∈ A.DL, A.app α = a + b → Jseg A k a b α = 0 ∧ HasDerivAt (Jseg A k a b) (A.ell * k a α) α := by
  exact M4a.lem_J_i_proof A k hK1 ha hb

/-- **`cl:lem:J`**, second part (paper, verbatim):

[...] Assume RH, let $\alpha\in\cat_L$ with $L(\alpha)=1+b$, and put
\[
  X_\alpha=c_1c_b\,(J_{1b}+J_{b1})\ \ (b\ne1),\qquad X_\alpha=c_1^2J_{11}=J_{11}\ \ (b=1).
\]
Then $X_\alpha$ is holomorphic on $D_L$, $X_\alpha(\alpha)=0$, and
\[
  X'_\alpha(\alpha)=\ell\,c_1c_b\,\mathfrak b(\alpha)\ \ (b\ne1),\qquad X'_\alpha(\alpha)=\ell\,k(1,\alpha)=\tfrac12\ell\,\mathfrak b(\alpha)\ \ (b=1).
\]

Lean: `X_α = Xcoef A k α`, with `b = L(α) - 1`. Under RH every `α ∈ 𝒞_L` lies in `D_L`. -/
theorem lem_J_ii (hRH : RiemannHypothesis) (A : Aff) (k : ℂ → ℂ → ℂ) (hK1 : K1 A k) {α : ℂ}
    (hα : α ∈ catalogueL A) :
    α ∈ A.DL ∧ DifferentiableOn ℂ (Xcoef A k α) A.DL ∧ Xcoef A k α α = 0 ∧
    (A.app α - 1 ≠ 1 →
      HasDerivAt (Xcoef A k α) (A.ell * cP 1 * cP (A.app α - 1) * bracket A k α) α) ∧
    (A.app α - 1 = 1 →
      HasDerivAt (Xcoef A k α) (A.ell * k 1 α) α ∧ (A.ell : ℂ) * k 1 α = A.ell * bracket A k α / 2) := by
  exact M4a.lem_J_ii_proof hRH A k hK1 hα

/-- **`cl:thm:class` (i)** = **Theorem D**, local form (paper, verbatim):

Assume RH, \textup{(K1)}, \textup{(K2)}, \textup{(K3)}, \textup{(R)} for $D$, \textup{(H2-log)}, and
[...]
Then:
\begin{enumerate}
\item[(i)] $D$ continues analytically along every path in $D_L\setminus\cat_L$ that starts in
$R_L\cap D_L$, and every admissible germ at a point of a slit disc about $\alpha\in\cat_L\cap D_L$ is the germ
of a function of the form
\[
  X_\alpha(s)\log(s-\alpha)+H(s)\qquad\text{on the slit disc,}
\]
with $H$ holomorphic on the whole disc (the disc depends on $\alpha$, not on the germ) and the same
$X_\alpha$ for every germ; one counterclockwise loop round $\alpha$ adds $2\pi iX_\alpha$.
[...]
\end{enumerate}
[...] part \textup{(i)} holds under RH, \textup{(K1)},
\textup{(K2)}, \textup{(K3)}, \textup{(R)} and \textup{(H2-log)}.

Lean: `D` on `R_L` is the series `Dser W` ((R) with `F = P`). Admissible germs: `IsAdmissibleGermOn (Dser W)
(ℍ_L ∖ 𝒞_L) R_L`. The slit disc is `slitDiscL α r` (leftward radius removed), on which the principal `log(s - α)`
is holomorphic; another branch of `log` changes `H` by a constant multiple of `X_α`, which is holomorphic on the
disc. The clause "one counterclockwise loop round `α` adds `2πiX_α`" is not restated: it follows from the local form,
since the principal `log` gains `2πi` (review notes, choice 12). Hypotheses (Z1), (Z2), (Z3) (through
`nr:lem:Q`, `nr:lem:growthQ`, `cl:lem:P`(vi)). -/
theorem thm_class_i (hRH : RiemannHypothesis) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (A : Aff)
    (k : ℂ → ℂ → ℂ) (W : ℂ → ℕ → ℕ → ℂ) (hK1 : K1 A k) (hK2 : K2 A k) (hK3 : K3 A k)
    (hR : HypR A k W P) (hH2 : H2log A k) :
    (∀ γ : C(unitInterval, ℂ), (∀ t, γ t ∈ A.DL \ catalogueL A) → γ 0 ∈ A.RL ∩ A.DL →
      ContinuesAlong (Dser W) γ) ∧
    ∀ α ∈ catalogueL A ∩ A.DL, ∃ r : ℝ, 0 < r ∧
      ∀ s₁ ∈ slitDiscL α r, ∀ g : ℂ → ℂ,
        IsAdmissibleGermOn (Dser W) (A.HL \ catalogueL A) A.RL g s₁ →
        ∃ H : ℂ → ℂ, DifferentiableOn ℂ H (ball α r) ∧
          g =ᶠ[𝓝 s₁] fun s => Xcoef A k α s * Complex.log (s - α) + H s := by
  sorry

/-- **`cl:thm:class` (ii)** = **Theorem D**, boundary (paper, verbatim):

Assume RH, \textup{(K1)}, \textup{(K2)}, \textup{(K3)}, \textup{(R)} for $D$, \textup{(H2-log)}, and
\begin{itemize}
\item[(H3)] for every $s_0$ with $\Re L(s_0)=1$ and every $r>0$ there is a scaled-zero pinch $\alpha$
with $|\alpha-s_0|<r$ and $X_\alpha\not\equiv0$.
\end{itemize}
Then: [...]
\item[(ii)] No admissible germ extends meromorphically to any disc centred on a point of the line
$\Re L(s)=1$.

Lean: as `cl:thm:boundary`, the disc contains the base point `s₁` of the germ; "extends meromorphically" is
`GermExtendsMeromorphically` (paper 1). Hypotheses as for (i), plus (H3). -/
theorem thm_class_ii (hRH : RiemannHypothesis) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (A : Aff)
    (k : ℂ → ℂ → ℂ) (W : ℂ → ℕ → ℕ → ℂ) (hK1 : K1 A k) (hK2 : K2 A k) (hK3 : K3 A k)
    (hR : HypR A k W P) (hH2 : H2log A k) (hH3 : H3 A k) :
    ∀ (g : ℂ → ℂ) (s₁ : ℂ), IsAdmissibleGermOn (Dser W) (A.HL \ catalogueL A) A.RL g s₁ →
      ∀ s₀ ∈ A.lineL, ∀ r : ℝ, 0 < r → s₁ ∈ ball s₀ r →
        ¬ GermExtendsMeromorphically g s₁ (ball s₀ r) := by
  sorry

/-- **`cl:thm:class`**, the sufficient condition for (H3) (paper, verbatim):

[...] Hypothesis \textup{(H3)} holds if $\mathfrak b$ extends meromorphically to a neighbourhood of every
point of the line $\Re L(s)=1$ and is not identically zero there; [...]

Lean: near each point `s₀` of the line there is `f` meromorphic on a disc about `s₀`, equal to `𝔟` on the part of
the disc in `D_L`, and not identically zero near `s₀`. RH and (K1) are used (through `cl:lem:J`); (Z1) for
`c_b ≠ 0` (through `nr:lem:Q`). -/
theorem thm_class_H3_of_bracket (hRH : RiemannHypothesis) (hZ1 : Z1) (A : Aff) (k : ℂ → ℂ → ℂ)
    (hK1 : K1 A k)
    (hb : ∀ s₀ ∈ A.lineL, ∃ r : ℝ, 0 < r ∧ ∃ f : ℂ → ℂ, MeromorphicOn f (ball s₀ r) ∧
      EqOn f (bracket A k) (ball s₀ r ∩ A.DL) ∧ ¬ (∀ᶠ s in 𝓝[≠] s₀, f s = 0)) :
    H3 A k := by
  exact M4a.thm_class_H3_of_bracket_proof hRH hZ1 A k hK1 hb

/-- **`cl:thm:class`**, (H3) under (K4) (paper, verbatim):

[...] in particular it holds under
\textup{(K4)} when $\mathfrak b\not\equiv0$.

Lean: "`𝔟 ≢ 0`" is "not identically zero on `D_L`" (where (K1) makes `𝔟` holomorphic). -/
theorem thm_class_H3_of_K4 (hRH : RiemannHypothesis) (hZ1 : Z1) (A : Aff) (k : ℂ → ℂ → ℂ)
    (hK1 : K1 A k) (hK4 : K4 k) (hb : ∃ s ∈ A.DL, bracket A k s ≠ 0) : H3 A k := by
  exact M4a.thm_class_H3_of_K4_proof hRH hZ1 A k hK1 hK4 hb

/-- **`cl:cor:domain`** (a Remark in the paper; verbatim):

Under \textup{(H3)}, if $W\subset\C$ is open and connected and meets the line $\sigma=0$, no function $f$
meromorphic on $W$ has an admissible germ $g$ at a point $s_1\in W$ as its germ there. [...]

Lean: the remark is written in the normalisation `L(s) = 2s + 1` of Section 4.5, where the line is `σ = 0`; it is
stated here for general `L`, with the line `Re L(s) = 1` (review notes, choice 13). Hypotheses as for
`cl:thm:class`(ii). -/
theorem rem_class_domain (hRH : RiemannHypothesis) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (A : Aff)
    (k : ℂ → ℂ → ℂ) (W : ℂ → ℕ → ℕ → ℂ) (hK1 : K1 A k) (hK2 : K2 A k) (hK3 : K3 A k)
    (hR : HypR A k W P) (hH2 : H2log A k) (hH3 : H3 A k) {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsConnected U) (hUL : (U ∩ A.lineL).Nonempty) {g : ℂ → ℂ} {s₁ : ℂ} (hs₁ : s₁ ∈ U)
    (hg : IsAdmissibleGermOn (Dser W) (A.HL \ catalogueL A) A.RL g s₁) :
    ¬ GermExtendsMeromorphically g s₁ U := by
  sorry

/-- **`cl:thm:mero` (i)** = **Theorem E (i)** (paper, verbatim):

Assume RH, \textup{(K1)}, \textup{(K2)} and \textup{(R)} for $D^{\log}$.
\begin{enumerate}
\item[(i)] $D^{\log}$ continues to a single-valued meromorphic function on $\HH_L$, and on $D_L\cap\{\Re L<2\}$
\begin{equation}\label{cl:eq:strip}
  D^{\log}(s)=I(s)+\mathfrak b(s)\,Q(L(s)-1),
\end{equation}
with $I$ holomorphic there. Its poles in $\{1<\Re L<2\}$ are simple and are exactly the pinches $\alpha$ with
$L(\alpha)=1+b$, $b\in\Sigma\setminus\{1\}$, at which $\mathfrak b(\alpha)\ne0$; the residue at such a pinch is
$-c_b\,\mathfrak b(\alpha)/\ell=R_b\,\mathfrak b(\alpha)/\ell$. At the pinch $s_2$ with $L(s_2)=2$ there is a simple pole with
residue $k(1,s_2)/\ell=\mathfrak b(s_2)/(2\ell)$, or no pole if $k(1,s_2)=0$.
[...]
\end{enumerate}

Lean: `D^log` on `R_L` is the series `Dser W` ((R) with `F = Q`). The strip identity is part of the `∃ F` and is
asserted where `L(s) - 1 ∉ Σ_Q`, for every continuation `Qc` of `Q`. The pole and residue claims hold for every
meromorphic `F` agreeing with the series off a discrete subset of `R_L`. `-c_b = R_b` and
`k(1, s₂) = 𝔟(s₂)/2` are identities of the definitions and are not restated. Hypotheses (Z1), (Z2), (Z3) (through
`nr:lem:Q`, `nr:lem:growthQ`). -/
theorem thm_mero_i (hRH : RiemannHypothesis) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (A : Aff)
    (k : ℂ → ℂ → ℂ) (W : ℂ → ℕ → ℕ → ℂ) (hK1 : K1 A k) (hK2 : K2 A k) (hR : HypR A k W Q) :
    (∃ F : ℂ → ℂ, MeromorphicOn F A.HL ∧ EqOn F (Dser W) A.RL ∧
      ∃ I : ℂ → ℂ, DifferentiableOn ℂ I {s | 1 < (A.app s).re ∧ (A.app s).re < 2} ∧
        ∀ Qc : ℂ → ℂ, IsQCont Qc → ∀ s : ℂ, 1 < (A.app s).re → (A.app s).re < 2 →
          A.app s - 1 ∉ PoleSetQ → F s = I s + bracket A k s * Qc (A.app s - 1)) ∧
    ∀ F : ℂ → ℂ, MeromorphicOn F A.HL → F =ᶠ[codiscreteWithin A.RL] Dser W →
      (∀ s : ℂ, 1 < (A.app s).re → (A.app s).re < 2 → -1 ≤ meromorphicOrderAt F s ∧
        (meromorphicOrderAt F s < 0 ↔
          ∃ b ∈ PoleSetQ \ {1}, A.app s = 1 + b ∧ bracket A k s ≠ 0)) ∧
      (∀ b ∈ PoleSetQ \ {1}, ∀ α : ℂ, A.app α = 1 + b →
        HasResidue F α (Rcoef b * bracket A k α / A.ell)) ∧
      ∀ s₂ : ℂ, A.app s₂ = 2 → -1 ≤ meromorphicOrderAt F s₂ ∧
        HasResidue F s₂ (k 1 s₂ / A.ell) ∧ (k 1 s₂ = 0 → 0 ≤ meromorphicOrderAt F s₂) := by
  exact M4b.thm_mero_i_proof hRH hZ1 hZ2 hZ3 A k W hK1 hK2 hR

/-- **`cl:thm:mero` (ii)** = **Theorem E (ii)** (paper, verbatim):

\item[(ii)] If $\mathfrak b\equiv0$, then $D^{\log}$ is holomorphic on all of $\HH_L$.

Lean: "`𝔟 ≡ 0`" is `𝔟 = 0` on `D_L`. -/
theorem thm_mero_ii (hRH : RiemannHypothesis) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (A : Aff)
    (k : ℂ → ℂ → ℂ) (W : ℂ → ℕ → ℕ → ℂ) (hK1 : K1 A k) (hK2 : K2 A k) (hR : HypR A k W Q)
    (hb : ∀ s ∈ A.DL, bracket A k s = 0) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F A.HL ∧ EqOn F (Dser W) A.RL := by
  exact M4b.thm_mero_ii_proof hRH hZ1 hZ2 hZ3 A k W hK1 hK2 hR hb

/-- **`cl:thm:mero` (iii)** = **Theorem E (iii)** (paper, verbatim):

\item[(iii)] If \textup{(K4)} holds and $\mathfrak b\not\equiv0$, then for no $s_0$ with $\Re L(s_0)=1$ and no
$r>0$ is there a function meromorphic on $\disc(s_0,r)$ that agrees with $D^{\log}$ on
$\disc(s_0,r)\cap\HH_L$.

Lean: as `thm_boundary`, for every meromorphic continuation `F` of the series. -/
theorem thm_mero_iii (hRH : RiemannHypothesis) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (A : Aff)
    (k : ℂ → ℂ → ℂ) (W : ℂ → ℕ → ℕ → ℂ) (hK1 : K1 A k) (hK2 : K2 A k) (hR : HypR A k W Q)
    (hK4 : K4 k) (hb : ∃ s ∈ A.DL, bracket A k s ≠ 0) :
    ∀ F : ℂ → ℂ, MeromorphicOn F A.HL → F =ᶠ[codiscreteWithin A.RL] Dser W →
      IsNaturalBoundary F A.HL A.lineL := by
  exact M4b.thm_mero_iii_proof hRH hZ1 hZ2 hZ3 A k W hK1 hK2 hR hK4 hb

/-- **`cl:lem:P` (i)** (paper, verbatim):

Assume RH.
\begin{enumerate}
\item[(i)] $\Omega$ is open, connected and simply connected, and contains $\{\Re z>1\}$.
[...]
\end{enumerate} -/
theorem lem_P_i (hRH : RiemannHypothesis) :
    IsOpen OmegaP ∧ IsConnected OmegaP ∧ SimplyConnectedSpace OmegaP ∧ halfPlane 1 ⊆ OmegaP := by
  exact M6.lem_P_i_proof hRH

/-- **`cl:lem:P` (ii)** (paper, verbatim):

\item[(ii)] There is a unique holomorphic function $\tilde P$ on $\Omega$ with $\tilde P=P$ on $\{\Re z>1\}$;
it satisfies $\tilde P'=-Q$ and $\tilde P(\bar z)=\overline{\tilde P(z)}$.

Lean: uniqueness as functions on `Ω`; `Q` is any continuation `Qc` (holomorphic on `Ω ⊆ {Re z > 0} ∖ Σ`).
(Z1) for the symmetry (through `nr:lem:Q`(i)). -/
theorem lem_P_ii (hRH : RiemannHypothesis) (hZ1 : Z1) :
    ∃ Pt : ℂ → ℂ, DifferentiableOn ℂ Pt OmegaP ∧ EqOn Pt P (halfPlane 1) ∧
      (∀ Pt' : ℂ → ℂ, DifferentiableOn ℂ Pt' OmegaP → EqOn Pt' P (halfPlane 1) → EqOn Pt' Pt OmegaP) ∧
      (∀ Qc : ℂ → ℂ, IsQCont Qc → ∀ z ∈ OmegaP, HasDerivAt Pt (-Qc z) z) ∧
      ∀ z ∈ OmegaP, Pt (conj z) = conj (Pt z) := by
  exact M6.lem_P_ii_proof hRH hZ1

/-- **`cl:lem:P` (iii)** (paper, verbatim):

\item[(iii)] Every germ of a branch of $P$ continues analytically along every path in
$\{\Re z>0\}\setminus\Sigma$; every branch has derivative $-Q$, so two branches on a connected open set
differ by a constant.

Lean: a branch of `P` is `IsPBranch`. The final "so" clause is elementary calculus from the derivative and is not
restated. -/
theorem lem_P_iii (hRH : RiemannHypothesis) :
    (∀ (g : ℂ → ℂ) (z₁ : ℂ), IsPBranch g z₁ → ∀ γ : C(unitInterval, ℂ),
      (∀ t, γ t ∈ halfPlane 0 \ PoleSetQ) → γ 0 = z₁ → ContinuesAlong g γ) ∧
    ∀ (g : ℂ → ℂ) (z₁ : ℂ), IsPBranch g z₁ → ∀ Qc : ℂ → ℂ, IsQCont Qc →
      ∀ᶠ z in 𝓝 z₁, HasDerivAt g (-Qc z) z := by
  exact M6.lem_P_iii_proof hRH

/-- **`cl:lem:P` (iv)**, local form (paper, verbatim):

\item[(iv)] Let $a\in\Sigma$ and let $\Delta$ be a disc centred at $a$, contained in $\{\Re z>0\}$, with
$\Delta\cap\Sigma=\{a\}$. There is $E_a$ holomorphic on $\Delta$ such that on $\Delta$ slit along any ray from
$a$ every branch of $P$ equals $c_a\log(z-a)+E_a(z)+C$, with $\log$ any branch on the slit disc and a
constant $C$ depending on the branch. [...]

Lean: the ray is `a + [0,∞) e^{iθ}`; the branch of `log` used is `Log((z - a)/(-e^{iθ}))`, whose cut is exactly
that ray; any other branch on the slit disc differs by a constant, absorbed into `C`. A branch of `P` at a point
`z₁` of the slit disc is `IsPBranch`; "equals" is equality of germs at `z₁`. (Z1) through `nr:lem:Q`(i). -/
theorem lem_P_iv (hRH : RiemannHypothesis) (hZ1 : Z1) {a : ℂ} (ha : a ∈ PoleSetQ) {R : ℝ} (hR : 0 < R)
    (hΔ : ball a R ⊆ halfPlane 0) (hΔS : ball a R ∩ PoleSetQ = {a}) :
    ∃ E : ℂ → ℂ, DifferentiableOn ℂ E (ball a R) ∧
      ∀ θ : ℝ, ∀ z₁ ∈ ball a R \ {z | ∃ t : ℝ, 0 ≤ t ∧ z = a + t * exp (θ * I)},
        ∀ g : ℂ → ℂ, IsPBranch g z₁ → ∃ C : ℂ,
          g =ᶠ[𝓝 z₁] fun z => cP a * Complex.log ((z - a) / (-exp (θ * I))) + E z + C := by
  exact M6.lem_P_iv_proof hRH hZ1 ha hR hΔ hΔS

/-- **`cl:lem:P` (iv)**, the coefficients (paper, verbatim):

[...] Here $c_a=-R_a$ is real, $c_{\bar a}=c_a$, and
\[
  c_1=-1,\qquad c_{1/j}=-\frac{\mu(j)}j,\qquad c_{\rho/n}=\frac{\mu(n)m(\rho)}n,
\]
all non-zero.

Lean: `c_1 = -1` is also proved outright (`cP_one`). -/
theorem lem_P_iv_values (hRH : RiemannHypothesis) (hZ1 : Z1) :
    (∀ a ∈ PoleSetQ, (cP a).im = 0 ∧ cP (conj a) = cP a ∧ cP a ≠ 0) ∧ cP 1 = -1 ∧
    (∀ j : ℕ, 2 ≤ j → Squarefree j → cP (1 / (j : ℂ)) = -(mu j / j)) ∧
    ∀ n : ℕ, 1 ≤ n → Squarefree n → ∀ ρ ∈ NontrivialZeros,
      cP (ρ / (n : ℂ)) = mu n * (zetaMult ρ : ℂ) / n := by
  exact M4a.lem_P_iv_values_proof hRH hZ1

/-- **`cl:lem:P` (v)** (paper, verbatim):

\item[(v)] $\Omega\cap\{\Re z>\frac12\}=\{\Re z>\frac12\}\setminus(\frac12,1]$, and
$\tilde P(z)=-\Log(z-1)+E_1(z)$ there, with $E_1$ holomorphic on $\{\Re z>\frac12\}$ and $\Log$ principal.

Lean: `P̃` is any holomorphic function on `Ω` equal to `P` on `Re z > 1` (unique by (ii)). -/
theorem lem_P_v (hRH : RiemannHypothesis) :
    OmegaP ∩ halfPlane (1 / 2) = halfPlane (1 / 2) \ {z | ∃ x : ℝ, 1 / 2 < x ∧ x ≤ 1 ∧ z = x} ∧
    ∀ Pt : ℂ → ℂ, DifferentiableOn ℂ Pt OmegaP → EqOn Pt P (halfPlane 1) →
      ∃ E₁ : ℂ → ℂ, DifferentiableOn ℂ E₁ (halfPlane (1 / 2)) ∧
        ∀ z ∈ OmegaP ∩ halfPlane (1 / 2), Pt z = -Complex.log (z - 1) + E₁ z := by
  exact M6.lem_P_v_proof hRH

/-- **`cl:lem:P` (vi)** (paper, verbatim):

\item[(vi)] For $0<\varepsilon\le\frac12$ there is $C_\varepsilon$ with $|\tilde P(x+iy)|\le C_\varepsilon\log|y|$ for
$\frac12+\varepsilon\le x\le3$ and $|y|\ge3$; and $|\tilde P(z)|\le P(\Re z)$ for $\Re z>1$.

Lean: `P(Re z)` is the series at the real point (a real number). Hypotheses (Z2), (Z3) (through
`nr:lem:growthQ`), and (Z1): the multiplicity bound from (Z2) is used at negative heights, which with Lean's `Z2`
(zeros with `0 < γ ≤ t`) needs `m(ρ̄) = m(ρ)` (as in `lem_Q_iii`). -/
theorem lem_P_vi (hRH : RiemannHypothesis) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) :
    ∀ Pt : ℂ → ℂ, DifferentiableOn ℂ Pt OmegaP → EqOn Pt P (halfPlane 1) →
      (∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∃ C : ℝ, ∀ x y : ℝ, 1 / 2 + ε ≤ x → x ≤ 3 → 3 ≤ |y| →
        ‖Pt (x + y * I)‖ ≤ C * Real.log |y|) ∧
      ∀ z : ℂ, 1 < z.re → ‖Pt z‖ ≤ (P z.re).re := by
  exact M6.lem_P_vi_proof hRH hZ1 hZ2 hZ3

/-- **`cl:ex:G`**, the hypotheses (paper, verbatim):

$G(s)=\sum_{p,q}(p+q)^{-s}$: $L(s)=s$, $k(z,s)=K_s(z)$. [...] so $k$ is
holomorphic on $\{(z,s):\sigma>0,\ z\in\mathrm{Str}(s)\}$, which is (K1) on $D_L$ and (H2a). (K2): [...]
(K3), (K4) are clear. (R): the series converges absolutely for $\sigma>2$, is
holomorphic there and real for real $s$, and the identity is Lemma~\ref{nr:lem:MB} with $P$ in place of
$Q$ (the same proof). $\mathfrak b(s)=2\Gamma(1)\Gamma(s-1)/\Gamma(s)=2/(s-1)\not\equiv0$, so (H3) holds.

Lean: the bracket formula, (K1), (H2a) and (K3) are proved outright (`bracket_kerG`, `K1_kerG`, `H2a_kerG`,
`K3_kerG`). RH, (Z1) (through (H3), `cl:thm:class`'s sufficient
condition). (Z6) is used for (K2) and (R) (Stirling, `nr:lem:MB`). -/
theorem ex_G_hyp (hRH : RiemannHypothesis) (hZ1 : Z1) (hZ6 : Z6) :
    K1 Aff.idL kerG ∧ H2a Aff.idL kerG ∧ K2 Aff.idL kerG ∧ K3 Aff.idL kerG ∧ K4 kerG ∧
      HypR Aff.idL kerG WG P ∧ H3 Aff.idL kerG := by
  exact M4b.ex_G_hyp_proof hRH hZ1 hZ6

/-- **`cl:ex:G`**, the conclusions (paper, verbatim):

[...] Theorem~\ref{cl:thm:class} gives: every branch of $G$ near $\alpha\in\cat_L$ is $X_\alpha\log(s-\alpha)+(\text{holomorphic})$
with $X'_{1+a}(1+a)=c_1c_a\cdot2/a=-2c_a/a$, that is, $2\mu(j)$ at $1+1/j$ and $-2\mu(n)m(\rho)/\rho$ at $1+\rho/n$, and
$X_2'(2)=1$; and $\sigma=1$ is a natural boundary of $G$ on every branch.

Lean: `G = Dser WG` (`Dser_WG`); branches are admissible germs for `ℍ ∖ 𝒞_L` and `σ > 2` (under RH `𝒞_L` is paper
1's catalogue, `prop_catalogue_i`). The coefficient values are paper 1's `HasCatalogueValues`, as in paper 1's
`thm_A_local`. Hypotheses RH, (Z1), (Z2), (Z3), (Z6). -/
theorem ex_G (hRH : RiemannHypothesis) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6) :
    (∀ α ∈ catalogueL Aff.idL, ∃ r : ℝ, 0 < r ∧ ∀ s₁ ∈ slitDiscL α r, ∀ g : ℂ → ℂ,
      IsAdmissibleGermOn G (Aff.idL.HL \ catalogueL Aff.idL) Aff.idL.RL g s₁ →
      ∃ H : ℂ → ℂ, DifferentiableOn ℂ H (ball α r) ∧
        g =ᶠ[𝓝 s₁] fun s => Xcoef Aff.idL kerG α s * Complex.log (s - α) + H s) ∧
    HasCatalogueValues (fun α => deriv (Xcoef Aff.idL kerG α) α) ∧
    ∀ (g : ℂ → ℂ) (s₁ : ℂ), IsAdmissibleGermOn G (Aff.idL.HL \ catalogueL Aff.idL) Aff.idL.RL g s₁ →
      ∀ y r : ℝ, 0 < r → s₁ ∈ ball (1 + (y : ℂ) * I) r →
        ¬ GermExtendsMeromorphically g s₁ (ball (1 + (y : ℂ) * I) r) := by
  exact M6.ex_G_proof hRH hZ1 hZ2 hZ3 hZ6

/-- **`cl:ex:squares`**, the hypotheses (paper, verbatim):

$\sum_{p,q}(p^2+q^2)^{-s}$: $L(s)=2s$, $k(z,s)=\frac12\Gamma(z/2)\Gamma(s-z/2)/\Gamma(s)$, [...]
(K1) and (H2a). (K2) by Stirling as before; (K3), (K4)
clear. (R): [...] The bracket is
\[
  \mathfrak b(s)=k(1,s)+k(2s-1,s)=\frac{\Gamma(\frac12)\Gamma(s-\frac12)}{\Gamma(s)}=\sqrt\pi\,\frac{\Gamma(s-\frac12)}{\Gamma(s)},
\]
whose zeros are those of $1/\Gamma(s)$, at $s=0,-1,-2,\dots$; so $\mathfrak b$ has no zero in $\sigma>0$ and (H3) holds.

Lean: the bracket formula and "no zero" are asserted on `ℍ_L = {σ > 1/2}`, where `𝔟` is holomorphic. The paper's
"no zero in `σ > 0`" is about the meromorphic function `𝔟`, which has a pole at `s = 1/2` (from `Γ(s - 1/2)`);
Lean's value there is the junk `Γ(0) = 0`, so a pointwise "`≠ 0`" on `σ > 0` would be false. (H3) uses `𝔟` only on
`ℍ_L`. The bracket clause is proved outright (`bracket_kerSq`). The paper says
that `𝔟` is meromorphic with a pole at `s = 1/2` and zero-free on `ℍ_L`. Hypotheses RH, (Z1), (Z6). -/
theorem ex_squares_hyp (hRH : RiemannHypothesis) (hZ1 : Z1) (hZ6 : Z6) :
    K1 Aff.twoL kerSq ∧ H2a Aff.twoL kerSq ∧ K2 Aff.twoL kerSq ∧ K3 Aff.twoL kerSq ∧ K4 kerSq ∧
      HypR Aff.twoL kerSq WSq P ∧
      (∀ s : ℂ, 1 / 2 < s.re →
        bracket Aff.twoL kerSq s = (Real.sqrt Real.pi : ℂ) * Gamma (s - 1 / 2) / Gamma s ∧
          bracket Aff.twoL kerSq s ≠ 0) ∧
      H3 Aff.twoL kerSq := by
  exact M4b.ex_squares_hyp_proof hRH hZ1 hZ6

/-- **`cl:ex:squares`**, the conclusions (paper, verbatim):

[...] The pinches are $s=(1+b)/2$, $b\in\Sigma$, the scaled-zero pinches $(1+\rho/n)/2$, and the boundary line is
$\sigma=\frac12$. Theorem~\ref{cl:thm:class}: under RH every branch has a singularity $X_\alpha\log(s-\alpha)$ at every
pinch, with $X'_\alpha(\alpha)=2c_1c_b\mathfrak b(\alpha)\ne0$ for $b\ne1$ and $X'_1(1)=2k(1,1)=\pi$ at the pinch $s=1$, and
$\sigma=\frac12$ is a natural boundary of $\sum_{p,q}(p^2+q^2)^{-s}$ on every branch.
[...]

Lean: `b = L(α) - 1 = 2α - 1`. The closing comparison with El-Gammal's conjectures is commentary and is cut.
Hypotheses RH, (Z1), (Z2), (Z3), (Z6). -/
theorem ex_squares (hRH : RiemannHypothesis) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6) :
    (∀ α ∈ catalogueL Aff.twoL, ∃ r : ℝ, 0 < r ∧ ∀ s₁ ∈ slitDiscL α r, ∀ g : ℂ → ℂ,
      IsAdmissibleGermOn (Dser WSq) (Aff.twoL.HL \ catalogueL Aff.twoL) Aff.twoL.RL g s₁ →
      ∃ H : ℂ → ℂ, DifferentiableOn ℂ H (ball α r) ∧
        g =ᶠ[𝓝 s₁] fun s => Xcoef Aff.twoL kerSq α s * Complex.log (s - α) + H s) ∧
    (∀ α ∈ catalogueL Aff.twoL, 2 * α - 1 ≠ 1 →
      deriv (Xcoef Aff.twoL kerSq α) α = 2 * cP 1 * cP (2 * α - 1) * bracket Aff.twoL kerSq α ∧
        deriv (Xcoef Aff.twoL kerSq α) α ≠ 0) ∧
    deriv (Xcoef Aff.twoL kerSq 1) 1 = 2 * kerSq 1 1 ∧ 2 * kerSq 1 1 = Real.pi ∧
    ∀ (g : ℂ → ℂ) (s₁ : ℂ),
      IsAdmissibleGermOn (Dser WSq) (Aff.twoL.HL \ catalogueL Aff.twoL) Aff.twoL.RL g s₁ →
      ∀ y r : ℝ, 0 < r → s₁ ∈ ball (1 / 2 + (y : ℂ) * I) r →
        ¬ GermExtendsMeromorphically g s₁ (ball (1 / 2 + (y : ℂ) * I) r) := by
  sorry

/-- **`cl:ex:S`**, the hypotheses (paper, verbatim):

$S(s)=\sum_{p,q}p^{1-s}q^{2-s}(p^2+q^2)^{-2}$: $L(s)=2s+1$ and $k(z,s)=\frac12K\big(\frac{z-s+1}2\big)$ with
$K(w)=\Gamma(w)\Gamma(2-w)$. [...] so (K1) holds on $D_L=\{0<\sigma<1\}$. It fails for $\sigma>1$, [...]
so (H2a) is not available; but $k(z,s)=g(z-s)$ with $g(w)=\frac12K\big(\frac{w+1}2\big)$ meromorphic on
$\C$, which is (H2b) with $\theta=1$: [...]
(K2): [...] (K3): $K$ is real on the
real axis. (K4): clear. (R): [...] the series converges absolutely on $R_L=\{\sigma>\frac12\}$, where it is holomorphic and real
for real $s$. [...] Fubini gives \eqref{cl:eq:D}. The
pinches are $\frac12$, $\frac1{2j}$ and $\frac\rho{2n}$, the boundary line is $\sigma=0$, and the bracket is
\[
  \mathfrak b(s)=k(1,s)+k(2s,s)=\tfrac12\big[K(1-\tfrac s2)+K(\tfrac{s+1}2)\big],
\]
meromorphic on $\C$ and not identically zero ($\mathfrak b(0)=\frac12[K(1)+K(\frac12)]=\frac12(1+\frac\pi2)$). So (H3)
holds, [...]

Hypotheses RH, (Z1), (Z6). -/
theorem ex_S_hyp (hRH : RiemannHypothesis) (hZ1 : Z1) (hZ6 : Z6) :
    K1 Aff.twoOneL kerS ∧ H2b kerS ∧ K2 Aff.twoOneL kerS ∧ K3 Aff.twoOneL kerS ∧ K4 kerS ∧
      HypR Aff.twoOneL kerS WS P ∧
      (∀ s : ℂ, bracket Aff.twoOneL kerS s = 1 / 2 * (KS (1 - s / 2) + KS ((s + 1) / 2))) ∧
      bracket Aff.twoOneL kerS 0 = 1 / 2 * (1 + Real.pi / 2) ∧
      H3 Aff.twoOneL kerS := by
  exact M4b.ex_S_hyp_proof hRH hZ1 hZ6

/-- **`cl:ex:S`**, the conclusions (paper, verbatim):

[...] and Theorem~\ref{cl:thm:class} gives: no germ of $S$ reached by continuation along a path in $\sigma>0$
that starts in $\sigma>\frac12$ and avoids the pinches extends meromorphically to any disc centred on the
imaginary axis, and every branch has the local model $X_\alpha\log(s-\alpha)+(\text{holomorphic})$ at every
pinch, with $X'_{\rho/(2n)}\big(\tfrac\rho{2n}\big)=-\frac{\mu(n)m(\rho)}n\big[K(1-\tfrac\rho{4n})+K(\tfrac12+\tfrac\rho{4n})\big]$.
Here more is true: this coefficient is non-zero at \emph{every} scaled-zero pinch, not only on a dense
set. [...]

Lean: the scaled-zero pinches of `L(s) = 2s + 1` are `ρ/(2n)`, `n ≥ 1` squarefree. Hypotheses RH, (Z1), (Z2), (Z3),
(Z6). -/
theorem ex_S (hRH : RiemannHypothesis) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6) :
    (∀ (g : ℂ → ℂ) (s₁ : ℂ),
      IsAdmissibleGermOn (Dser WS) (Aff.twoOneL.HL \ catalogueL Aff.twoOneL) Aff.twoOneL.RL g s₁ →
      ∀ y r : ℝ, 0 < r → s₁ ∈ ball ((y : ℂ) * I) r →
        ¬ GermExtendsMeromorphically g s₁ (ball ((y : ℂ) * I) r)) ∧
    (∀ α ∈ catalogueL Aff.twoOneL, ∃ r : ℝ, 0 < r ∧ ∀ s₁ ∈ slitDiscL α r, ∀ g : ℂ → ℂ,
      IsAdmissibleGermOn (Dser WS) (Aff.twoOneL.HL \ catalogueL Aff.twoOneL) Aff.twoOneL.RL g s₁ →
      ∃ H : ℂ → ℂ, DifferentiableOn ℂ H (ball α r) ∧
        g =ᶠ[𝓝 s₁] fun s => Xcoef Aff.twoOneL kerS α s * Complex.log (s - α) + H s) ∧
    ∀ n : ℕ, 1 ≤ n → Squarefree n → ∀ ρ ∈ NontrivialZeros,
      deriv (Xcoef Aff.twoOneL kerS (ρ / (2 * n))) (ρ / (2 * n)) =
          -(mu n * (zetaMult ρ : ℂ) / n) * (KS (1 - ρ / (4 * n)) + KS (1 / 2 + ρ / (4 * n))) ∧
        deriv (Xcoef Aff.twoOneL kerS (ρ / (2 * n))) (ρ / (2 * n)) ≠ 0 := by
  sorry

/-- The hypotheses of `cl:thm:mero` for `T` (no quote of its own; the checks are those of `cl:ex:G`, "(K1) on
`D_L`", "(K2): ...", and (R) for `D^log = T` is `nr:lem:MB`). (K1) is also proved outright (`K1_kerG`). Hypotheses RH
(choice 1), (Z6) ((K2) and `nr:lem:MB`). -/
theorem ex_T_hyp (hRH : RiemannHypothesis) (hZ6 : Z6) :
    K1 Aff.idL kerG ∧ K2 Aff.idL kerG ∧ HypR Aff.idL kerG WT Q := by
  exact M4b.ex_T_hyp_proof hRH hZ6

/-- **Theorem E for `T`** (paper, verbatim; introduction, the unlabelled paragraph before Theorem B):

Under RH it is immediate: on $1<\sigma<2$ one has $T(s)=I(s)+2Q(s-1)/(s-1)$ with $I$ holomorphic
(Theorem~\ref{intro:thm:E}(i) applied to $T$, equation~\eqref{cl:eq:strip}; the identity is also
in~\cite{SlothouberPaper1}), [...]

Lean: `T` on `ℍ` is a meromorphic continuation `F` equal to the series on `σ > 2`; the identity is asserted where
`s - 1 ∉ Σ_Q`, for every continuation `Qc` of `Q`. Proved from `thm_mero_i` (Theorem E(i)), `ex_T_hyp` and
`bracket_kerG` (`𝔟 = 2/(s-1)`). The rest of the sentence (Landau–Walfisz) is `cor_LW`. Hypotheses RH, (Z1), (Z2),
(Z3) (through `cl:thm:mero`), (Z6) (through `ex_T_hyp`). -/
theorem intro_T_strip (hRH : RiemannHypothesis) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6) :
    ∃ F : ℂ → ℂ, MeromorphicOn F HH ∧ EqOn F T (halfPlane 2) ∧
      ∃ I : ℂ → ℂ, DifferentiableOn ℂ I {s | 1 < s.re ∧ s.re < 2} ∧
        ∀ Qc : ℂ → ℂ, IsQCont Qc → ∀ s : ℂ, 1 < s.re → s.re < 2 → s - 1 ∉ PoleSetQ →
          F s = I s + 2 * Qc (s - 1) / (s - 1) := by
  obtain ⟨hK1, hK2, hR⟩ := ex_T_hyp hRH hZ6
  obtain ⟨⟨F, hF, hFT, I, hI, hrep⟩, -⟩ := thm_mero_i hRH hZ1 hZ2 hZ3 Aff.idL kerG WT hK1 hK2 hR
  rw [idL_HL] at hF
  rw [idL_RL, Dser_WT] at hFT
  refine ⟨F, hF, hFT, I, ?_, fun Qc hQc s hs1 hs2 hsQ => ?_⟩
  · simpa only [idL_app] using hI
  · have := hrep Qc hQc s (by rwa [idL_app]) (by rwa [idL_app]) (by rwa [idL_app])
    rw [this, idL_app, bracket_kerG hs1]
    ring

/-- **`cl:prop:T0`** (paper, verbatim):

Assume RH. The Mellin--Barnes kernel of $W_0$ with $L(s)=s$ is
$k_0(z,s)=K_s(z)\,(z-1)(s-1-z)$; it satisfies \textup{(K1)}--\textup{(K4)} and \textup{(R)} for $T_0$ and for
$G_0$, and its bracket vanishes identically: $\mathfrak b_0(s)=k_0(1,s)+k_0(s-1,s)\equiv0$. Consequently $T_0$ is
holomorphic on all of $\HH=\{\sigma>1\}$: each of the poles that $T$ has at $2$, $1+1/j$ and $1+\rho/n$ is absent
from $T_0$. Moreover $T_0\not\equiv0$.

Lean: "the kernel of `W₀` is `k₀`" is (R) for `k₀` (with `Q` for `T₀`, `P` for `G₀`). The bracket clause is proved
outright (`bracket_k0`). "`T₀ ≢ 0`" is a point of `σ > 2` where the series is non-zero. Hypotheses RH, (Z1), (Z2),
(Z3) (through `cl:thm:mero`(ii)), (Z6) ((K2), (R)). -/
theorem prop_T0 (hRH : RiemannHypothesis) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6) :
    K1 Aff.idL k0 ∧ K2 Aff.idL k0 ∧ K3 Aff.idL k0 ∧ K4 k0 ∧ HypR Aff.idL k0 W0log Q ∧
      HypR Aff.idL k0 W0 P ∧ (∀ s, bracket Aff.idL k0 s = 0) ∧
      (∃ F : ℂ → ℂ, DifferentiableOn ℂ F HH ∧ EqOn F T0 (halfPlane 2)) ∧
      ∃ s : ℂ, 2 < s.re ∧ T0 s ≠ 0 := by
  exact M4b.prop_T0_proof hRH hZ1 hZ2 hZ3 hZ6




/-- **`cl:rem:order`**, the coefficient expansions (a Remark in the paper; verbatim):

For the unweighted series $G_0$ the bracket also vanishes, but the pinches survive at higher order.
The kernel $k_0$ is symmetric under $z\mapsto s-z$, so $J_{b1}=J_{1b}$ (substitute $z\mapsto s-z$ in
$J_{b1}=\int_b^{s-1}k_0$). Let $\alpha=1+b$ with $b\in\Sigma\setminus\{1\}$, $\delta=s-\alpha$ and $z=1+t$. Then
$s-1-z=(b-1)+\delta-t$ and $K_s(1+t)\to K_\alpha(1)=\Gamma(b)/\Gamma(1+b)=1/b$ as $(t,\delta)\to0$, so
$k_0(1+t,\alpha+\delta)=t\,\frac{b-1}b+O\big(|t|(|t|+|\delta|)\big)$ and
\begin{gather*}
  J_{1b}(s)=\int_0^\delta k_0(1+t,s)\,dt=\frac{b-1}{2b}\,\delta^2+O(\delta^3),\\
  X_\alpha(s)=2c_1c_bJ_{1b}(s)=c_1c_b\,\frac{b-1}b\,\delta^2+O(\delta^3)\not\equiv0 .
\end{gather*}
At $\alpha=2$, with $z=1+t$ and $s=2+\delta$, $k_0(1+t,2+\delta)=K_{2+\delta}(1+t)\,t(\delta-t)$ and
$X_2=J_{11}=\int_0^\delta t(\delta-t)\,dt\,(1+O(|\delta|))=\frac16\delta^3+O(\delta^4)$. [...]

Lean: `X_α = Xcoef Aff.idL k0 α`. The expansions as `IsBigO` at `α`: `X_{1+b}(s) - c₁c_b (b-1)/b (s-α)² = O((s-α)³)`
for `b ∈ Σ ∖ {1}`, and `X₂(s) - (s-2)³/6 = O((s-2)⁴)`. (Under RH `α = 1 + b` lies in `D_L`, where `X_α` is a genuine
integral.) The intermediate claims are steps of the computation and are not restated; `c₁c_b ≠ 0` and `b ≠ 1` give
`X_{1+b} ≢ 0`. Hypothesis RH (choice 1). -/
theorem rem_order_coeff (hRH : RiemannHypothesis) :
    (∀ b ∈ PoleSetQ \ {1},
      (fun s => Xcoef Aff.idL k0 (1 + b) s - cP 1 * cP b * ((b - 1) / b) * (s - (1 + b)) ^ 2) =O[𝓝 (1 + b)]
        fun s => (s - (1 + b)) ^ 3) ∧
    (fun s => Xcoef Aff.idL k0 2 s - (s - 2) ^ 3 / 6) =O[𝓝 2] fun s => (s - 2) ^ 4 := by
  exact M4a.rem_order_coeff_proof hRH

/-- **`cl:rem:order`**, (H3) for `k₀` (a Remark in the paper; verbatim):

[...] So (H3) holds for $k_0$, [...]

Lean: (H3) for `L(s) = s` and `k₀`. Hypotheses RH, (Z1) (`c_b ≠ 0`, through `cl:lem:P`(iv)). The density of the
scaled-zero pinches comes from paper 1's `lem_density`, without (Z2), as for `thm_class_H3_of_K4` (choice 9). -/
theorem rem_order_H3 (hRH : RiemannHypothesis) (hZ1 : Z1) : H3 Aff.idL k0 := by
  exact M4a.rem_order_H3_proof hRH hZ1

/-- **`cl:rem:order`**, the boundary and local models of `G₀` (a Remark in the paper; verbatim):

[...] and
Theorem~\ref{cl:thm:class} gives: under RH, $\sigma=1$ is a natural boundary of $G_0$ on every branch, with
local models $X_\alpha\log(s-\alpha)$ of order $\delta^2\log\delta$ at $1+b$, $b\ne1$, and $\delta^3\log\delta$ at $2$, in place of
the $\delta\log\delta$ of $G$. [...]

Lean: as `ex_G`, with `G₀ = Dser W0` and `k₀`: the local model at every pinch, and no admissible germ extends
meromorphically to a disc centred on the line `σ = 1` (containing its base point). The orders are `rem_order_coeff`.
Proved from `thm_class_i`, `thm_class_ii` (with (K1)–(K3) and (R) from `prop_T0`, (H2-log) from `H2a_k0` and
`H2log_of_H2a`, (H3) from `rem_order_H3`) and `lem_J_ii` (every pinch is in `D_L`). Hypotheses RH, (Z1), (Z2), (Z3),
(Z6). -/
theorem rem_order_G0 (hRH : RiemannHypothesis) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6) :
    (∀ α ∈ catalogueL Aff.idL, ∃ r : ℝ, 0 < r ∧ ∀ s₁ ∈ slitDiscL α r, ∀ g : ℂ → ℂ,
      IsAdmissibleGermOn G0 (Aff.idL.HL \ catalogueL Aff.idL) Aff.idL.RL g s₁ →
      ∃ H : ℂ → ℂ, DifferentiableOn ℂ H (ball α r) ∧
        g =ᶠ[𝓝 s₁] fun s => Xcoef Aff.idL k0 α s * Complex.log (s - α) + H s) ∧
    ∀ (g : ℂ → ℂ) (s₁ : ℂ), IsAdmissibleGermOn G0 (Aff.idL.HL \ catalogueL Aff.idL) Aff.idL.RL g s₁ →
      ∀ y r : ℝ, 0 < r → s₁ ∈ ball (1 + (y : ℂ) * I) r →
        ¬ GermExtendsMeromorphically g s₁ (ball (1 + (y : ℂ) * I) r) := by
  obtain ⟨hK1, hK2, hK3, -, -, hR, -⟩ := prop_T0 hRH hZ1 hZ2 hZ3 hZ6
  have hH2 := H2log_of_H2a Aff.idL k0 H2a_k0
  have hcl := thm_class_i hRH hZ1 hZ2 hZ3 Aff.idL k0 W0 hK1 hK2 hK3 hR hH2
  refine ⟨fun α hα => hcl.2 α ⟨hα, (lem_J_ii hRH Aff.idL k0 hK1 hα).1⟩, ?_⟩
  intro g s₁ hg y r hr hs₁
  refine thm_class_ii hRH hZ1 hZ2 hZ3 Aff.idL k0 W0 hK1 hK2 hK3 hR hH2 (rem_order_H3 hRH hZ1) g s₁ hg
    (1 + (y : ℂ) * I) ?_ r hr hs₁
  show (Aff.idL.app (1 + (y : ℂ) * I)).re = 1
  simp [idL_app]

/-- **`cl:rem:order`**, the `r`-th power kernels: coefficient expansion (a Remark in the paper; verbatim):

[...] Replacing the factor $(z-1)(s-1-z)$ by its $r$-th power, $r\in\Z_{\ge1}$ (the kernel of
a finite combination of the weights $p^iq^j(p+q)^{-s-i-j}$ with polynomial coefficients in $s$), the same
computation gives order $\delta^{r+1}\log\delta$ at $1+b$, $b\ne1$. [...]

Lean: `k_r(z,s) = K_s(z)((z-1)(s-1-z))^r` (`kr r`), `X_α = Xcoef Aff.idL (kr r) α`, `α = 1 + b`, `b ∈ Σ ∖ {1}`:
`X_α(s) - 2c₁c_b(b-1)^r/(b(r+1)) (s-α)^{r+1} = O((s-α)^{r+2})`. The remark gave no constant (the revised paper gives this one in `cl:prop:order`); it is "the same
computation" as for `k₀`: `k_r(1+t, α+δ) = t^r (b-1)^r/b + O(|t|^r(|t|+|δ|))`, so `J_{1b} = (b-1)^r/(b(r+1)) δ^{r+1} +
O(δ^{r+2})`, `J_{b1} = J_{1b}` (`k_r` is symmetric under `z ↦ s - z`), and `X_α = c₁c_b(J_{1b} + J_{b1})`. At `r = 1`
it is the constant `c₁c_b(b-1)/b` of `rem_order_coeff` (`rem_order_kr_const_one`, `kr_one`). The leading coefficient
is non-zero (`rem_order_kr_coeff_ne`), which is "order `δ^{r+1}`". Hypothesis RH (choice 1). -/
theorem rem_order_kr_coeff (hRH : RiemannHypothesis) (r : ℕ) (hr : 1 ≤ r) :
    ∀ b ∈ PoleSetQ \ {1},
      (fun s => Xcoef Aff.idL (kr r) (1 + b) s -
          2 * cP 1 * cP b * (b - 1) ^ r / (b * ((r : ℂ) + 1)) * (s - (1 + b)) ^ (r + 1)) =O[𝓝 (1 + b)]
        fun s => (s - (1 + b)) ^ (r + 2) := by
  exact M4a.rem_order_kr_coeff_proof hRH r hr

/-- **`cl:rem:order`**, the `r`-th power kernels: the leading coefficient is non-zero (part of "order
`δ^{r+1} log δ`"; see `rem_order_kr_coeff` for the quote). Proved from `lem_P_iv_values` (`c_b ≠ 0`), `cP_one`, and
`b ≠ 0`, `b ≠ 1`. Hypotheses RH, (Z1) (through `cl:lem:P`(iv)). -/
theorem rem_order_kr_coeff_ne (hRH : RiemannHypothesis) (hZ1 : Z1) (r : ℕ) :
    ∀ b ∈ PoleSetQ \ {1}, 2 * cP 1 * cP b * (b - 1) ^ r / (b * ((r : ℂ) + 1)) ≠ 0 := by
  rintro b ⟨hb, hb1⟩
  have hcb := ((lem_P_iv_values hRH hZ1).1 b hb).2.2
  have hb0 := ne_zero_of_mem_poleSetQ hb
  have hb1' : b - 1 ≠ 0 := sub_ne_zero.mpr hb1
  have hr1 : (r : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero r
  rw [cP_one]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero (neg_ne_zero.mpr one_ne_zero)) hcb)
    (pow_ne_zero _ hb1')) (mul_ne_zero hb0 hr1)

/-- **`cl:rem:order`**, the `r`-th power kernels: (K2) (a Remark in the paper; see `rem_order_kr_coeff` for the
quote). The paper does not list the hypotheses for `k_r`; "the same computation" uses those of `k₀`, for which the
proof of `cl:prop:T0` says "(K1)--(K4) hold as for $K_s$ [...]; the polynomial factor does not affect the exponential
decay in (K2)". (K1), (H2a), (K3) for `k_r` are proved outright (`K1_kr`, `H2a_kr`, `K3_kr`). Hypotheses RH
(choice 1), (Z6) (Stirling). -/
theorem rem_order_kr_K2 (hRH : RiemannHypothesis) (hZ6 : Z6) (r : ℕ) : K2 Aff.idL (kr r) := by
  exact M4a.rem_order_kr_K2_proof hRH hZ6 r

/-- **`cl:rem:order`**, the `r`-th power kernels: the local model (a Remark in the paper; see `rem_order_kr_coeff`
for the quote).

Lean: for any weight `W` whose kernel is `k_r` (the paper's "the kernel of a finite combination of the weights
`p^iq^j(p+q)^{-s-i-j}`"; formally (R) for `k_r` with `F = P`, the unweighted logarithmic class, as for `G₀`), the
local model at every pinch is `X_α log(s - α) + H` with `X_α = Xcoef Aff.idL (kr r) α`, whose order at `α = 1 + b`
is `δ^{r+1}` (`rem_order_kr_coeff`, `rem_order_kr_coeff_ne`). Stated for every `r ∈ ℕ` (`r = 0` is the kernel `K_s`).
The paper claims no natural boundary for these series, so none is stated. Proved from `thm_class_i` (with
`K1_kr`, `rem_order_kr_K2`, `K3_kr`, and (H2-log) from `H2a_kr` and `H2log_of_H2a`) and `lem_J_ii`. Hypotheses RH,
(Z1), (Z2), (Z3), (Z6). -/
theorem rem_order_kr_model (hRH : RiemannHypothesis) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6) (r : ℕ)
    (W : ℂ → ℕ → ℕ → ℂ) (hR : HypR Aff.idL (kr r) W P) :
    ∀ α ∈ catalogueL Aff.idL, ∃ ε : ℝ, 0 < ε ∧ ∀ s₁ ∈ slitDiscL α ε, ∀ g : ℂ → ℂ,
      IsAdmissibleGermOn (Dser W) (Aff.idL.HL \ catalogueL Aff.idL) Aff.idL.RL g s₁ →
      ∃ H : ℂ → ℂ, DifferentiableOn ℂ H (ball α ε) ∧
        g =ᶠ[𝓝 s₁] fun s => Xcoef Aff.idL (kr r) α s * Complex.log (s - α) + H s := by
  have hK1 := K1_kr r
  have hcl := thm_class_i hRH hZ1 hZ2 hZ3 Aff.idL (kr r) W hK1 (rem_order_kr_K2 hRH hZ6 r) (K3_kr r) hR
    (H2log_of_H2a Aff.idL (kr r) (H2a_kr r))
  exact fun α hα => hcl.2 α ⟨hα, (lem_J_ii hRH Aff.idL (kr r) hK1 hα).1⟩

/-- **`cl:lem:Qleft`** (paper, verbatim):

Assume RH.
\begin{enumerate}
\item[(i)] For $\frac13<x_0<\frac12$ there is $C(x_0)$ with $|Q(x_0+iy)|\le C(x_0)\log(|y|+3)$ for all real $y$.
\item[(ii)] There is an absolute constant $C$ such that for every $Y\ge3$ there is $Y'\in[Y,Y+1]$ with
$|Q(x\pm iY')|\le C\log^2Y$ for $\frac13\le x\le1$.
\item[(iii)] There is an absolute constant $C$ such that $\eta\,|Q(w)|\le C\log(|\Im w|+3)$ whenever
$\Re w=\frac12+\eta$ with $0<\eta\le\frac14$.
\end{enumerate}

Lean: `Q` is any continuation `Qc` (`IsQCont`), and each bound is asserted together with the fact that the point is not
in `Σ_Q`, so that it is about genuine values (in (ii) this is the choice of `Y'`, which avoids the ordinates; the
paper's proof chooses it so). `η = Re w - 1/2`. Hypotheses RH (the paper's), (Z1), (Z2), (Z3) (the proof's). -/
theorem lem_Qleft (hRH : RiemannHypothesis) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) :
    (∀ x₀ : ℝ, 1 / 3 < x₀ → x₀ < 1 / 2 → ∃ C : ℝ, ∀ Qc : ℂ → ℂ, IsQCont Qc → ∀ y : ℝ,
      (x₀ + y * I : ℂ) ∉ PoleSetQ ∧ ‖Qc (x₀ + y * I)‖ ≤ C * Real.log (|y| + 3)) ∧
    (∃ C : ℝ, ∀ Y : ℝ, 3 ≤ Y → ∃ Y' ∈ Icc Y (Y + 1), ∀ Qc : ℂ → ℂ, IsQCont Qc →
      ∀ x ∈ Icc (1 / 3 : ℝ) 1,
        (x + Y' * I : ℂ) ∉ PoleSetQ ∧ (x - Y' * I : ℂ) ∉ PoleSetQ ∧
        ‖Qc (x + Y' * I)‖ ≤ C * Real.log Y ^ 2 ∧ ‖Qc (x - Y' * I)‖ ≤ C * Real.log Y ^ 2) ∧
    ∃ C : ℝ, ∀ Qc : ℂ → ℂ, IsQCont Qc → ∀ w : ℂ, 1 / 2 < w.re → w.re ≤ 3 / 4 →
      w ∉ PoleSetQ ∧ (w.re - 1 / 2) * ‖Qc w‖ ≤ C * Real.log (|w.im| + 3) := by
  exact M5.lem_Qleft_proof hRH hZ1 hZ2 hZ3

/-- **`cl:thm:filter` (i)** = **Theorem F (i)** (paper, verbatim):

Assume RH, and let $H$, $G$ and $D_H$ be as above.
\begin{enumerate}
\item[(i)] $D_H$ continues to a holomorphic function on $\HH$. In particular $T_0$ is holomorphic on $\HH$.
[...]
\end{enumerate}

Lean: `H ∈ ℂ[z,w]` non-zero with `H(z,w) = H(w,z)` and `H(1,w) ≡ 0` (as identities of functions, equivalent for
polynomials over `ℂ`); `G` (`H = (z-1)(w-1)G`) is not needed in the statement. The `T₀` clause is in `prop_T0`.
Hypotheses (Z1), (Z2), (Z3), (Z6). -/
theorem thm_filter_i (hRH : RiemannHypothesis) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6)
    (H : MvPolynomial (Fin 2) ℂ) (hH0 : H ≠ 0) (hHs : ∀ z w, evalH H z w = evalH H w z)
    (hH1 : ∀ w, evalH H 1 w = 0) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F HH ∧ EqOn F (DH H) (halfPlane 2) := by
  exact M5.thm_filter_i_proof hRH hZ1 hZ2 hZ3 hZ6 H hH0 hHs hH1

/-- **`cl:thm:filter` (ii)** = **Theorem F (ii)** (paper, verbatim):

\item[(ii)] Let $\tau_0$ be a real number that is neither $0$ nor the ordinate of a zero, and $s_0=1+i\tau_0$. Then
\begin{equation}\label{cl:eq:CH}
  \lim_{\eta\downarrow0}\eta\,D_H(s_0+\eta)=C_H(\tau_0):=\sum_{\substack{(\rho,\rho')\\ \rho+\rho'=s_0}}
  m(\rho)m(\rho')\,\frac{\Gamma(\rho)\Gamma(\rho')}{\Gamma(s_0)}\,H(\rho,\rho'),
\end{equation}
the sum over the ordered pairs of zeros $(\rho,\rho')$ with $\rho+\rho'=s_0$, each zero counted once as a point;
the sum converges absolutely, and is $0$ if there is no such pair.

Lean: `D_H` near the line is the holomorphic continuation `F` of (i). Absolute convergence is `Summable` of
`CHterm` (over `ℂ`, unconditional = absolute); "`0` if there is no pair" holds for the empty `tsum`. Hypotheses
(Z1), (Z2), (Z3), (Z6) (through `cl:lem:Qleft`, Stirling). -/
theorem thm_filter_ii (hRH : RiemannHypothesis) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6)
    (H : MvPolynomial (Fin 2) ℂ) (hH0 : H ≠ 0) (hHs : ∀ z w, evalH H z w = evalH H w z)
    (hH1 : ∀ w, evalH H 1 w = 0) {τ₀ : ℝ} (hτ0 : τ₀ ≠ 0) (hτ : ∀ ρ ∈ NontrivialZeros, ρ.im ≠ τ₀)
    (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F HH) (hFD : EqOn F (DH H) (halfPlane 2)) :
    Summable (CHterm H τ₀) ∧
      Tendsto (fun η : ℝ => (η : ℂ) * F (1 + τ₀ * I + η)) (𝓝[>] 0) (𝓝 (CH H τ₀)) := by
  exact M5.thm_filter_ii_proof hRH hZ1 hZ2 hZ3 hZ6 H hH0 hHs hH1 hτ0 hτ F hF hFD

/-- **`cl:thm:filter` (iii)** = **Theorem F (iii)** (paper, verbatim):

\item[(iii)] Assume also \textup{(F)}. Then for no $s_1$ with $\Re s_1=1$ and no $r>0$ is there a function
meromorphic on $\disc(s_1,r)$ that agrees with $D_H$ on $\disc(s_1,r)\cap\HH$. In particular $\sigma=1$ is a
natural boundary of $T_0$ under RH and \textup{(F)}.

Lean: for every holomorphic continuation of `D_H`, resp. of `T₀`, to `ℍ`. Hypotheses (F) (the paper's), (Z1), (Z2),
(Z3), (Z6), and Littlewood's gap theorem `ZLittlewood`, which the proof uses ("By Littlewood's theorem") and which is
not among (Z1)–(Z7); the paper lists it as (Z8). -/
theorem thm_filter_iii (hRH : RiemannHypothesis) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6)
    (hL : ZLittlewood) (hF : HypF)
    (H : MvPolynomial (Fin 2) ℂ) (hH0 : H ≠ 0) (hHs : ∀ z w, evalH H z w = evalH H w z)
    (hH1 : ∀ w, evalH H 1 w = 0) :
    (∀ F : ℂ → ℂ, DifferentiableOn ℂ F HH → EqOn F (DH H) (halfPlane 2) →
      IsNaturalBoundary F HH lineOne) ∧
    ∀ F : ℂ → ℂ, DifferentiableOn ℂ F HH → EqOn F T0 (halfPlane 2) → IsNaturalBoundary F HH lineOne := by
  exact M5.thm_filter_iii_proof hRH hZ1 hZ2 hZ3 hZ6 hL hF H hH0 hHs hH1

/-- **`cl:thm:filter` (iv)** = **Theorem F (iv)** (paper, verbatim):

\item[(iv)] Under RH alone,
\[
  \lim_{\eta\downarrow0}\eta\,T_0(1+\eta)=\frac\pi{16}+2\sum_{\gamma>0}m(\rho)^2\,|\Gamma(\rho)|^2\,|\rho-1|^2>0 .
\]
So $T_0$ has no holomorphic extension to any disc about $1$, and a function meromorphic on a disc about $1$ that
agrees with $T_0$ on the right half of the disc has a simple pole at $1$ with this residue.

Lean: `T₀` near `1` is its holomorphic continuation `F` to `ℍ`. The sum's convergence is stated (`Summable`);
`Λ₀ > 0` is proved outright (`Lambda0_pos`). Hypotheses (Z1), (Z2), (Z3), (Z6). -/
theorem thm_filter_iv (hRH : RiemannHypothesis) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6) :
    Summable lambda0Term ∧
    ∀ F : ℂ → ℂ, DifferentiableOn ℂ F HH → EqOn F T0 (halfPlane 2) →
      Tendsto (fun η : ℝ => (η : ℂ) * F (1 + η)) (𝓝[>] 0) (𝓝 (Lambda0 : ℂ)) ∧
      (∀ r : ℝ, 0 < r → ¬ ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball 1 r) ∧ EqOn g F (ball 1 r ∩ HH)) ∧
      ∀ r : ℝ, 0 < r → ∀ f : ℂ → ℂ, MeromorphicOn f (ball 1 r) →
        f =ᶠ[codiscreteWithin (ball 1 r ∩ HH)] F →
        meromorphicOrderAt f 1 = -1 ∧ HasResidue f 1 (Lambda0 : ℂ) := by
  exact M5.thm_filter_iv_proof hRH hZ1 hZ2 hZ3 hZ6

/--
**`D_H` as a double prime series** (the first remark after `cl:thm:filter`; paper, verbatim):

Three remarks. First, for $\sigma>2$ the function $D_H$ is a double prime series: writing $H$ in the basis of
rising factorials, $H(z,w)=\sum_{i,j}h_{ij}\,z^{(i)}w^{(j)}$ with $z^{(i)}=z(z+1)\cdots(z+i-1)$, the computation in the
proof of Proposition~\ref{cl:prop:T0} (the kernel of $p^iq^j(p+q)^{-s-i-j}$ is $\Gamma(z+i)\Gamma(s-z+j)/\Gamma(s+i+j)$)
gives $D_H(s)=\sum_{p,q}\log p\log q\,W_H(p,q;s)$ with
$W_H(p,q;s)=\sum_{i,j}h_{ij}\,\frac{\Gamma(s+i+j)}{\Gamma(s)}\,p^iq^j(p+q)^{-s-i-j}$, and hypothesis (R) holds for it as for
$W_0$. [...]
-/
theorem filter_series (hRH : RiemannHypothesis) (hZ6 : Z6)
    (H : MvPolynomial (Fin 2) ℂ) (hH0 : H ≠ 0) (hHs : ∀ z w, evalH H z w = evalH H w z)
    (hH1 : ∀ w, evalH H 1 w = 0) (N : ℕ) (h : ℕ → ℕ → ℂ) (hrep : IsRisingRep H N h) :
    (∀ s : ℂ, 2 < s.re →
      Summable fun pq : Nat.Primes × Nat.Primes => ‖WHlog N h s (pq.1 : ℕ) (pq.2 : ℕ)‖) ∧
    (∀ s : ℂ, 2 < s.re → DH H s = Dser (WHlog N h) s) ∧
    DifferentiableOn ℂ (Dser (WHlog N h)) (halfPlane 2) ∧
    ∀ s ∈ Aff.idL.RL ∩ Aff.idL.DL, ∀ c : ℝ, 1 < c → c < (Aff.idL.app s).re - 1 →
      Dser (WHlog N h) s = VerticalIntegral' (fun z => kH H z s * Q z * Q (Aff.idL.app s - z)) c := by
  exact M4b.filter_series_proof hRH hZ6 H hH0 hHs hH1 N h hrep

/-- **`D_H` as a double prime series, reality** (see `filter_series` for the quote).

Lean: under real coefficients of `H`, all of (R) for `k_H`, `W_H` and `Q`, including "real on `R_L ∩ ℝ`", and `D_H`
real at real `s > 2`. The paper's "(R) holds for it as for `W_0`" is stated without this restriction, and is false
for non-real coefficients (`filter_series`, section 5 of the review notes); this statement is the corrected claim.
The paper states the restriction to real coefficients. Hypotheses RH (choice 1),
(Z6). -/
theorem filter_series_real (hRH : RiemannHypothesis) (hZ6 : Z6)
    (H : MvPolynomial (Fin 2) ℂ) (hH0 : H ≠ 0) (hHs : ∀ z w, evalH H z w = evalH H w z)
    (hH1 : ∀ w, evalH H 1 w = 0) (hreal : ∀ m, (H.coeff m).im = 0) (N : ℕ) (h : ℕ → ℕ → ℂ)
    (hrep : IsRisingRep H N h) :
    HypR Aff.idL (kH H) (WHlog N h) Q ∧ ∀ x : ℝ, 2 < x → (DH H x).im = 0 := by
  exact M4b.filter_series_real_proof hRH hZ6 H hH0 hHs hH1 hreal N h hrep

/-- **`cl:lem:kernelt`** (paper, verbatim; classical, Stirling):

Let $0<x_1\le x_2<\sigma_1\le\sigma_2$. There are $C$ and $A$ such that for $w=x+iy$ with $x_1\le x\le x_2$ and $s=\sigma+it$
with $\sigma_1\le\sigma\le\sigma_2$,
\[
  |K_s(w)|\le C(1+|y|)^A(1+|t-y|)^A(1+|t|)^A\,e^{-\frac\pi2(|y|+|t-y|-|t|)} .
\]
Moreover, for every $B\ge0$ there is $C_B$ with
$\int_\R(1+|y|)^B(1+|t-y|)^Be^{-\frac\pi2(|y|+|t-y|-|t|)}dy\le C_B(1+|t|)^{2B+1}$ for all real $t$.

Lean: real exponents `A`, `B` (`Real.rpow`); `Γ(s) ≠ 0` since `σ ≥ σ₁ > 0`, so `K_s(w)` has no junk value. The integral
bound is stated with `Integrable` (a non-integrable Bochner integral is `0`). Hypotheses RH (choice 1; the proof does
not use it), (Z6) (the proof's). -/
theorem lem_kernelt (hRH : RiemannHypothesis) (hZ6 : Z6) :
    (∀ x₁ x₂ σ₁ σ₂ : ℝ, 0 < x₁ → x₁ ≤ x₂ → x₂ < σ₁ → σ₁ ≤ σ₂ → ∃ C A : ℝ,
      ∀ x ∈ Icc x₁ x₂, ∀ y : ℝ, ∀ σ ∈ Icc σ₁ σ₂, ∀ t : ℝ,
        ‖KerS (σ + t * I) (x + y * I)‖ ≤ C * (1 + |y|) ^ A * (1 + |t - y|) ^ A * (1 + |t|) ^ A *
          Real.exp (-(Real.pi / 2 * (|y| + |t - y| - |t|)))) ∧
    ∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, ∀ t : ℝ,
      Integrable (fun y : ℝ => (1 + |y|) ^ B * (1 + |t - y|) ^ B *
        Real.exp (-(Real.pi / 2 * (|y| + |t - y| - |t|)))) ∧
      ∫ y : ℝ, (1 + |y|) ^ B * (1 + |t - y|) ^ B * Real.exp (-(Real.pi / 2 * (|y| + |t - y| - |t|))) ≤
        C * (1 + |t|) ^ (2 * B + 1) := by
  exact M4a.lem_kernelt_proof hRH hZ6

/-- **`cl:thm:Tk`** (i)–(iv) (paper, verbatim):

Assume RH. For every $k\ge1$:
\begin{enumerate}
\item[(i)] $T_k$ continues to a single-valued meromorphic function on $\{\sigma>k-1\}$;
\item[(ii)] its only pole in $\{\sigma>k-\frac12\}$ is $s=k$, simple, with residue $1/(k-1)!$;
\item[(iii)] on $\{k-1<\sigma<k\}$,
\[
  T_k(s)=H_k(s)+k\,\frac{\Gamma(s-k+1)}{\Gamma(s)}\,Q(s-k+1)\qquad\text{with }H_k\text{ holomorphic there};
\]
\item[(iv)] for every compact interval $[x_1,x_2]\subset(k-\frac12,\infty)$ there are $N$, $C$ and $y_0$ with
$|T_k(x+iy)|\le C|y|^N$ for $x_1\le x\le x_2$ and $|y|\ge y_0$.
\end{enumerate}
[...]

Lean: (i), (iii), (iv) are about one continuation `F` (∃); (iii) is asserted where `s - k + 1 ∉ Σ_Q`, for every
continuation `Qc` of `Q`. (ii) holds for every meromorphic continuation. Hypotheses (Z1), (Z2), (Z3) (through
`nr:lem:growthQ`), (Z6) (through `cl:lem:kernelt`). -/
theorem thm_Tk (hRH : RiemannHypothesis) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6) (k : ℕ)
    (hk : 1 ≤ k) :
    (∃ F : ℂ → ℂ, MeromorphicOn F (halfPlane ((k : ℝ) - 1)) ∧ EqOn F (Tk k) (halfPlane k) ∧
      (∃ Hk : ℂ → ℂ, DifferentiableOn ℂ Hk {s | (k : ℝ) - 1 < s.re ∧ s.re < k} ∧
        ∀ Qc : ℂ → ℂ, IsQCont Qc → ∀ s : ℂ, (k : ℝ) - 1 < s.re → s.re < k →
          s - k + 1 ∉ PoleSetQ →
            F s = Hk s + k * (Gamma (s - k + 1) / Gamma s) * Qc (s - k + 1)) ∧
      ∀ x₁ x₂ : ℝ, (k : ℝ) - 1 / 2 < x₁ → x₁ ≤ x₂ → ∃ N C y₀ : ℝ, ∀ x ∈ Icc x₁ x₂, ∀ y : ℝ,
        y₀ ≤ |y| → ‖F (x + y * I)‖ ≤ C * |y| ^ N) ∧
    ∀ F : ℂ → ℂ, MeromorphicOn F (halfPlane ((k : ℝ) - 1)) →
      F =ᶠ[codiscreteWithin (halfPlane k)] Tk k →
      (∀ s ∈ halfPlane ((k : ℝ) - 1 / 2), s ≠ k → 0 ≤ meromorphicOrderAt F s) ∧
      meromorphicOrderAt F k = -1 ∧ HasResidue F k (1 / (k - 1).factorial) := by
  exact M5.thm_Tk_proof hRH hZ1 hZ2 hZ3 hZ6 k hk

/-- **`cl:thm:Tk`**, consequences for `k ≥ 2` (paper, verbatim):

[...] Consequently, for $k\ge2$ the poles of $T_k$ in $\{k-1<\sigma<k\}$ are exactly the points $k-1+b$, $b\in\Sigma\setminus\{1\}$,
simple, with residue
\begin{gather*}
  k\,R_b\,\frac{\Gamma(b)}{\Gamma(k-1+b)}\neq0 ,\qquad\text{that is}\\
  \frac{k\mu(j)\,\Gamma(1/j)}{j\,\Gamma(k-1+1/j)}\ \text{ at }k-1+\frac1j,\qquad
  -\frac{k\mu(n)m(\rho)\,\Gamma(\rho/n)}{n\,\Gamma(k-1+\rho/n)}\ \text{ at }k-1+\frac\rho n ;
\end{gather*}
and $\Re s=k-1$ is a natural boundary of $T_k$: for no $s_0$ with $\Re s_0=k-1$ and no $r>0$ is there a
function meromorphic on $\disc(s_0,r)$ that agrees with $T_k$ on $\disc(s_0,r)\cap\{\sigma>k-1\}$.

Lean: for every meromorphic continuation `F` of `T_k` to `σ > k - 1`. Hypotheses as for (i)–(iv). -/
theorem thm_Tk_poles (hRH : RiemannHypothesis) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6) (k : ℕ)
    (hk : 2 ≤ k) (F : ℂ → ℂ) (hF : MeromorphicOn F (halfPlane ((k : ℝ) - 1)))
    (hFT : F =ᶠ[codiscreteWithin (halfPlane k)] Tk k) :
    (∀ s : ℂ, (k : ℝ) - 1 < s.re → s.re < k →
      (meromorphicOrderAt F s < 0 ↔ s - (k - 1) ∈ PoleSetQ \ {1})) ∧
    (∀ b ∈ PoleSetQ \ {1}, meromorphicOrderAt F (k - 1 + b) = -1 ∧
      HasResidue F (k - 1 + b) (k * Rcoef b * Gamma b / Gamma (k - 1 + b)) ∧
      (k : ℂ) * Rcoef b * Gamma b / Gamma (k - 1 + b) ≠ 0) ∧
    (∀ j : ℕ, 2 ≤ j → Squarefree j →
      HasResidue F (k - 1 + 1 / (j : ℂ))
        (k * mu j * Gamma (1 / (j : ℂ)) / (j * Gamma (k - 1 + 1 / (j : ℂ))))) ∧
    (∀ n : ℕ, 1 ≤ n → Squarefree n → ∀ ρ ∈ NontrivialZeros,
      HasResidue F (k - 1 + ρ / (n : ℂ))
        (-(k * mu n * (zetaMult ρ : ℂ) * Gamma (ρ / (n : ℂ))) / (n * Gamma (k - 1 + ρ / (n : ℂ))))) ∧
    IsNaturalBoundary F (halfPlane ((k : ℝ) - 1)) {s | s.re = (k : ℝ) - 1} := by
  exact M5.thm_Tk_poles_proof hRH hZ1 hZ2 hZ3 hZ6 k hk F hF hFT

/-! ## 5. The introduction's Theorems A, C, D, F, assembled from their parts

Theorem B (`intro:thm:B`) is `thm_boundary`, Theorem E (`intro:thm:E`) is `thm_mero_i`, `thm_mero_ii`, `thm_mero_iii`,
and Theorem G (`intro:thm:G`) is `thm_Tk` with `thm_Tk_poles`: the same statements, not repeated. -/

/-- **`intro:thm:A`** (paper, verbatim):

\textup{(i)} $T$ continues to a single-valued meromorphic function on the half-plane
$\{\sigma>2B_\infty\}$, real on the real axis. Its poles there are simple and lie in $\Pi$.

\textup{(ii)} For $\Re s_0>2B_\infty$ the set of ordered pairs $(a,b)\in\Sigma_Q\times\Sigma_Q$ with
$a+b=s_0$ is finite, and
\[
  \Res_{s=s_0}T=\sum_{\substack{(a,b)\in\Sigma_Q^2\\ a+b=s_0}}R_aR_b\,\frac{\Gamma(a)\Gamma(b)}{\Gamma(s_0)},
\]
the pair $(a,a)$, if present, counted once. In particular $s_0$ is a regular point of $T$ when
$s_0\notin\Pi$.

Lean: (i) is the first part of `thm_cont`, (ii) is `thm_residue`; proved from them. -/
theorem intro_thm_A (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6) :
    (∃ F : ℂ → ℂ, MeromorphicOn F (halfPlane (2 * Binf)) ∧ EqOn F T (halfPlane 2) ∧
      AnalyticOnNhd ℂ F (halfPlane (2 * Binf) \ Pinch) ∧
      (∀ s ∈ halfPlane (2 * Binf), -1 ≤ meromorphicOrderAt F s) ∧
      (∀ s ∈ halfPlane (2 * Binf) \ Pinch, F (conj s) = conj (F s))) ∧
    ∀ s₀ : ℂ, 2 * Binf < s₀.re → (pinchPairs s₀).Finite ∧
      ∀ F : ℂ → ℂ, MeromorphicOn F (halfPlane (2 * Binf)) →
        F =ᶠ[codiscreteWithin (halfPlane 2)] T →
        HasResidue F s₀ (pairSum s₀) ∧ (s₀ ∉ Pinch → 0 ≤ meromorphicOrderAt F s₀) := by
  obtain ⟨F, h1, h2, h3, h4, h5, -⟩ := thm_cont hZ1 hZ2 hZ3 hZ6
  exact ⟨⟨F, h1, h2, h3, h4, h5⟩, fun s₀ hs₀ => thm_residue hZ1 hZ2 hZ3 hZ6 hs₀⟩

/-- **`intro:thm:C`** (paper, verbatim):

\textup{(a)} Assume RH. Then the poles of $T$ on the real interval $(1,2)$ are exactly the points
$1+1/k$, $k\ge2$ squarefree, with residue $2\mu(k)$.

\textup{(b)} Suppose $B>B_\infty$ \textup{(}for instance, $\zeta$ has at least one, but only finitely
many, zeros off the critical line\textup{)}. Then $\frac12<B<1$, $B$ is attained by finitely many
zeros, $T$ is meromorphic on $\{\sigma>2B_\infty\}\ni2B$, and
\begin{gather*}
  \Res_{s=2B}T=A+\begin{cases}2\mu(k)&\text{if }2B=1+1/k\text{ for an integer }k\ge2,\\ 0&\text{otherwise,}\end{cases}\\
  A=\frac1{\Gamma(2B)}\sum_{\rho:\ \beta=B}m(\rho)^2|\Gamma(\rho)|^2 ,
\end{gather*}
the sum over the distinct zeros with $\beta=B$ in both half-planes, with $0<A<0.073$. So the residue
is never $0$ and differs from the value that \textup{(a)} assigns to the point $2B$ under RH.

\textup{(c)} With no hypothesis on the zeros: RH holds if and only if there are an open set $U\supset(1,2]$ and a
function meromorphic on $U$ that agrees with $T$ on $U\cap\{\sigma>2\}$ and whose poles on $(1,2)$ are exactly the
points $1+1/k$, $k\ge2$ squarefree, each simple with residue $2\mu(k)$.

Lean: (a) is `thm_real_a` (whose meromorphy clause on `ℍ` is part of `nr:thm:real`(a)), (b) is `thm_real_b` (its
last sentence is `thm_real_b_values`), (c) is `thm_test`; proved from them. In (c), as in `thm_test`, `RH` is
Mathlib's `RiemannHypothesis`; the `←` direction needs the argument that every zero that is not trivial lies in
`0 < β < 1`. -/
theorem intro_thm_C (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6) (hZ7 : Z7) :
    (RiemannHypothesis →
      (∃ F : ℂ → ℂ, MeromorphicOn F HH ∧ EqOn F T (halfPlane 2)) ∧
      ∀ F : ℂ → ℂ, MeromorphicOn F HH → F =ᶠ[codiscreteWithin (halfPlane 2)] T →
        (∀ x : ℝ, x ∈ Ioo (1 : ℝ) 2 →
          (meromorphicOrderAt F x < 0 ↔ ∃ k : ℕ, 2 ≤ k ∧ Squarefree k ∧ (x : ℂ) = 1 + 1 / (k : ℂ))) ∧
        ∀ k : ℕ, 2 ≤ k → Squarefree k → HasResidue F (1 + 1 / (k : ℂ)) (2 * mu k)) ∧
    (Binf < Bsup →
      1 / 2 < Bsup ∧ Bsup < 1 ∧ {ρ | ρ ∈ NontrivialZeros ∧ ρ.re = Bsup}.Finite ∧
      {ρ | ρ ∈ NontrivialZeros ∧ ρ.re = Bsup}.Nonempty ∧
      (∃ F : ℂ → ℂ, MeromorphicOn F (halfPlane (2 * Binf)) ∧ EqOn F T (halfPlane 2)) ∧
      2 * Binf < 2 * Bsup ∧ 0 < Aconst ∧ Aconst < 0.073 ∧
      ∀ F : ℂ → ℂ, MeromorphicOn F (halfPlane (2 * Binf)) → F =ᶠ[codiscreteWithin (halfPlane 2)] T →
        (∀ k : ℕ, 2 ≤ k → 2 * Bsup = 1 + 1 / (k : ℝ) →
          HasResidue F ((2 * Bsup : ℝ) : ℂ) (Aconst + 2 * mu k)) ∧
        ((∀ k : ℕ, 2 ≤ k → 2 * Bsup ≠ 1 + 1 / (k : ℝ)) → HasResidue F ((2 * Bsup : ℝ) : ℂ) Aconst)) ∧
    (RiemannHypothesis ↔
      ∃ U : Set ℂ, IsOpen U ∧ (∀ x : ℝ, x ∈ Ioc (1 : ℝ) 2 → (x : ℂ) ∈ U) ∧
        ∃ Tt : ℂ → ℂ, MeromorphicOn Tt U ∧ EqOn Tt T (U ∩ halfPlane 2) ∧
          (∀ x : ℝ, x ∈ Ioo (1 : ℝ) 2 →
            (meromorphicOrderAt Tt x < 0 ↔ ∃ k : ℕ, 2 ≤ k ∧ Squarefree k ∧ (x : ℂ) = 1 + 1 / (k : ℂ))) ∧
          ∀ k : ℕ, 2 ≤ k → Squarefree k →
            meromorphicOrderAt Tt (1 + 1 / (k : ℂ)) = -1 ∧ HasResidue Tt (1 + 1 / (k : ℂ)) (2 * mu k)) :=
  ⟨fun hRH => thm_real_a hRH hZ1 hZ2 hZ3 hZ6, fun h => thm_real_b hZ1 hZ2 hZ3 hZ6 hZ7 h,
    thm_test hZ1 hZ2 hZ3 hZ6⟩

/-- **`intro:thm:D`** (paper, verbatim):

Assume RH, the hypotheses \textup{(K1)}, \textup{(K2)}, \textup{(K3)}, \textup{(R)} and \textup{(H2-log)}
of Section~\ref{cl:sec:setting}, and \textup{(H3)}: every point of the line $\Re L(s)=1$ is a limit of
scaled-zero pinches $\alpha$ with $X_\alpha\not\equiv0$. Then near every pinch $\alpha$ in $D_L$ every branch of
$D$ has the form $X_\alpha(s)\log(s-\alpha)+(\text{holomorphic})$, with the same $X_\alpha$ for every branch, and
no branch extends meromorphically to any disc centred on a point of the line $\Re L(s)=1$.
Hypothesis \textup{(H3)} is used for the last assertion only; the local form, with its independence of
the branch, holds under RH, \textup{(K1)}--\textup{(K3)}, \textup{(R)} and \textup{(H2-log)}.
Hypothesis \textup{(H3)} holds under \textup{(K4)} when $\mathfrak b\not\equiv0$.

Lean: the local form of `thm_class_i`, then `thm_class_ii` under (H3), then `thm_class_H3_of_K4`; proved from them.
(A LaTeX `%` comment line between the second and third sentences of the source is omitted from the quote.) -/
theorem intro_thm_D (hRH : RiemannHypothesis) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (A : Aff)
    (k : ℂ → ℂ → ℂ) (W : ℂ → ℕ → ℕ → ℂ) (hK1 : K1 A k) (hK2 : K2 A k) (hK3 : K3 A k)
    (hR : HypR A k W P) (hH2 : H2log A k) :
    (∀ α ∈ catalogueL A ∩ A.DL, ∃ r : ℝ, 0 < r ∧
      ∀ s₁ ∈ slitDiscL α r, ∀ g : ℂ → ℂ,
        IsAdmissibleGermOn (Dser W) (A.HL \ catalogueL A) A.RL g s₁ →
        ∃ H : ℂ → ℂ, DifferentiableOn ℂ H (ball α r) ∧
          g =ᶠ[𝓝 s₁] fun s => Xcoef A k α s * Complex.log (s - α) + H s) ∧
    (H3 A k → ∀ (g : ℂ → ℂ) (s₁ : ℂ), IsAdmissibleGermOn (Dser W) (A.HL \ catalogueL A) A.RL g s₁ →
      ∀ s₀ ∈ A.lineL, ∀ r : ℝ, 0 < r → s₁ ∈ ball s₀ r →
        ¬ GermExtendsMeromorphically g s₁ (ball s₀ r)) ∧
    (K4 k → (∃ s ∈ A.DL, bracket A k s ≠ 0) → H3 A k) :=
  ⟨(thm_class_i hRH hZ1 hZ2 hZ3 A k W hK1 hK2 hK3 hR hH2).2,
    fun hH3 => thm_class_ii hRH hZ1 hZ2 hZ3 A k W hK1 hK2 hK3 hR hH2 hH3,
    fun hK4 hb => thm_class_H3_of_K4 hRH hZ1 A k hK1 hK4 hb⟩

/-- **`intro:thm:F`** (paper, verbatim):

Assume RH. \textup{(i)} $D_H$ continues to a holomorphic function on $\HH$. \textup{(ii)} If $\tau_0\in\R$ is
neither $0$ nor the ordinate of a zero and $s_0=1+i\tau_0$, then
\[
  \lim_{\eta\downarrow0}\eta\,D_H(s_0+\eta)=\sum_{\rho+\rho'=s_0}m(\rho)m(\rho')\,\frac{\Gamma(\rho)\Gamma(\rho')}{\Gamma(s_0)}\,H(\rho,\rho'),
\]
the absolutely convergent sum over the ordered pairs of zeros with $\rho+\rho'=s_0$. \textup{(iii)} If also
\textup{(F)} holds, then no function meromorphic on a disc centred on the line $\sigma=1$ agrees with $D_H$ on the
part of the disc in $\HH$; in particular $\sigma=1$ is a natural boundary of $T_0$ under RH and \textup{(F)}.
\textup{(iv)} Under RH alone, $\eta\,T_0(1+\eta)\to\frac\pi{16}+2\sum_{\gamma>0}m(\rho)^2|\Gamma(\rho)|^2|\rho-1|^2>0$ as
$\eta\downarrow0$, so $s=1$ is a singular point of $T_0$.

Lean: `thm_filter_i` to `thm_filter_iv`; Littlewood's theorem (`ZLittlewood`) is a premise of (iii) only. -/
theorem intro_thm_F (hRH : RiemannHypothesis) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6)
    (H : MvPolynomial (Fin 2) ℂ) (hH0 : H ≠ 0) (hHs : ∀ z w, evalH H z w = evalH H w z)
    (hH1 : ∀ w, evalH H 1 w = 0) :
    (∃ F : ℂ → ℂ, DifferentiableOn ℂ F HH ∧ EqOn F (DH H) (halfPlane 2)) ∧
    (∀ τ₀ : ℝ, τ₀ ≠ 0 → (∀ ρ ∈ NontrivialZeros, ρ.im ≠ τ₀) →
      ∀ F : ℂ → ℂ, DifferentiableOn ℂ F HH → EqOn F (DH H) (halfPlane 2) →
        Summable (CHterm H τ₀) ∧
          Tendsto (fun η : ℝ => (η : ℂ) * F (1 + τ₀ * I + η)) (𝓝[>] 0) (𝓝 (CH H τ₀))) ∧
    (ZLittlewood → HypF →
      (∀ F : ℂ → ℂ, DifferentiableOn ℂ F HH → EqOn F (DH H) (halfPlane 2) →
        IsNaturalBoundary F HH lineOne) ∧
      ∀ F : ℂ → ℂ, DifferentiableOn ℂ F HH → EqOn F T0 (halfPlane 2) →
        IsNaturalBoundary F HH lineOne) ∧
    (Summable lambda0Term ∧
      ∀ F : ℂ → ℂ, DifferentiableOn ℂ F HH → EqOn F T0 (halfPlane 2) →
        Tendsto (fun η : ℝ => (η : ℂ) * F (1 + η)) (𝓝[>] 0) (𝓝 (Lambda0 : ℂ)) ∧
        (∀ r : ℝ, 0 < r → ¬ ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball 1 r) ∧ EqOn g F (ball 1 r ∩ HH)) ∧
        ∀ r : ℝ, 0 < r → ∀ f : ℂ → ℂ, MeromorphicOn f (ball 1 r) →
          f =ᶠ[codiscreteWithin (ball 1 r ∩ HH)] F →
          meromorphicOrderAt f 1 = -1 ∧ HasResidue f 1 (Lambda0 : ℂ)) :=
  ⟨thm_filter_i hRH hZ1 hZ2 hZ3 hZ6 H hH0 hHs hH1,
    fun _ hτ0 hτ F hF hFD => thm_filter_ii hRH hZ1 hZ2 hZ3 hZ6 H hH0 hHs hH1 hτ0 hτ F hF hFD,
    fun hL hF => thm_filter_iii hRH hZ1 hZ2 hZ3 hZ6 hL hF H hH0 hHs hH1,
    thm_filter_iv hRH hZ1 hZ2 hZ3 hZ6⟩

end GoldbachBoundaries.Paper2
