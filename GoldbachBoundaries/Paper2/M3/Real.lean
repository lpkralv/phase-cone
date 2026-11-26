import GoldbachBoundaries.Paper2.M3.AConst
import GoldbachBoundaries.Paper2.M3.Fill.pairSum_two_Bsup
import GoldbachBoundaries.Paper2.M3.Fill.pinchPairs_two_Bsup
import GoldbachBoundaries.Paper2.M3.Fill.real_mem_catalogue_iff

/-!
# M3: the real poles of `T` (`nr:thm:real`, `nr:cor:1+u` under RH, `nr:prop:dichotomy`(ii))

**Under RH** (`cor_one_add_RH`, `thm_real_a`) the route is paper 1's, not the paper's: `cor_T_poles` (paper 1) gives a
meromorphic `F₀` on `ℍ`, equal to the series on `σ > 2`, analytic off the catalogue `𝒞`, with a simple pole and the
catalogue residue at every point of `𝒞`; any `F` as in the statements equals `F₀` near every point of `ℍ` (paper 1's
`eventuallyEq_nhdsNE_of_agree_halfPlane_two`). The real points of `𝒞` in `(1, 2)` are the `1 + 1/k`
(`real_mem_catalogue_iff`; the `1 + ρ/n` are not real because `ζ` has no zero in `(0, 1)`). So neither needs M1, and
(Z1), (Z2), (Z3), (Z6) are not used.

**Without RH** (`thm_real_b`): M1's `Tcont` is meromorphic on `σ > 2B_∞`, and `Res_{2B} F = 𝓡(2B)` for every admissible
`F` (`hasResidue_Tcont`, `eventuallyEq_Tcont_of_codiscrete`). The pairs `(a, b) ∈ Σ_Q²` with `a + b = 2B` are the
`(ρ, ρ̄)` with `β = B` and, when `2B = 1 + 1/k` with `k` squarefree, `(1, 1/k)`, `(1/k, 1)` (`pinchPairs_two_Bsup`);
`R_ρ = R_{ρ̄} = -m(ρ)` (`Rcoef_of_half_le_re`, (Z1) for `m(ρ̄) = m(ρ)`), so `𝓡(2B) = A + [2B = 1 + 1/k] 2μ(k)`
(`pairSum_two_Bsup`). `rem_dichotomy_ii`: under `(H_∞)` `B_∞ = 1/2` (M2's `Binf_eq_half_of_Hinf`), and if RH fails
`B > 1/2` (`half_lt_Bsup_of_not_RH`), so `thm_real_b` applies and the residue `A + 2μ(k)` or `A` is not `0`.

The targets are at the end of the file (`Test.lean` uses `thm_real_a_proof`).
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M3

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1 GoldbachBoundaries.Paper2.M2

/-! ## Real lemmas -/

/-- The identity theorem on a half-plane `σ > a`, `a ≤ 2` (paper 1's `eventuallyEq_nhdsNE_of_agree_halfPlane_two`,
with a general half-plane and a general function `G` in place of `T`). -/
theorem eventuallyEq_nhdsNE_of_codiscrete_halfPlane {a : ℝ} (ha : a ≤ 2) {F F₀ G : ℂ → ℂ}
    (hF : MeromorphicOn F (halfPlane a)) (hF₀ : MeromorphicOn F₀ (halfPlane a)) (hF₀G : EqOn F₀ G (halfPlane 2))
    (hFG : F =ᶠ[codiscreteWithin (halfPlane 2)] G) {z : ℂ} (hz : z ∈ halfPlane a) :
    F =ᶠ[𝓝[≠] z] F₀ := by
  have h3 : (3 : ℂ) ∈ halfPlane 2 := by norm_num [halfPlane]
  have h3a : (3 : ℂ) ∈ halfPlane a := by
    show a < (3 : ℂ).re
    norm_num
    linarith
  have hn3 : halfPlane 2 ∈ 𝓝 (3 : ℂ) := (isOpen_halfPlane 2).mem_nhds h3
  have hFG3 : F =ᶠ[𝓝[≠] (3 : ℂ)] G :=
    eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin hFG hn3
  have hF₀G3 : F₀ =ᶠ[𝓝[≠] (3 : ℂ)] G :=
    Filter.mem_of_superset (nhdsWithin_le_nhds hn3) fun s hs => hF₀G hs
  have htop3 : meromorphicOrderAt (F - F₀) 3 = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    filter_upwards [hFG3, hF₀G3] with s h1 h2
    simp [h1, h2]
  have htop : meromorphicOrderAt (F - F₀) z = ⊤ :=
    (hF.sub hF₀).meromorphicOrderAt_eq_top_of_isPreconnected (isPreconnected_halfPlane a) h3a hz htop3
  rw [meromorphicOrderAt_eq_top_iff] at htop
  filter_upwards [htop] with s hs
  exact sub_eq_zero.mp hs

/-- `A + 2μ(k) ≠ 0` for `0 < A < 0.073` (the arithmetic of `thm_real_b_values` in `Paper2/Statements.lean`). -/
lemma Aconst_add_two_mu_ne_zero {A : ℝ} (hA0 : 0 < A) (hA1 : A < 0.073) (k : ℕ) :
    (A : ℂ) + 2 * mu k ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  have hcases : (ArithmeticFunction.moebius k : ℤ) = -1 ∨ (ArithmeticFunction.moebius k : ℤ) = 0 ∨
      (ArithmeticFunction.moebius k : ℤ) = 1 := by
    have := ArithmeticFunction.abs_moebius_le_one (n := k)
    rw [abs_le] at this
    omega
  rcases hcases with h' | h' | h' <;> simp [mu, h'] at hre <;> linarith

/-! ## Target: `cor_one_add_RH` -/

/-- `cor_one_add_RH` of `Paper2/Statements.lean`, statement verbatim. -/
theorem cor_one_add_RH_proof (hRH : RiemannHypothesis) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6)
    (F : ℂ → ℂ) (hF : MeromorphicOn F HH) (hFT : F =ᶠ[codiscreteWithin (halfPlane 2)] T) :
    ∃ res : ℂ → ℂ, HasCatalogueValues res ∧ ∀ α ∈ catalogue, HasResidue F α (res α) := by
  have _ : Z1 ∧ Z2 ∧ Z3 ∧ Z6 := ⟨hZ1, hZ2, hZ3, hZ6⟩  -- not needed on paper 1's route (`cor_T_poles`)
  obtain ⟨F₀, hF₀m, hF₀T, -, -, res, hres, hval, -⟩ := cor_T_poles hRH
  refine ⟨res, hval, fun α hα => (hres α hα).congr ?_⟩
  exact (eventuallyEq_nhdsNE_of_agree_halfPlane_two hF hF₀m hF₀T hFT (catalogue_subset_HH hα)).symm

/-! ## Target: `thm_real_a` -/

/-- `thm_real_a` of `Paper2/Statements.lean`, statement verbatim. -/
theorem thm_real_a_proof (hRH : RiemannHypothesis) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6) :
    (∃ F : ℂ → ℂ, MeromorphicOn F HH ∧ EqOn F T (halfPlane 2)) ∧
    ∀ F : ℂ → ℂ, MeromorphicOn F HH → F =ᶠ[codiscreteWithin (halfPlane 2)] T →
      (∀ x : ℝ, x ∈ Ioo (1 : ℝ) 2 →
        (meromorphicOrderAt F x < 0 ↔ ∃ k : ℕ, 2 ≤ k ∧ Squarefree k ∧ (x : ℂ) = 1 + 1 / (k : ℂ))) ∧
      ∀ k : ℕ, 2 ≤ k → Squarefree k → HasResidue F (1 + 1 / (k : ℂ)) (2 * mu k) := by
  have _ : Z1 ∧ Z2 ∧ Z3 ∧ Z6 := ⟨hZ1, hZ2, hZ3, hZ6⟩  -- not needed on paper 1's route (`cor_T_poles`)
  obtain ⟨F₀, hF₀m, hF₀T, hF₀a, hF₀o, res, hres, hval, -⟩ := cor_T_poles hRH
  refine ⟨⟨F₀, hF₀m, hF₀T⟩, fun F hF hFT => ⟨fun x hx => ?_, fun k hk hsq => ?_⟩⟩
  · have hxH : (x : ℂ) ∈ HH := by
      show (1 : ℝ) < (x : ℂ).re
      simpa using hx.1
    rw [meromorphicOrderAt_congr (eventuallyEq_nhdsNE_of_agree_halfPlane_two hF hF₀m hF₀T hFT hxH),
      ← real_mem_catalogue_iff hx]
    constructor
    · intro hneg
      by_contra hc
      exact absurd (hF₀a _ ⟨hxH, hc⟩).meromorphicOrderAt_nonneg (not_le.mpr hneg)
    · intro hc
      rw [hF₀o _ hc]
      decide
  · have hα : (1 + 1 / (k : ℂ)) ∈ catalogue := Or.inl (Or.inr ⟨k, hk, hsq, rfl⟩)
    have := (hres _ hα).congr
      (eventuallyEq_nhdsNE_of_agree_halfPlane_two hF hF₀m hF₀T hFT (catalogue_subset_HH hα)).symm
    rwa [hval.2.1 k hk hsq] at this

/-! ## Target: `thm_real_b` -/

/-- `thm_real_b` of `Paper2/Statements.lean`, statement verbatim. -/
theorem thm_real_b_proof (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6) (hZ7 : Z7) (h : Binf < Bsup) :
    1 / 2 < Bsup ∧ Bsup < 1 ∧ {ρ | ρ ∈ NontrivialZeros ∧ ρ.re = Bsup}.Finite ∧
    {ρ | ρ ∈ NontrivialZeros ∧ ρ.re = Bsup}.Nonempty ∧
    (∃ F : ℂ → ℂ, MeromorphicOn F (halfPlane (2 * Binf)) ∧ EqOn F T (halfPlane 2)) ∧
    2 * Binf < 2 * Bsup ∧ 0 < Aconst ∧ Aconst < 0.073 ∧
    ∀ F : ℂ → ℂ, MeromorphicOn F (halfPlane (2 * Binf)) → F =ᶠ[codiscreteWithin (halfPlane 2)] T →
      (∀ k : ℕ, 2 ≤ k → 2 * Bsup = 1 + 1 / (k : ℝ) →
        HasResidue F ((2 * Bsup : ℝ) : ℂ) (Aconst + 2 * mu k)) ∧
      ((∀ k : ℕ, 2 ≤ k → 2 * Bsup ≠ 1 + 1 / (k : ℝ)) → HasResidue F ((2 * Bsup : ℝ) : ℂ) Aconst) := by
  have _ := hZ6  -- (Z6) is not needed on the M1 route (polynomial Gamma decay)
  obtain ⟨hB1, hB2, hfin, hne⟩ := lem_B_iv_proof hZ1 h
  obtain ⟨ρ, hρ, hre⟩ := hne
  obtain ⟨hA0, hAle, -, hA2⟩ := lem_A_proof hZ7 hB1 hB2 ⟨ρ, hρ, hre⟩
  obtain ⟨hmero, -, -⟩ := Tcont_props hZ1 hZ2 hZ3
  have hs₀ : 2 * Binf < ((2 * Bsup : ℝ) : ℂ).re := by
    rw [ofReal_re]
    linarith
  have hT := hasResidue_Tcont hZ1 hZ2 hZ3 hs₀
  obtain ⟨hp1, hp2⟩ := pairSum_two_Bsup hZ1 h
  refine ⟨hB1, hB2, hfin, ⟨ρ, hρ, hre⟩, ⟨Tcont, hmero, Tcont_eqOn_T hZ1 hZ2 hZ3⟩, by linarith, hA0,
    by linarith, fun F hF hFT => ?_⟩
  have hev := eventuallyEq_Tcont_of_codiscrete hZ1 hZ2 hZ3 hF hFT hs₀
  refine ⟨fun k hk hkB => ?_, fun hk => ?_⟩
  · have := hT.congr hev.symm
    rwa [hp1 k hk hkB] at this
  · have := hT.congr hev.symm
    rwa [hp2 hk] at this

/-! ## Target: `rem_dichotomy_ii` -/

/-- `rem_dichotomy_ii` of `Paper2/Statements.lean`, statement verbatim. -/
theorem rem_dichotomy_ii_proof (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6) (hZ7 : Z7) (hH : Hinf)
    (hRH : ¬ RiemannHypothesis) :
    (∃ F : ℂ → ℂ, MeromorphicOn F HH ∧ EqOn F T (halfPlane 2)) ∧ 1 < 2 * Bsup ∧
      ∀ F : ℂ → ℂ, MeromorphicOn F HH → F =ᶠ[codiscreteWithin (halfPlane 2)] T →
        meromorphicOrderAt F ((2 * Bsup : ℝ) : ℂ) < 0 := by
  have hBinf : Binf = 1 / 2 := Binf_eq_half_of_Hinf hZ1 hH
  have hHH : halfPlane (2 * Binf) = HH := by
    rw [hBinf]
    norm_num
  have hB : 1 / 2 < Bsup := half_lt_Bsup_of_not_RH hZ1 hRH
  have h : Binf < Bsup := by
    rw [hBinf]
    exact hB
  obtain ⟨-, -, -, -, ⟨F₀, hF₀m, hF₀T⟩, -, hA0, hA1, hres⟩ := thm_real_b_proof hZ1 hZ2 hZ3 hZ6 hZ7 h
  refine ⟨⟨F₀, by rw [← hHH]; exact hF₀m, hF₀T⟩, by linarith, fun F hF hFT => ?_⟩
  have hF' : MeromorphicOn F (halfPlane (2 * Binf)) := by
    rw [hHH]
    exact hF
  obtain ⟨hr1, hr2⟩ := hres F hF' hFT
  have hmem : ((2 * Bsup : ℝ) : ℂ) ∈ HH := by
    show (1 : ℝ) < ((2 * Bsup : ℝ) : ℂ).re
    rw [ofReal_re]
    linarith
  by_cases hk : ∃ k : ℕ, 2 ≤ k ∧ 2 * Bsup = 1 + 1 / (k : ℝ)
  · obtain ⟨k, hk2, hkB⟩ := hk
    rw [(hr1 k hk2 hkB).meromorphicOrderAt_eq_neg_one (hF _ hmem) (Aconst_add_two_mu_ne_zero hA0 hA1 k)]
    decide
  · push Not at hk
    have hne : (Aconst : ℂ) ≠ 0 := by exact_mod_cast hA0.ne'
    rw [(hr2 hk).meromorphicOrderAt_eq_neg_one (hF _ hmem) hne]
    decide

end GoldbachBoundaries.Paper2.M3
