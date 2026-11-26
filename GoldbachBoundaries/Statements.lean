import GoldbachBoundaries.Defs
import GoldbachBoundaries.ZetaRealNonvanishing
import GoldbachBoundaries.SigmaFinite
import GoldbachBoundaries.SigmaMeromorphic
import GoldbachBoundaries.TIdentity.Assembly
import GoldbachBoundaries.Density
import GoldbachBoundaries.TBoundary
import GoldbachBoundaries.ThmA.Skeleton

/-!
Each main result of the paper is stated here as a Lean `theorem`, under the
paper's statement quoted verbatim (LaTeX source, with its label). `RiemannHypothesis` (Mathlib's
`def`) is an explicit premise wherever the paper assumes RH. There are no `axiom`s. The statements were signed off
with `sorry` proofs (2026-10-18); each is now closed by `exact` from a proof file elsewhere in the
library, with the statement unchanged, and none uses `sorry`.

Reading guide for the reviewer:

* Section 1: sanity lemmas, with real proofs where short. They check that the definitions mean
  what they should (multiplicities are `≥ 1`, RH puts zeros on the line, `𝒞 ⊆ ℍ`, `𝒞 = 1 + Σ`)
  and that the hypotheses of the main statements can be met (an admissible germ exists).
* Section 2: `lem:Sigma` (i), (ii), (iv), `lem:density`.
* Section 3: Theorem B and its parts `thm:T-identity`, `cor:T-poles`, `thm:T-boundary`.
  `thm_B` is assembled from the parts by a real (one-line) proof.
* Section 4: Theorem A and its parts (sentences 1–2, `thm:local` for every branch,
  `thm:G-boundary` and its strong form `thm_A_no_extension`, `rem:every-path`), plus `lem:slant`,
  `cor:domain` and the path-concatenation lemma. `thm_A` is assembled from the parts by a real
  (one-line) proof.
-/

noncomputable section

open Complex Filter Topology Set Metric

namespace GoldbachBoundaries

/-! ## 1. Sanity lemmas -/

/-- `ζ` is analytic away from `1`. -/
lemma analyticAt_riemannZeta {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ riemannZeta s := by
  have hd : DifferentiableOn ℂ riemannZeta ({1} : Set ℂ)ᶜ :=
    fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt
  exact hd.analyticAt (isOpen_compl_singleton.mem_nhds hs)

lemma ne_one_of_mem_nontrivialZeros {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) : ρ ≠ 1 := by
  rintro rfl
  simp [NontrivialZeros] at hρ

lemma ne_zero_of_mem_nontrivialZeros {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) : ρ ≠ 0 := by
  rintro rfl
  simp [NontrivialZeros] at hρ

/-- Sanity: `m(ρ) ≥ 1` at every non-trivial zero (so `zetaMult` is the multiplicity, not a junk
`0`). -/
theorem one_le_zetaMult {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) : 1 ≤ zetaMult ρ := by
  have hne1 := ne_one_of_mem_nontrivialZeros hρ
  have han := analyticAt_riemannZeta hne1
  have hzero : riemannZeta ρ = 0 := hρ.1
  -- ζ is not identically zero near ρ (identity theorem on the connected set `{1}ᶜ`)
  have hcd : riemannZeta ⁻¹' {0}ᶜ ∈ codiscreteWithin ({1} : Set ℂ)ᶜ := by
    refine AnalyticOnNhd.preimage_zero_mem_codiscreteWithin (x := 2)
      (fun z hz => analyticAt_riemannZeta hz) ?_ ?_ ?_
    · exact riemannZeta_ne_zero_of_one_le_re (by norm_num)
    · norm_num
    · exact isConnected_compl_singleton_of_one_lt_rank (by simp) 1
  have hev : ∀ᶠ z in 𝓝[≠] ρ, riemannZeta z ≠ 0 := by
    have hdisj := (mem_codiscreteWithin.mp hcd) ρ hne1
    have h1 : (({1} : Set ℂ)ᶜ \ riemannZeta ⁻¹' {0}ᶜ)ᶜ ∈ 𝓝[≠] ρ :=
      Filter.disjoint_principal_right.mp hdisj
    have h2 : ∀ᶠ z in 𝓝[≠] ρ, z ∈ ({1} : Set ℂ)ᶜ :=
      nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds hne1)
    filter_upwards [h1, h2] with z hz1 hz2 hz3
    exact hz1 ⟨hz2, by simpa using hz3⟩
  have hntop : meromorphicOrderAt riemannZeta ρ ≠ ⊤ :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero han.meromorphicAt).2 hev
  have hA0 : analyticOrderAt riemannZeta ρ ≠ 0 := fun h => (han.analyticOrderAt_eq_zero.mp h) hzero
  unfold zetaMult
  rw [han.meromorphicOrderAt_eq] at hntop ⊢
  cases hO : analyticOrderAt riemannZeta ρ with
  | top => simp [hO] at hntop
  | coe n =>
    have hn : n ≠ 0 := fun h => hA0 (by simp [hO, h])
    rw [ENat.map_natCast, WithTop.untopD_coe]
    simp only [Int.toNat_natCast]
    omega

/-- Sanity: in Mathlib's formulation of RH (all zeros other than `-2(n+1)` and `s = 1` have real
part `1/2`), every zero of `ζ` with positive real part lies on the critical line. -/
theorem re_eq_half_of_RH (hRH : RiemannHypothesis) {ρ : ℂ} (hz : riemannZeta ρ = 0)
    (hre : 0 < ρ.re) : ρ.re = 1 / 2 := by
  refine hRH ρ hz ?_ ?_
  · rintro ⟨n, rfl⟩
    have : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
    rw [this] at hre
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  · rintro rfl
    exact riemannZeta_one_ne_zero hz

/-- Sanity: under RH every non-trivial zero has real part `1/2`. -/
theorem re_eq_half_of_mem_nontrivialZeros (hRH : RiemannHypothesis) {ρ : ℂ}
    (hρ : ρ ∈ NontrivialZeros) : ρ.re = 1 / 2 :=
  re_eq_half_of_RH hRH hρ.1 hρ.2.1

/-- Sanity: `𝒞 ⊆ ℍ`, unconditionally (`Re(1 + ρ/n) = 1 + Re ρ / n > 1`). -/
theorem catalogue_subset_HH : catalogue ⊆ HH := by
  intro s hs
  simp only [HH, halfPlane, mem_ofPred_eq]
  rcases hs with (hs | ⟨k, hk, -, rfl⟩) | ⟨n, hn, -, ρ, hρ, rfl⟩
  · rw [mem_singleton_iff.mp hs]; norm_num
  · have hk' : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have : (1 + 1 / (k : ℂ)).re = 1 + 1 / (k : ℝ) := by
      simp [Complex.normSq_natCast]
    rw [this]
    have : 0 < 1 / (k : ℝ) := by positivity
    linarith
  · have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have : (1 + ρ / (n : ℂ)).re = 1 + ρ.re / n := by simp [Complex.div_natCast_re]
    rw [this]
    have : 0 < ρ.re / n := div_pos hρ.2.1 hn'
    linarith

/-- Sanity (`lem:catalogue`, the *second* equality `{1 + a : a ∈ Σ} = 𝒞`): `𝒞 = 1 + Σ`,
unconditionally. The first equality, `{a + b : a, b ∈ Σ} ∩ ℍ = {1 + a : a ∈ Σ}`, uses RH and is
not stated here. -/
theorem catalogue_eq_image : catalogue = (fun a => 1 + a) '' PoleSetQ := by
  ext s
  simp only [catalogue, PoleSetQ, mem_union, mem_singleton_iff, mem_ofPred_eq, mem_image]
  constructor
  · rintro ((rfl | ⟨k, hk, hsf, rfl⟩) | ⟨n, hn, hsf, ρ, hρ, rfl⟩)
    · exact ⟨1, Or.inl (Or.inl rfl), by norm_num⟩
    · exact ⟨1 / k, Or.inl (Or.inr ⟨k, hk, hsf, rfl⟩), rfl⟩
    · exact ⟨ρ / n, Or.inr ⟨n, hn, hsf, ρ, hρ, rfl⟩, rfl⟩
  · rintro ⟨a, ((rfl | ⟨k, hk, hsf, rfl⟩) | ⟨n, hn, hsf, ρ, hρ, rfl⟩), rfl⟩
    · exact Or.inl (Or.inl (by norm_num))
    · exact Or.inl (Or.inr ⟨k, hk, hsf, rfl⟩)
    · exact Or.inr ⟨n, hn, hsf, ρ, hρ, rfl⟩

/-- `G` is holomorphic on every half-plane `σ > a`, `a > 2` (absolute convergence). -/
theorem G_differentiableOn {a : ℝ} (ha : 2 < a) : DifferentiableOn ℂ G (halfPlane a) := by
  set b : ℝ := a / 2 with hb
  have hb1 : 1 < b := by rw [hb]; linarith
  have hS : Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-b)) :=
    (Real.summable_nat_rpow.2 (by linarith)).subtype _
  have hnn : 0 ≤ (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-b)) :=
    fun p => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hS2 := hS.mul_of_nonneg hS hnn hnn
  refine differentiableOn_tsum_of_summable_norm hS2 ?_ (isOpen_halfPlane a) ?_
  · intro pq w _
    have hpos : (((pq.1 : ℕ) + (pq.2 : ℕ) : ℕ) : ℂ) ≠ 0 := by
      have := pq.1.2.pos; exact_mod_cast (by omega)
    exact ((differentiableAt_id.neg).const_cpow (Or.inl hpos)).differentiableWithinAt
  · intro pq w hw
    have hp : 0 < (pq.1 : ℕ) := pq.1.2.pos
    have hq : 0 < (pq.2 : ℕ) := pq.2.2.pos
    rw [norm_natCast_cpow_of_pos (by omega)]
    simp only [neg_re]
    have hw' : a < w.re := hw
    set n : ℝ := (((pq.1 : ℕ) + (pq.2 : ℕ) : ℕ) : ℝ) with hn
    have hn1 : 1 ≤ n := by rw [hn]; exact_mod_cast (by omega)
    have hpn : ((pq.1 : ℕ) : ℝ) ≤ n := by rw [hn]; exact_mod_cast (by omega)
    have hqn : ((pq.2 : ℕ) : ℝ) ≤ n := by rw [hn]; exact_mod_cast (by omega)
    calc n ^ (-w.re) ≤ n ^ (-a) := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
      _ = n ^ (-b) * n ^ (-b) := by
          rw [← Real.rpow_add (by linarith)]; congr 1; rw [hb]; ring
      _ ≤ ((pq.1 : ℕ) : ℝ) ^ (-b) * ((pq.2 : ℕ) : ℝ) ^ (-b) := by
          apply mul_le_mul
          · exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hp) hpn (by linarith)
          · exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hq) hqn (by linarith)
          · exact Real.rpow_nonneg (by linarith) _
          · exact Real.rpow_nonneg (Nat.cast_nonneg _) _

theorem G_analyticAt {s : ℂ} (hs : 2 < s.re) : AnalyticAt ℂ G s := by
  have ha : 2 < (s.re + 2) / 2 := by linarith
  refine (G_differentiableOn ha).analyticAt ((isOpen_halfPlane _).mem_nhds ?_)
  show (s.re + 2) / 2 < s.re
  linarith

lemma three_notMem_catalogue : (3 : ℂ) ∉ catalogue := by
  rintro ((h | ⟨k, hk, -, h⟩) | ⟨n, hn, -, ρ, hρ, h⟩)
  · norm_num at h
  · -- 3 = 1 + 1/k forces 1/k = 2, impossible for k ≥ 2
    have hre := congrArg Complex.re h
    have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
    have : (1 + 1 / (k : ℂ)).re = 1 + 1 / (k : ℝ) := by
      simp [Complex.normSq_natCast]
    rw [this] at hre
    norm_num at hre
    have : 1 / (k : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hk'
    have : (k : ℝ)⁻¹ ≤ 1 / 2 := by simpa using this
    linarith
  · -- 3 = 1 + ρ/n forces Re ρ = 2n ≥ 2, outside the critical strip
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.div_natCast_re] at hre
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hρre : ρ.re = 2 * n := by
      have : ρ.re / n = 2 := by norm_num at hre; linarith
      field_simp at this; linarith
    have := hρ.2.2
    linarith

/-- Sanity (non-vacuity of `IsAdmissibleGerm`, the hypothesis of `thm:G-boundary` and
`cor:domain`): `G` itself, at `s₁ = 3`, is an admissible germ (constant path). -/
theorem exists_admissibleGerm : IsAdmissibleGerm G 3 := by
  refine ⟨ContinuousMap.const _ (3 : ℂ), fun _ => ⟨?_, three_notMem_catalogue⟩, ?_, rfl, ?_⟩
  · show (1 : ℝ) < (3 : ℂ).re; norm_num
  · show (2 : ℝ) < (3 : ℂ).re; norm_num
  · refine ⟨fun _ => G, ⟨fun _ => G_analyticAt ?_, fun _ => Eventually.of_forall
      (fun _ => EventuallyEq.rfl)⟩, EventuallyEq.rfl, EventuallyEq.rfl⟩
    show (2 : ℝ) < (3 : ℂ).re; norm_num

/-! Uniqueness of the representation of a catalogue point (used by
`exists_hasCatalogueValues`). -/

lemma catalogue_two_ne_one_add_inv {k : ℕ} (hk : 2 ≤ k) : (1 + 1 / (k : ℂ)) ≠ 2 := by
  intro h
  have hre := congrArg Complex.re h
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have : (1 + 1 / (k : ℂ)).re = 1 + 1 / (k : ℝ) := by simp [Complex.normSq_natCast]
  rw [this] at hre
  norm_num at hre
  have : (k : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hk'
  linarith

lemma catalogue_inv_inj {k k' : ℕ} (hk : 2 ≤ k) (hk' : 2 ≤ k')
    (h : (1 + 1 / (k : ℂ)) = 1 + 1 / (k' : ℂ)) : k = k' := by
  have h1 := add_left_cancel h
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hk0' : (k' : ℂ) ≠ 0 := by exact_mod_cast (by omega : k' ≠ 0)
  rw [one_div, one_div, inv_inj] at h1
  exact_mod_cast h1

lemma catalogue_zero_ne_two {n : ℕ} (hn : 1 ≤ n) {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) :
    1 + ρ / (n : ℂ) ≠ 2 := by
  intro h
  have hre := congrArg Complex.re h
  simp only [Complex.add_re, Complex.one_re, Complex.div_natCast_re] at hre
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hρre : ρ.re = n := by
    have : ρ.re / n = 1 := by norm_num at hre; linarith
    field_simp at this; linarith
  linarith [hρ.2.2]

lemma catalogue_zero_ne_inv (hRH : RiemannHypothesis) {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) : 1 + ρ / (n : ℂ) ≠ 1 + 1 / (k : ℂ) := by
  intro h
  have h1 := add_left_cancel h
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hρeq : ρ = (n : ℂ) / k := by
    field_simp at h1; field_simp; linear_combination h1
  have him : ρ.im = 0 := by rw [hρeq]; simp [Complex.div_natCast_im]
  have hre : ρ.re = 1 / 2 := re_eq_half_of_mem_nontrivialZeros hRH hρ
  have : ρ = 1 / 2 := Complex.ext (by simp [hre]) (by simp [him])
  exact riemannZeta_one_half_ne_zero (this ▸ hρ.1)

lemma catalogue_zero_inj (hRH : RiemannHypothesis) {n n' : ℕ} (hn : 1 ≤ n) (hn' : 1 ≤ n')
    {ρ ρ' : ℂ} (hρ : ρ ∈ NontrivialZeros) (hρ' : ρ' ∈ NontrivialZeros)
    (h : 1 + ρ / (n : ℂ) = 1 + ρ' / (n' : ℂ)) : n = n' ∧ ρ = ρ' := by
  have h1 := add_left_cancel h
  have hre := congrArg Complex.re h1
  simp only [Complex.div_natCast_re, re_eq_half_of_mem_nontrivialZeros hRH hρ,
    re_eq_half_of_mem_nontrivialZeros hRH hρ'] at hre
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hnr' : (0 : ℝ) < n' := by exact_mod_cast hn'
  have hnn : (n : ℝ) = n' := by field_simp at hre; linarith
  have hnn' : n = n' := by exact_mod_cast hnn
  subst hnn'
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  exact ⟨rfl, by simpa [div_left_inj' hn0] using h1⟩

/-- Sanity (non-vacuity of `HasCatalogueValues`): under RH there is a function with the
catalogue values, i.e. the three clauses never assign two different numbers to one point.
This needs the uniqueness of the representation of a catalogue point: `1 + 1/k` determines `k`;
`1 + ρ/n` is never `2` (real parts); under RH `1 + ρ/n = 1 + ρ'/n'` forces `n = n'` and `ρ = ρ'`
(real parts `1 + 1/(2n)`); and `1 + ρ/n = 1 + 1/k` would make `ρ` real, so `ρ = 1/2` under RH,
which `ζ(1/2) ≠ 0` (`riemannZeta_one_half_ne_zero`, `ZetaRealNonvanishing.lean`) excludes. -/
theorem exists_hasCatalogueValues (hRH : RiemannHypothesis) : ∃ v, HasCatalogueValues v := by
  classical
  let v : ℂ → ℂ := fun s =>
    if s = 2 then 1
    else if h : ∃ k : ℕ, 2 ≤ k ∧ s = 1 + 1 / (k : ℂ) then 2 * mu h.choose
    else if h : ∃ q : ℕ × ℂ, 1 ≤ q.1 ∧ q.2 ∈ NontrivialZeros ∧ s = 1 + q.2 / (q.1 : ℂ) then
      -(2 * mu h.choose.1 * (zetaMult h.choose.2 : ℂ)) / h.choose.2
    else 0
  refine ⟨v, ?_, ?_, ?_⟩
  · simp [v]
  · intro k hk _
    have hex : ∃ k' : ℕ, 2 ≤ k' ∧ 1 + 1 / (k : ℂ) = 1 + 1 / (k' : ℂ) := ⟨k, hk, rfl⟩
    have hch : hex.choose = k :=
      (catalogue_inv_inj hk hex.choose_spec.1 hex.choose_spec.2).symm
    simp only [v, catalogue_two_ne_one_add_inv hk, hex, ↓reduceIte, ↓reduceDIte, hch]
  · intro n hn _ ρ hρ
    have hno : ¬ ∃ k : ℕ, 2 ≤ k ∧ 1 + ρ / (n : ℂ) = 1 + 1 / (k : ℂ) := by
      rintro ⟨k, hk, h⟩
      exact catalogue_zero_ne_inv hRH hn hk hρ h
    have hex : ∃ q : ℕ × ℂ, 1 ≤ q.1 ∧ q.2 ∈ NontrivialZeros ∧
        1 + ρ / (n : ℂ) = 1 + q.2 / (q.1 : ℂ) := ⟨(n, ρ), hn, hρ, rfl⟩
    obtain ⟨h1, h2⟩ := catalogue_zero_inj hRH hn hex.choose_spec.1 hρ hex.choose_spec.2.1
      hex.choose_spec.2.2
    simp only [v, catalogue_zero_ne_two hn hρ, hno, hex, ↓reduceIte, ↓reduceDIte, ← h1, ← h2]

/-! ## 2. Preliminaries: `lem:Sigma`, `lem:density` -/

/-- **`lem:Sigma` (i), (ii)** (paper, verbatim):

Assume RH.
\begin{enumerate}
\item[(i)] $Q$ is single-valued meromorphic on $\{\Re z>0\}$; its poles are exactly the points of
$\Sigma$, all simple.
\item[(ii)] Write $\Res_aQ=-\lambda_a$. Then $\lambda_1=-1$, $\lambda_{1/k}=-\mu(k)/k$,
$\lambda_{\rho/n}=\mu(n)m(\rho)/n$, and every $\lambda_a\neq0$.
[...]
\end{enumerate}

Lean: some `Qc` meromorphic on `Re z > 0`, equal to the series `Q` on `Re z > 1`, analytic off
`Σ`, with a simple pole at every point of `Σ`, and residues as in (ii) (via `HasSigmaResidues`,
which records `Res_a Q = -λ_a`). -/
theorem lem_Sigma_i_ii (hRH : RiemannHypothesis) :
    ∃ Qc : ℂ → ℂ, MeromorphicOn Qc (halfPlane 0) ∧ EqOn Qc Q (halfPlane 1) ∧
      AnalyticOnNhd ℂ Qc (halfPlane 0 \ PoleSetQ) ∧
      (∀ a ∈ PoleSetQ, meromorphicOrderAt Qc a = -1) ∧
      ∃ res : ℂ → ℂ, (∀ a ∈ PoleSetQ, HasResidue Qc a (res a)) ∧ HasSigmaResidues res ∧
        ∀ a ∈ PoleSetQ, res a ≠ 0 :=
  lem_Sigma_i_ii_proof hRH

/-- **`lem:Sigma` (iv)** (paper, verbatim):

Assume RH. [...] \item[(iv)] $\Sigma\cap\{\Re z>\frac12\}=\{1\}$, and $\Sigma$ is locally finite in
$\{\Re z>0\}$.

Lean: local finiteness as "every point of `Re z > 0` has a neighbourhood meeting `Σ` in a finite
set". -/
theorem lem_Sigma_iv (hRH : RiemannHypothesis) :
    PoleSetQ ∩ halfPlane (1 / 2) = {1} ∧
      ∀ z ∈ halfPlane 0, ∃ U ∈ 𝓝 z, (U ∩ PoleSetQ).Finite :=
  lem_Sigma_iv_proof hRH

/-- **`lem:density`** (paper, verbatim; unconditional):

For every $y\in\R$ and $\varepsilon>0$ there are infinitely many pairs \textup{(}prime $n$, zero
$\rho$\textup{)} with $|\rho/n-iy|<\varepsilon$.

Lean: "zero" is a non-trivial zero (the paper's standing convention for `ρ`); the pairs form an
infinite subset of `ℕ × ℂ`. No RH premise, as in the paper. -/
theorem lem_density (y : ℝ) {ε : ℝ} (hε : 0 < ε) :
    {np : ℕ × ℂ | np.1.Prime ∧ np.2 ∈ NontrivialZeros ∧
      ‖np.2 / (np.1 : ℂ) - (y : ℂ) * I‖ < ε}.Infinite :=
  lem_density_proof y hε

/-! ## 3. Theorem B (the weighted series `T`) -/

/-- **`thm:T-identity`** (paper, verbatim):

Assume RH and let $b\in(\frac12,1)$. There is a function $H_b$, holomorphic on $\sigma>2b$, with
\[
  T(s)=\frac{2Q(s-1)}{s-1}-\frac1{\Gamma(s)(s-2)}+H_b(s).
\]
$H_b$ does not depend on $b$, so it is holomorphic on $\HH$.

Lean: the final claim (one `H`, holomorphic on `ℍ`). The identity is asserted only on `σ > 2`,
where `T(s)` and `Q(s-1)` are the convergent series; on the rest of `ℍ` it is the paper's
definition of the continuation of `T` (with `Q` continued by `lem:Sigma`), and holds there by the
identity theorem. The per-`b` form follows (`thm_T_identity_b`). -/
theorem thm_T_identity (hRH : RiemannHypothesis) :
    ∃ H : ℂ → ℂ, DifferentiableOn ℂ H HH ∧
      ∀ s : ℂ, 2 < s.re →
        T s = 2 * Q (s - 1) / (s - 1) - 1 / (Complex.Gamma s * (s - 2)) + H s := by
  exact thm_T_identity_proof hRH

/-- The per-`b` form of `thm:T-identity`, derived from the `ℍ` form (real proof). -/
theorem thm_T_identity_b (hRH : RiemannHypothesis) {b : ℝ} (hb : b ∈ Ioo (1 / 2 : ℝ) 1) :
    ∃ H : ℂ → ℂ, DifferentiableOn ℂ H (halfPlane (2 * b)) ∧
      ∀ s : ℂ, 2 < s.re →
        T s = 2 * Q (s - 1) / (s - 1) - 1 / (Complex.Gamma s * (s - 2)) + H s := by
  obtain ⟨H, hH, hid⟩ := thm_T_identity hRH
  refine ⟨H, hH.mono fun s hs => ?_, hid⟩
  have : 2 * b < s.re := hs
  show (1 : ℝ) < s.re
  linarith [hb.1]

/-- **`cor:T-poles`** (paper, verbatim):

Assume RH. Then $T$ is single-valued meromorphic on $\HH$. Its poles there are exactly the points
of $\cat$, all simple, with
\[
  \Res_{s=2}T=1,\qquad \Res_{s=1+1/k}T=2\mu(k),\qquad \Res_{s=1+\rho/n}T=-\frac{2\mu(n)m(\rho)}{\rho},
\]
all non-zero.

Lean: some `F` meromorphic on `ℍ`, equal to the series `T` on `σ > 2`, analytic on `ℍ ∖ 𝒞`,
of order exactly `-1` at every point of `𝒞`, whose residues have the catalogue values and are
non-zero. (Any two such `F` agree off a discrete set, since `ℍ` is connected, so orders and
residues do not depend on the choice.) -/
theorem cor_T_poles (hRH : RiemannHypothesis) :
    ∃ F : ℂ → ℂ, MeromorphicOn F HH ∧ EqOn F T (halfPlane 2) ∧
      AnalyticOnNhd ℂ F (HH \ catalogue) ∧
      (∀ α ∈ catalogue, meromorphicOrderAt F α = -1) ∧
      ∃ res : ℂ → ℂ, (∀ α ∈ catalogue, HasResidue F α (res α)) ∧ HasCatalogueValues res ∧
        ∀ α ∈ catalogue, res α ≠ 0 := by
  exact cor_T_poles_proof hRH

/-- **`thm:T-boundary`** (paper, verbatim):

Assume RH. For no $y\in\R$ and $r>0$ is there a meromorphic function $f$ on
$\disc=\disc(1+iy,r)$ with $f=T$ on $\disc\cap\HH$.

Lean: "T on `Δ ∩ ℍ`" is the meromorphic continuation, so the statement is made for *every* `F`
meromorphic on `ℍ` that agrees with the series `T` on `σ > 2` off a discrete set (such `F` exist
by `cor_T_poles`, so this is not vacuous). "f = T on `Δ ∩ ℍ`" is equality off a discrete subset
of `Δ ∩ ℍ`. -/
theorem thm_T_boundary (hRH : RiemannHypothesis) (F : ℂ → ℂ) (hF : MeromorphicOn F HH)
    (hFT : F =ᶠ[codiscreteWithin (halfPlane 2)] T) :
    IsNaturalBoundary F HH lineOne :=
  thm_T_boundary_of_density hRH (fun y _ hε => lem_density y hε) F hF hFT

/-- **`thm:B`** (paper, verbatim):

Assume RH. Then
\[
  T(s)=\frac{2\,Q(s-1)}{s-1}-\frac{1}{\Gamma(s)(s-2)}+H(s)
\]
with $H$ holomorphic on $\HH$. Hence $T$ is meromorphic on $\HH$ with simple poles exactly at the
points of $\cat$, with residues $1$ at $2$, $2\mu(k)$ at $1+1/k$, and $-2\mu(n)m(\rho)/\rho$ at
$1+\rho/n$; and $\sigma=1$ is a natural boundary of $T$.

Lean: the conjunction of `thm_T_identity`, `cor_T_poles` and `thm_T_boundary` (see those for the
encoding); proved from them. -/
theorem thm_B (hRH : RiemannHypothesis) :
    (∃ H : ℂ → ℂ, DifferentiableOn ℂ H HH ∧
      ∀ s : ℂ, 2 < s.re →
        T s = 2 * Q (s - 1) / (s - 1) - 1 / (Complex.Gamma s * (s - 2)) + H s) ∧
    (∃ F : ℂ → ℂ, MeromorphicOn F HH ∧ EqOn F T (halfPlane 2) ∧
      AnalyticOnNhd ℂ F (HH \ catalogue) ∧
      (∀ α ∈ catalogue, meromorphicOrderAt F α = -1) ∧
      ∃ res : ℂ → ℂ, (∀ α ∈ catalogue, HasResidue F α (res α)) ∧ HasCatalogueValues res ∧
        ∀ α ∈ catalogue, res α ≠ 0) ∧
    (∀ F : ℂ → ℂ, MeromorphicOn F HH → F =ᶠ[codiscreteWithin (halfPlane 2)] T →
      IsNaturalBoundary F HH lineOne) :=
  ⟨thm_T_identity hRH, cor_T_poles hRH, thm_T_boundary hRH⟩

/-! ## 4. Theorem A (the unweighted series `G`) -/

/-- `κ` is an admissible slope in the sense of `lem:slant`: `κ ∈ (-1,1) ∖ {0}` and, with
`v = 1 + iκ`, no two distinct points of `𝒞` differ by a real multiple of `v`. -/
def IsGoodSlant (κ : ℝ) : Prop :=
  κ ≠ 0 ∧ |κ| < 1 ∧
    ∀ α ∈ catalogue, ∀ α' ∈ catalogue, α ≠ α' → ∀ t : ℝ, α - α' ≠ (t : ℂ) * slantDir κ

/-- **`lem:slant`** (paper, verbatim):

Assume RH. There is $\kappa\in(-1,1)\setminus\{0\}$ such that, with $v=1+i\kappa$, no two distinct
points of $\cat$ differ by a real multiple of $v$.

Stated so that the `∀ κ, IsGoodSlant κ → …` in `thm_A_local` is not vacuous. -/
theorem lem_slant (hRH : RiemannHypothesis) : ∃ κ : ℝ, IsGoodSlant κ := by
  exact ThmA.lem_slant_proof hRH

/-- **`thm:A`, sentences 1–2** (paper, verbatim):

Assume RH. The series $G$ continues analytically along every path in $\HH\setminus\cat$ that
starts in $\sigma>2$.

(The same claim, for paths $\omega:[0,1]\to\HH\setminus\cat$ with $\omega(0)$ in $\sigma>2$, is the
first claim of `prop:branches`.)

Lean: paths are continuous maps `[0,1] → ℂ`; continuation is `ContinuesAlong` (germ chains,
`Defs.lean`). -/
theorem thm_A_continuation (hRH : RiemannHypothesis) :
    ∀ γ : C(unitInterval, ℂ), (∀ t, γ t ∈ HH \ catalogue) → 2 < (γ 0).re →
      ContinuesAlong G γ := by
  exact ThmA.thm_A_continuation_proof hRH

/-- **Concatenation of continuations** (not a paper statement; used silently in
`thm:G-boundary` step 2, `cor:domain` and `rem:every-path`). If `g` is a terminal germ of `F`
along `γ₁` and `g'` a terminal germ of `g` along `γ₂`, where `γ₂` starts at the end of `γ₁`, then
`g'` is a terminal germ of `F` along a path `γ` from `γ₁ 0` to `γ₂ 1` whose points all lie on
`γ₁` or `γ₂` (the concatenation). Pure complex analysis, no RH. -/
theorem isTerminalGerm_trans {F g g' : ℂ → ℂ} {γ₁ γ₂ : C(unitInterval, ℂ)}
    (h₁ : IsTerminalGerm F γ₁ g) (h₁₂ : γ₂ 0 = γ₁ 1) (h₂ : IsTerminalGerm g γ₂ g') :
    ∃ γ : C(unitInterval, ℂ), γ 0 = γ₁ 0 ∧ γ 1 = γ₂ 1 ∧
      (∀ t, γ t ∈ range γ₁ ∪ range γ₂) ∧ IsTerminalGerm F γ g' := by
  exact ThmA.isTerminalGerm_trans_proof h₁ h₁₂ h₂

/-- The continuation of an admissible germ along a path in `ℍ ∖ 𝒞` is again admissible.
Proved from `isTerminalGerm_trans`; no RH. -/
theorem admissible_continuation {g g' : ℂ → ℂ} {s₁ : ℂ} (hg : IsAdmissibleGerm g s₁)
    (γ : C(unitInterval, ℂ)) (hγ0 : γ 0 = s₁) (hγ : ∀ t, γ t ∈ HH \ catalogue)
    (hg' : IsTerminalGerm g γ g') : IsAdmissibleGerm g' (γ 1) := by
  obtain ⟨γ₁, hγ₁, h2, h1, hterm⟩ := hg
  obtain ⟨δ, hδ0, hδ1, hδr, hδ⟩ := isTerminalGerm_trans hterm (hγ0.trans h1.symm) hg'
  refine ⟨δ, fun t => ?_, by rw [hδ0]; exact h2, hδ1, hδ⟩
  rcases hδr t with ⟨u, hu⟩ | ⟨u, hu⟩
  · rw [← hu]; exact hγ₁ u
  · rw [← hu]; exact hγ u

/-- **`thm:A`, local form of every branch** (paper, verbatim; `thm:local` is the same claim for
the principal sheet):

Near each $\alpha\in\cat$ every branch has the form
$X_\alpha(s)\log(s-\alpha)+(\text{holomorphic})$ on a slit disc about $\alpha$, with $X_\alpha$
holomorphic on $\HH$, $X_\alpha(\alpha)=0$ and
\begin{gather*}
  X_2'(2)=1,\qquad X'_{1+1/k}(1+1/k)=2\mu(k),\\
  X'_{1+\rho/n}(1+\rho/n)=-\frac{2\mu(n)m(\rho)}{\rho}\neq0 .
\end{gather*}

Lean: a family `X α`, chosen before any slope (the paper's `X_α = 2λ₁λ_a J_{1a}` does not depend
on `κ`), with `X α` holomorphic on `ℍ`, `X α α = 0`, and `X'_α(α)` having the catalogue values,
all non-zero (the paper writes `≠ 0` only for the third family; for the first two it is immediate
since `μ(k) ≠ 0` for squarefree `k`). Then for *every* admissible slope `κ` (the paper fixes an
arbitrary one, l.609; non-vacuous by `lem_slant`) and every `α ∈ 𝒞` there is `r > 0` such that
every branch `g` at every point `s₁` of the slit disc `Δ(α, r) ∖ cut_α` agrees near `s₁` with
`X α · Log((s - α)/v) + h`, `v = 1 + iκ`, for some `h` holomorphic on the whole disc (`h` depends on
the branch; `r` depends on `κ` and `α`, not on the branch). The branch of `log(s - α)` is the
paper's `Log_α`; other branches differ by constants, absorbed into `h`. -/
theorem thm_A_local (hRH : RiemannHypothesis) :
    ∃ X : ℂ → ℂ → ℂ,
      (∀ α ∈ catalogue, DifferentiableOn ℂ (X α) HH ∧ X α α = 0) ∧
      HasCatalogueValues (fun α => deriv (X α) α) ∧
      (∀ α ∈ catalogue, deriv (X α) α ≠ 0) ∧
      ∀ κ : ℝ, IsGoodSlant κ → ∀ α ∈ catalogue, ∃ r : ℝ, 0 < r ∧
        ∀ s₁ ∈ slitDisc (slantDir κ) α r, ∀ g : ℂ → ℂ, IsAdmissibleGerm g s₁ →
          ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (ball α r) ∧
            g =ᶠ[𝓝 s₁] fun s => X α s * logAt (slantDir κ) α s + h s := by
  exact ThmA.thm_A_local_proof hRH

/-- **`thm:G-boundary`** (paper, verbatim):

Assume RH. Let $g$ be an admissible germ at $s_1\in\HH$. For no $y\in\R$ and $r>0$ with
$s_1\in\disc:=\disc(1+iy,r)$ is there a meromorphic function $f$ on $\disc$ whose germ at $s_1$ is
$g$.

Lean: "germ of `f` at `s₁` is `g`" is `f =ᶠ[𝓝[≠] s₁] g` (`GermExtendsMeromorphically`); this is
equivalent to `=ᶠ[𝓝 s₁]` and does not read `f s₁`. -/
theorem thm_G_boundary (hRH : RiemannHypothesis) {g : ℂ → ℂ} {s₁ : ℂ}
    (hg : IsAdmissibleGerm g s₁) (y r : ℝ) (hr : 0 < r) (hs₁ : s₁ ∈ ball (1 + (y : ℂ) * I) r) :
    ¬ GermExtendsMeromorphically g s₁ (ball (1 + (y : ℂ) * I) r) := by
  exact ThmA.thm_G_boundary_proof hRH hg y r hr hs₁

/-- **`rem:every-path`** (paper, verbatim, first sentence and conclusion):

Every germ obtained from $G$ by continuation along \emph{any} path in $\C$ is admissible. [...]
So the Riemann surface of $G$ lies over $\HH\setminus\cat$, [...]

and the last clause of **`thm:A`**: $G$ cannot be continued analytically along any path in $\C$
that leaves $\HH\setminus\cat$.

Lean: a path that starts in `σ > 2` and along which `G` continues stays in `ℍ ∖ 𝒞`. Then every
germ so obtained is admissible by definition (`rem_every_path_admissible`). -/
theorem rem_every_path (hRH : RiemannHypothesis) :
    ∀ γ : C(unitInterval, ℂ), 2 < (γ 0).re → ContinuesAlong G γ → ∀ t, γ t ∈ HH \ catalogue := by
  exact ThmA.rem_every_path_proof hRH

/-- `rem:every-path`, first sentence, as stated: every terminal germ of `G` along any path in `ℂ`
starting in `σ > 2` is admissible. Derived from `rem_every_path` (real proof). -/
theorem rem_every_path_admissible (hRH : RiemannHypothesis) (γ : C(unitInterval, ℂ))
    (h0 : 2 < (γ 0).re) {g : ℂ → ℂ} (hg : IsTerminalGerm G γ g) : IsAdmissibleGerm g (γ 1) := by
  obtain ⟨f, hf, hf0, hg1⟩ := hg
  exact ⟨γ, rem_every_path hRH γ h0 ⟨f, hf, hf0⟩, h0, rfl, f, hf, hf0, hg1⟩

/-- The continuation of an admissible germ along *any* path in `ℂ` is again admissible.
Proved from `isTerminalGerm_trans` and `rem_every_path`. -/
theorem admissible_continuation_any_path (hRH : RiemannHypothesis) {g g' : ℂ → ℂ} {s₁ : ℂ}
    (hg : IsAdmissibleGerm g s₁) (γ : C(unitInterval, ℂ)) (hγ0 : γ 0 = s₁)
    (hg' : IsTerminalGerm g γ g') : IsAdmissibleGerm g' (γ 1) := by
  obtain ⟨γ₁, -, h2, h1, hterm⟩ := hg
  obtain ⟨δ, hδ0, hδ1, -, hδ⟩ := isTerminalGerm_trans hterm (hγ0.trans h1.symm) hg'
  have h2' : 2 < (δ 0).re := by rw [hδ0]; exact h2
  have := rem_every_path_admissible hRH δ h2' hδ
  rwa [hδ1] at this

/-- **`thm:A`, "no branch extends meromorphically to any disc centred on a point of the line"**,
in the paper's strong reading (l.156; l.164: "no germ of $G$, reached along any path, extends
meromorphically to a disc centred on the line"): the branch `g` at `s₁` need not lie in the disc;
continue it along any path `γ` in `ℂ` from `s₁` to a point `γ 1` of the disc, and the germ reached
there does not extend meromorphically to the disc. Proved from `admissible_continuation_any_path`
and `thm_G_boundary`; with the constant path it gives back `thm_G_boundary`. -/
theorem thm_A_no_extension (hRH : RiemannHypothesis) {g : ℂ → ℂ} {s₁ : ℂ}
    (hg : IsAdmissibleGerm g s₁) (γ : C(unitInterval, ℂ)) (g' : ℂ → ℂ) (hγ0 : γ 0 = s₁)
    (hg' : IsTerminalGerm g γ g') (y r : ℝ) (hr : 0 < r) (hγ1 : γ 1 ∈ ball (1 + (y : ℂ) * I) r) :
    ¬ GermExtendsMeromorphically g' (γ 1) (ball (1 + (y : ℂ) * I) r) :=
  thm_G_boundary hRH (admissible_continuation_any_path hRH hg γ hγ0 hg') y r hr hγ1

/-- **`cor:domain`** (paper, verbatim):

Assume RH. Let $g$ be an admissible germ at $s_1$. If $W\subset\C$ is open, connected, meets the
line $\sigma=1$ and contains $s_1$, no meromorphic function on $W$ has germ $g$ at $s_1$. -/
theorem cor_domain (hRH : RiemannHypothesis) {g : ℂ → ℂ} {s₁ : ℂ} (hg : IsAdmissibleGerm g s₁)
    {W : Set ℂ} (hWo : IsOpen W) (hWc : IsConnected W) (hWL : (W ∩ lineOne).Nonempty)
    (hs₁ : s₁ ∈ W) : ¬ GermExtendsMeromorphically g s₁ W := by
  exact ThmA.cor_domain_proof hRH hg hWo hWc hWL hs₁

/-- **`thm:A`** (paper, verbatim):

Assume RH. The series $G$ continues analytically along every path in $\HH\setminus\cat$ that
starts in $\sigma>2$. Near each $\alpha\in\cat$ every branch has the form
$X_\alpha(s)\log(s-\alpha)+(\text{holomorphic})$ on a slit disc about $\alpha$, with $X_\alpha$
holomorphic on $\HH$, $X_\alpha(\alpha)=0$ and
\begin{gather*}
  X_2'(2)=1,\qquad X'_{1+1/k}(1+1/k)=2\mu(k),\\
  X'_{1+\rho/n}(1+\rho/n)=-\frac{2\mu(n)m(\rho)}{\rho}\neq0 .
\end{gather*}
No branch of $G$ extends meromorphically to any disc centred on a point of the line $\sigma=1$, and
$G$ cannot be continued analytically along any path in $\C$ that leaves $\HH\setminus\cat$.

Lean: the conjunction of `thm_A_continuation`, `thm_A_local`, `thm_A_no_extension` (the strong
reading of the third sentence: branches continued along any path into the disc) and
`rem_every_path`; proved from them. -/
theorem thm_A (hRH : RiemannHypothesis) :
    (∀ γ : C(unitInterval, ℂ), (∀ t, γ t ∈ HH \ catalogue) → 2 < (γ 0).re →
      ContinuesAlong G γ) ∧
    (∃ X : ℂ → ℂ → ℂ,
      (∀ α ∈ catalogue, DifferentiableOn ℂ (X α) HH ∧ X α α = 0) ∧
      HasCatalogueValues (fun α => deriv (X α) α) ∧
      (∀ α ∈ catalogue, deriv (X α) α ≠ 0) ∧
      ∀ κ : ℝ, IsGoodSlant κ → ∀ α ∈ catalogue, ∃ r : ℝ, 0 < r ∧
        ∀ s₁ ∈ slitDisc (slantDir κ) α r, ∀ g : ℂ → ℂ, IsAdmissibleGerm g s₁ →
          ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (ball α r) ∧
            g =ᶠ[𝓝 s₁] fun s => X α s * logAt (slantDir κ) α s + h s) ∧
    (∀ (g : ℂ → ℂ) (s₁ : ℂ), IsAdmissibleGerm g s₁ →
      ∀ (γ : C(unitInterval, ℂ)) (g' : ℂ → ℂ), γ 0 = s₁ → IsTerminalGerm g γ g' →
        ∀ y r : ℝ, 0 < r → γ 1 ∈ ball (1 + (y : ℂ) * I) r →
          ¬ GermExtendsMeromorphically g' (γ 1) (ball (1 + (y : ℂ) * I) r)) ∧
    (∀ γ : C(unitInterval, ℂ), 2 < (γ 0).re → ContinuesAlong G γ → ∀ t, γ t ∈ HH \ catalogue) :=
  ⟨thm_A_continuation hRH, thm_A_local hRH,
    fun _ _ hg γ g' h0 hg' y r hr h1 => thm_A_no_extension hRH hg γ g' h0 hg' y r hr h1,
    rem_every_path hRH⟩

end GoldbachBoundaries
