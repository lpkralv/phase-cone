import GoldbachBoundaries.Paper2.M4a.Skeleton
import GoldbachBoundaries.Paper2.M3.Skeleton

/-!
# Paper 2, Milestone M4b (Theorem E and the hypothesis checks of Section 4): definitions and small facts

Everything in this file has a real proof.

## Objects

* `primeSum ω z = ∑_p ω(p) p^{-z}`: `P` for `ω = 1`, `Q` for `ω = log` (`primeSum_one`, `primeSum_log`), so one
  Mellin–Barnes lemma serves both (R) for `D` and (R) for `D^log`. `PrimeWeight ω`: `ω ≥ 0` and the series converges
  absolutely on `Re z > 1`. `wtd ω W` multiplies a weight by `ω(p)ω(q)`.
* `kMB a μ ν z = a⁻¹ K_ν((z + μ)/a)`: the Mellin–Barnes kernel of `t^μ (1 + t^a)^{-ν}`. It covers every kernel of
  M4b: `K_s(z)` (`a = 1`, `μ = 0`, `ν = s`), `Γ(z+i)Γ(s-z+j)/Γ(s+i+j)` (`a = 1`, `μ = i`, `ν = s+i+j`), the kernel of
  `(p²+q²)^{-s}` (`a = 2`, `μ = 0`, `ν = s`) and that of `S` (`a = 2`, `μ = 1 - s`, `ν = 2`).
* `Wrise N cf`, `krise N cf`: finite combinations `∑ c_{ij}(s) p^i q^j (p+q)^{-s-i-j}` and their kernels
  `∑ c_{ij}(s) Γ(z+i)Γ(s-z+j)/Γ(s+i+j)`; `W_G`, `W₀`, `W_H` are instances.
* `Ilog A k c s = (1/2πi) ∫_{(c)} k(z,s) Q(z) Q(L(s) - z) dz` with paper 1's continuation `Qcont`; `Iminus` and
  `Iplus` are the paper's `I` and `I⁺` (Step 1 of `cl:thm:mero`) on the lines `c = Re L(s)/2` and
  `c₊ = min(3/4, (Re L(s) - 1/2)/2)`; `Fmero` is the continuation of `D^log` to `ℍ_L`, glued from the series on
  `R_L`, `(cl:eq:Iplus)` on `3/2 < Re L ≤ 2` and `(cl:eq:strip)` on `1 < Re L ≤ 3/2`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M4b

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-! ## Prime sums and weights -/

/-- `∑_p ω(p) p^{-z}`. -/
def primeSum (ω : ℕ → ℝ) (z : ℂ) : ℂ := ∑' p : Nat.Primes, (ω (p : ℕ) : ℂ) * ((p : ℕ) : ℂ) ^ (-z)

/-- `ω ≥ 0`, and `∑_p ω(p) p^{-z}` converges absolutely on `Re z > 1`. -/
def PrimeWeight (ω : ℕ → ℝ) : Prop :=
  (∀ n, 0 ≤ ω n) ∧
    ∀ z : ℂ, 1 < z.re → Summable fun p : Nat.Primes => ‖(ω (p : ℕ) : ℂ) * ((p : ℕ) : ℂ) ^ (-z)‖

/-- The weight multiplied by `ω(p)ω(q)`. -/
def wtd (ω : ℕ → ℝ) (W : ℂ → ℕ → ℕ → ℂ) (s : ℂ) (p q : ℕ) : ℂ := (ω p : ℂ) * (ω q : ℂ) * W s p q

lemma primeSum_log : primeSum (fun n => Real.log n) = Q := rfl

lemma primeSum_one : primeSum (fun _ => 1) = P := by
  funext z; simp [primeSum, P]

lemma wtd_one (W : ℂ → ℕ → ℕ → ℂ) : wtd (fun _ => 1) W = W := by
  funext s p q; simp [wtd]

lemma WT_eq_wtd : WT = wtd (fun n => Real.log n) WG := rfl

lemma W0log_eq_wtd : W0log = wtd (fun n => Real.log n) W0 := rfl

lemma WHlog_eq_wtd (N : ℕ) (h : ℕ → ℕ → ℂ) : WHlog N h = wtd (fun n => Real.log n) (WH N h) := rfl

lemma primeWeight_one : PrimeWeight (fun _ => 1) :=
  ⟨fun _ => zero_le_one, fun _ hz => by simpa using summable_norm_P_terms hz⟩

lemma primeWeight_log : PrimeWeight (fun n => Real.log n) :=
  ⟨fun n => Real.log_natCast_nonneg n, fun _ hz => summable_norm_Q_terms hz⟩

/-! ## Mellin–Barnes kernels -/

/-- `a⁻¹ K_ν((z + μ)/a)`, the Mellin–Barnes kernel of `t^μ (1 + t^a)^{-ν}`. -/
def kMB (a : ℕ) (μ ν z : ℂ) : ℂ := ((a : ℂ))⁻¹ * KerS ν ((z + μ) / a)

/-- `∑_{i,j<N} c_{ij}(s) p^i q^j (p+q)^{-s-i-j}`. -/
def Wrise (N : ℕ) (cf : ℕ → ℕ → ℂ → ℂ) (s : ℂ) (p q : ℕ) : ℂ :=
  ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
    cf i j s * (p : ℂ) ^ i * (q : ℂ) ^ j * (((p + q : ℕ) : ℂ)) ^ (-(s + i + j))

/-- Its kernel `∑_{i,j<N} c_{ij}(s) Γ(z+i)Γ(s-z+j)/Γ(s+i+j)` (the kernel of `p^iq^j(p+q)^{-s-i-j}` is
`Γ(z+i)Γ(s-z+j)/Γ(s+i+j)`, proof of `cl:prop:T0`). -/
def krise (N : ℕ) (cf : ℕ → ℕ → ℂ → ℂ) (z s : ℂ) : ℂ :=
  ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
    cf i j s * (Gamma (z + i) * Gamma (s - z + j) / Gamma (s + i + j))

/-- The coefficients of `W₀ = (1 - s)(p+q)^{-s} + s(s+1) pq (p+q)^{-s-2}`. -/
def cW0 (i j : ℕ) (s : ℂ) : ℂ :=
  if i = 0 ∧ j = 0 then 1 - s else if i = 1 ∧ j = 1 then s * (s + 1) else 0

/-- The coefficients of `W_H`: `h_{ij} Γ(s+i+j)/Γ(s)`. -/
def cWH (h : ℕ → ℕ → ℂ) (i j : ℕ) (s : ℂ) : ℂ := h i j * (Gamma (s + i + j) / Gamma s)

lemma WH_eq_Wrise (N : ℕ) (h : ℕ → ℕ → ℂ) : WH N h = Wrise N (cWH h) := rfl

/-! ## The objects of `cl:thm:mero` -/

/-- `(1/2πi) ∫_{(c)} k(z,s) Q(z) Q(L(s) - z) dz`, with paper 1's continuation `Qcont` for `Q`. -/
def Ilog (A : Aff) (k : ℂ → ℂ → ℂ) (c : ℝ) (s : ℂ) : ℂ :=
  VerticalIntegral' (fun z => k z s * Qcont z * Qcont (A.app s - z)) c

/-- The line of `I`: `c = Re L(s)/2`. For `1 < Re L(s) < 2` it lies in `(max(1/2, Re L(s)-1), min(1, Re L(s)-1/2))`,
so that neither factor has a pole on it. -/
def cMinus (A : Aff) (s : ℂ) : ℝ := (A.app s).re / 2

/-- The line of `I⁺`: `c₊ = min(3/4, (Re L(s) - 1/2)/2)`. For `3/2 < Re L(s) < 3` it lies in
`(1/2, min(1, Re L(s) - 1))`. -/
def cPlus (A : Aff) (s : ℂ) : ℝ := min (3 / 4) (((A.app s).re - 1 / 2) / 2)

/-- The paper's `I(s)` (Step 1 of `cl:thm:mero`), on `1 < Re L(s) < 2`. -/
def Iminus (A : Aff) (k : ℂ → ℂ → ℂ) (s : ℂ) : ℂ := Ilog A k (cMinus A s) s

/-- The paper's `I⁺(s)` (Step 1 of `cl:thm:mero`), on `3/2 < Re L(s) < 3`. -/
def Iplus (A : Aff) (k : ℂ → ℂ → ℂ) (s : ℂ) : ℂ := Ilog A k (cPlus A s) s

/-- The continuation of `D^log` to `ℍ_L`: the series on `R_L`, `I⁺(s) + k(1,s)Q(L(s)-1)` (eq. `(cl:eq:Iplus)`) on
`3/2 < Re L(s) ≤ 2`, and `I(s) + 𝔟(s)Q(L(s)-1)` (eq. `(cl:eq:strip)`) on `Re L(s) ≤ 3/2`. -/
def Fmero (A : Aff) (k : ℂ → ℂ → ℂ) (W : ℂ → ℕ → ℕ → ℂ) (s : ℂ) : ℂ := by
  classical
  exact if 2 < (A.app s).re then Dser W s
    else if 3 / 2 < (A.app s).re then Iplus A k s + k 1 s * Qcont (A.app s - 1)
    else Iminus A k s + bracket A k s * Qcont (A.app s - 1)

/-- The strip `1 < Re L(s) < 2` of `(cl:eq:strip)`. -/
def stripL (A : Aff) : Set ℂ := {s | 1 < (A.app s).re ∧ (A.app s).re < 2}

/-- The region `3/2 < Re L(s) < 3` of `(cl:eq:Iplus)`. -/
def upperL (A : Aff) : Set ℂ := {s | 3 / 2 < (A.app s).re ∧ (A.app s).re < 3}

/-! ## Regions -/

lemma app_re' (A : Aff) (s : ℂ) : (A.app s).re = A.ell * s.re + A.ell0 := by
  simp [Aff.app]

lemma continuous_app_re' (A : Aff) : Continuous fun s => (A.app s).re := by
  unfold Aff.app; fun_prop

lemma isOpen_RL (A : Aff) : IsOpen A.RL :=
  isOpen_lt continuous_const (continuous_app_re' A)

lemma isOpen_stripL (A : Aff) : IsOpen (stripL A) :=
  (isOpen_lt continuous_const (continuous_app_re' A)).inter
    (isOpen_lt (continuous_app_re' A) continuous_const)

lemma isOpen_upperL (A : Aff) : IsOpen (upperL A) :=
  (isOpen_lt continuous_const (continuous_app_re' A)).inter
    (isOpen_lt (continuous_app_re' A) continuous_const)

lemma stripL_subset_DL (A : Aff) : stripL A ⊆ A.DL := fun _ hs => ⟨hs.1, by linarith [hs.2]⟩

lemma upperL_subset_DL (A : Aff) : upperL A ⊆ A.DL := fun _ hs => ⟨by linarith [hs.1], hs.2⟩

lemma HL_subset (A : Aff) : A.HL ⊆ stripL A ∪ upperL A ∪ A.RL := by
  intro s hs
  have hs' : 1 < (A.app s).re := hs
  by_cases h2 : 2 < (A.app s).re
  · exact Or.inr h2
  · by_cases h3 : 3 / 2 < (A.app s).re
    · by_cases h4 : (A.app s).re < 2
      · exact Or.inl (Or.inl ⟨hs', h4⟩)
      · exact Or.inl (Or.inr ⟨h3, by linarith⟩)
    · exact Or.inl (Or.inl ⟨hs', by linarith⟩)

/-- `ℍ_L` is the half-plane `σ > (1 - ℓ₀)/ℓ`. -/
lemma HL_eq_halfPlane (A : Aff) : A.HL = halfPlane ((1 - A.ell0) / A.ell) := by
  ext s
  simp only [Aff.HL, halfPlane, mem_ofPred_eq, app_re']
  rw [div_lt_iff₀ A.ell_pos]
  constructor <;> intro h <;> linarith

/-- `R_L` is the half-plane `σ > (2 - ℓ₀)/ℓ`. -/
lemma RL_eq_halfPlane (A : Aff) : A.RL = halfPlane ((2 - A.ell0) / A.ell) := by
  ext s
  simp only [Aff.RL, halfPlane, mem_ofPred_eq, app_re']
  rw [div_lt_iff₀ A.ell_pos]
  constructor <;> intro h <;> linarith

lemma isPreconnected_HL (A : Aff) : IsPreconnected A.HL := by
  rw [HL_eq_halfPlane]; exact (convex_halfSpace_re_gt _).isPreconnected

lemma Fmero_of_RL (A : Aff) (k : ℂ → ℂ → ℂ) (W : ℂ → ℕ → ℕ → ℂ) {s : ℂ} (hs : 2 < (A.app s).re) :
    Fmero A k W s = Dser W s := by
  simp [Fmero, hs]

lemma idL_HL_eq : Aff.idL.HL = HH := by ext s; simp [Aff.HL, M4a.app_idL, halfPlane]

lemma idL_RL_eq : Aff.idL.RL = halfPlane 2 := by ext s; simp [Aff.RL, M4a.app_idL, halfPlane]

lemma twoL_app (s : ℂ) : Aff.twoL.app s = 2 * s := by simp [Aff.app, Aff.twoL]

lemma twoOneL_app (s : ℂ) : Aff.twoOneL.app s = 2 * s + 1 := by simp [Aff.app, Aff.twoOneL]

/-! ## The kernels of the examples: facts with short proofs (copies of the sanity lemmas of
`Paper2/Statements.lean`, which this milestone does not import) -/

/-- `K_s(z)` is jointly holomorphic on `{0 < Re z < Re s}`. -/
lemma differentiableOn_kerG' :
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

lemma kerG_K1 : K1 Aff.idL kerG := by
  refine differentiableOn_kerG'.mono ?_
  rintro ⟨z, s⟩ ⟨-, hz0, hz1⟩
  simp [Aff.app, Aff.idL] at hz1 ⊢
  exact ⟨hz0, hz1⟩

lemma kerG_H2a : H2a Aff.idL kerG := by
  refine differentiableOn_kerG'.mono ?_
  rintro ⟨z, s⟩ ⟨-, hz0, hz1⟩
  simp [Aff.app, Aff.idL] at hz1 ⊢
  exact ⟨hz0, hz1⟩

lemma kerG_K3 : K3 Aff.idL kerG := by
  intro s _ z _
  simp only [kerG, KerS, map_div₀, map_mul, ← Complex.Gamma_conj, map_sub]

lemma kerG_bracket {s : ℂ} (hs : 1 < s.re) : bracket Aff.idL kerG s = 2 / (s - 1) := by
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

lemma kerSq_bracket {s : ℂ} (hs : 1 / 2 < s.re) :
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

lemma kerG_eq_kr : kr 0 = kerG := by
  funext z s; simp [kr, kerG]

lemma k0_H2a : H2a Aff.idL k0 := by
  have h := kerG_H2a
  unfold H2a at h ⊢
  have : (fun p : ℂ × ℂ => k0 p.1 p.2) = fun p => kerG p.1 p.2 * (p.1 - 1) * (p.2 - 1 - p.1) := by
    funext p; simp [k0, kerG]
  rw [this]
  exact (h.mul (differentiable_fst.sub_const 1).differentiableOn).mul
    ((differentiable_snd.sub_const 1).sub differentiable_fst).differentiableOn

lemma k0_K1 : K1 Aff.idL k0 := by
  refine k0_H2a.mono ?_
  rintro ⟨z, s⟩ ⟨hs, hz⟩
  exact ⟨hs.1, hz⟩

lemma k0_K3 : K3 Aff.idL k0 := by
  intro s _ z _
  simp only [k0, KerS, map_div₀, map_mul, ← Complex.Gamma_conj, map_sub, map_one]

lemma k0_bracket (s : ℂ) : bracket Aff.idL k0 s = 0 := by
  simp [bracket, k0, Aff.app, Aff.idL]

/-- A kernel that is a global quotient `u/v` of entire functions of two variables, with `v` non-zero somewhere in
every ball, is meromorphic on `ℂ²` in the sense of `IsMeromorphic₂`. -/
lemma isMeromorphic₂_of_global {k : ℂ → ℂ → ℂ} {u v : ℂ × ℂ → ℂ} (hu : AnalyticOnNhd ℂ u univ)
    (hv : AnalyticOnNhd ℂ v univ) (hne : ∀ p : ℂ × ℂ, ∀ r > 0, ∃ q ∈ ball p r, v q ≠ 0)
    (hk : ∀ q : ℂ × ℂ, v q ≠ 0 → k q.1 q.2 = u q / v q) : IsMeromorphic₂ k :=
  fun p => ⟨1, one_pos, u, v, fun q _ => hu q (mem_univ q), fun q _ => hv q (mem_univ q),
    hne p 1 one_pos, fun q _ hq => hk q hq⟩

end GoldbachBoundaries.Paper2.M4b
