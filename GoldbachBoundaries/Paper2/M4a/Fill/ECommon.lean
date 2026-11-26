import GoldbachBoundaries.Paper2.M4a.Kernel

/-!
# M4a filler group E: shared helpers

Helpers for the group E targets (`Restrict.lean`: `analyticOnNhd_lineCoeff`, `eq_div_of_continuousAt`,
`exists_lineCoeff_ne_zero`, `isMeromorphic₂_restrict_line`; `H3.lean`: `analyticOnNhd_bracket`,
`bracket_meromorphic_of_K4`, `not_eventually_zero_of_eqOn_bracket`). They live in the sub-namespace `FillE` to keep
clear of other fillers' helpers.
-/

noncomputable section

open Complex Filter Topology Set Metric

namespace GoldbachBoundaries.Paper2.M4a.FillE

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-! ## One variable: Taylor's theorem at `z₀` -/

/-- Taylor's theorem at `z₀` with an analytic remainder (from Mathlib's version at `0`). -/
lemma taylor_at {f : ℂ → ℂ} {z₀ : ℂ} (hf : AnalyticAt ℂ f z₀) (n : ℕ) :
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F z₀ ∧ ∀ᶠ z in 𝓝 z₀,
      f z = (∑ i ∈ Finset.range n, ((z - z₀) ^ i / i.factorial) • iteratedDeriv i f z₀) +
        (z - z₀) ^ n • F z := by
  have hg : AnalyticAt ℂ (fun w => f (z₀ + w)) 0 := by
    have h1 : AnalyticAt ℂ (fun w : ℂ => z₀ + w) 0 := by fun_prop
    exact hf.comp_of_eq (f := fun w : ℂ => z₀ + w) h1 (by simp)
  obtain ⟨F₀, hF₀, hev⟩ := hg.exists_eventuallyEq_sum_add_pow_mul n
  have hder : ∀ i, iteratedDeriv i (fun w => f (z₀ + w)) 0 = iteratedDeriv i f z₀ := by
    intro i; rw [iteratedDeriv_comp_const_add]; simp
  refine ⟨fun z => F₀ (z - z₀), ?_, ?_⟩
  · have h1 : AnalyticAt ℂ (fun z : ℂ => z - z₀) z₀ := by fun_prop
    exact hF₀.comp_of_eq (f := fun z : ℂ => z - z₀) h1 (by simp)
  · have ht : Tendsto (fun z : ℂ => z - z₀) (𝓝 z₀) (𝓝 0) := by
      have : Continuous fun z : ℂ => z - z₀ := by fun_prop
      simpa using this.tendsto z₀
    filter_upwards [ht.eventually hev] with z hz
    simp only [hder, add_sub_cancel] at hz
    exact hz

/-- If the first `m` derivatives of an analytic `f` vanish at `z₀`, then near `z₀`,
`f z = (z - z₀)^m (f^{(m)}(z₀)/m! + (z - z₀) G z)` with `G` analytic. -/
lemma eq_pow_mul_of_iteratedDeriv {f : ℂ → ℂ} {z₀ : ℂ} (hf : AnalyticAt ℂ f z₀) {m : ℕ}
    (hj : ∀ j < m, iteratedDeriv j f z₀ = 0) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G z₀ ∧ ∀ᶠ z in 𝓝 z₀,
      f z = (z - z₀) ^ m * (iteratedDeriv m f z₀ / m.factorial + (z - z₀) * G z) := by
  obtain ⟨G, hG, hev⟩ := taylor_at hf (m + 1)
  refine ⟨G, hG, ?_⟩
  filter_upwards [hev] with z hz
  rw [hz, Finset.sum_range_succ, Finset.sum_eq_zero (fun i hi => by
    rw [hj i (Finset.mem_range.mp hi), smul_zero])]
  simp only [smul_eq_mul, zero_add, pow_succ]
  ring

/-! ## Two variables: slices and partial derivatives in the first variable -/

/-- A slice `z ↦ u (z, s)` of a function analytic at `(z, s)` is analytic at `z`. -/
lemma analyticAt_slice {u : ℂ × ℂ → ℂ} {z s : ℂ} (h : AnalyticAt ℂ u (z, s)) :
    AnalyticAt ℂ (fun w => u (w, s)) z := by
  have h1 : AnalyticAt ℂ (fun w : ℂ => (w, s)) z := analyticAt_id.prod analyticAt_const
  exact h.comp_of_eq (f := fun w : ℂ => (w, s)) h1 rfl

/-- The partial derivative in the first variable. -/
def pz (u : ℂ × ℂ → ℂ) : ℂ × ℂ → ℂ := fun q => fderiv ℂ u q (1, 0)

lemma analyticOnNhd_pz {u : ℂ × ℂ → ℂ} {U : Set (ℂ × ℂ)} (hu : AnalyticOnNhd ℂ u U) :
    AnalyticOnNhd ℂ (pz u) U := by
  intro q hq
  have h1 := hu.fderiv q hq
  have h2 : AnalyticAt ℂ (fun L : (ℂ × ℂ) →L[ℂ] ℂ => L (1, 0)) (fderiv ℂ u q) :=
    (ContinuousLinearMap.apply ℂ ℂ ((1 : ℂ), (0 : ℂ))).analyticAt _
  exact h2.comp h1

lemma analyticOnNhd_iterate_pz {u : ℂ × ℂ → ℂ} {U : Set (ℂ × ℂ)} (hu : AnalyticOnNhd ℂ u U) (j : ℕ) :
    AnalyticOnNhd ℂ (pz^[j] u) U := by
  induction j generalizing u with
  | zero => simpa using hu
  | succ j ih =>
    rw [Function.iterate_succ_apply]
    exact ih (analyticOnNhd_pz hu)

/-- The derivative of a slice is the slice of the partial derivative. -/
lemma hasDerivAt_slice {u : ℂ × ℂ → ℂ} {z s : ℂ} (h : DifferentiableAt ℂ u (z, s)) :
    HasDerivAt (fun w => u (w, s)) (pz u (z, s)) z := by
  have h1 : HasDerivAt (fun w : ℂ => (w, s)) ((1 : ℂ), (0 : ℂ)) z :=
    (hasDerivAt_id z).prodMk (hasDerivAt_const z s)
  exact h.hasFDerivAt.comp_hasDerivAt z h1

/-- The iterated derivative of a slice is the slice of the iterated partial derivative. -/
lemma iteratedDeriv_slice {U : Set (ℂ × ℂ)} (hU : IsOpen U) (j : ℕ) :
    ∀ u : ℂ × ℂ → ℂ, AnalyticOnNhd ℂ u U → ∀ w s : ℂ, (w, s) ∈ U →
      iteratedDeriv j (fun z => u (z, s)) w = (pz^[j] u) (w, s) := by
  induction j with
  | zero => intro u _ w s _; simp
  | succ j ih =>
    intro u hu w s hws
    rw [iteratedDeriv_succ', Function.iterate_succ_apply]
    have hev : deriv (fun z => u (z, s)) =ᶠ[𝓝 w] fun z => pz u (z, s) := by
      have hc : Continuous fun z : ℂ => (z, s) := by fun_prop
      have hmem : (fun z : ℂ => (z, s)) ⁻¹' U ∈ 𝓝 w := (hU.preimage hc).mem_nhds hws
      filter_upwards [hmem] with z hz
      exact (hasDerivAt_slice (hu _ hz).differentiableAt).deriv
    rw [hev.iteratedDeriv_eq]
    exact ih (pz u) (analyticOnNhd_pz hu) w s hws

/-! ## The regions of the affine map -/

lemma isOpen_domK1 (A : Aff) : IsOpen A.domK1 := by
  have h1 : IsOpen {p : ℂ × ℂ | p.2 ∈ A.DL} := (isOpen_DL A).preimage continuous_snd
  have h2 : IsOpen {p : ℂ × ℂ | 0 < p.1.re} :=
    isOpen_lt continuous_const (Complex.continuous_re.comp continuous_fst)
  have h3 : IsOpen {p : ℂ × ℂ | p.1.re < (A.app p.2).re} :=
    isOpen_lt (Complex.continuous_re.comp continuous_fst) ((continuous_app_re A).comp continuous_snd)
  have : A.domK1 = {p : ℂ × ℂ | p.2 ∈ A.DL} ∩ ({p : ℂ × ℂ | 0 < p.1.re} ∩
      {p : ℂ × ℂ | p.1.re < (A.app p.2).re}) := by
    ext p; simp [Aff.domK1, Aff.Str]
  rw [this]; exact h1.inter (h2.inter h3)

/-- (K1) gives joint differentiability at every point of the open domain. -/
lemma differentiableAt_of_K1 {A : Aff} {k : ℂ → ℂ → ℂ} (hK1 : K1 A k) {z s : ℂ} (hs : s ∈ A.DL)
    (hz0 : 0 < z.re) (hzs : z.re < (A.app s).re) :
    DifferentiableAt ℂ (fun p : ℂ × ℂ => k p.1 p.2) (z, s) :=
  hK1.differentiableAt ((isOpen_domK1 A).mem_nhds ⟨hs, hz0, hzs⟩)

/-- (K1) gives continuity of `z ↦ k z s` at points of `Str(s)`, `s ∈ D_L`. -/
lemma continuousAt_slice_of_K1 {A : Aff} {k : ℂ → ℂ → ℂ} (hK1 : K1 A k) {z s : ℂ} (hs : s ∈ A.DL)
    (hz0 : 0 < z.re) (hzs : z.re < (A.app s).re) :
    ContinuousAt (fun w => k w s) z := by
  have h := (differentiableAt_of_K1 hK1 hs hz0 hzs).continuousAt
  have hc : ContinuousAt (fun w : ℂ => (w, s)) z := by fun_prop
  exact h.comp_of_eq (f := fun w : ℂ => (w, s)) hc rfl

lemma one_mem_Str {A : Aff} {s : ℂ} (hs : s ∈ A.DL) : 0 < (1 : ℂ).re ∧ (1 : ℂ).re < (A.app s).re := by
  simpa using hs.1

lemma app_sub_one_mem_Str {A : Aff} {s : ℂ} (hs : s ∈ A.DL) :
    0 < (A.app s - 1).re ∧ (A.app s - 1).re < (A.app s).re := by
  have := hs.1
  simp only [sub_re, one_re]
  constructor <;> linarith

lemma convex_DL (A : Aff) : Convex ℝ A.DL := by
  intro x hx y hy a b ha hb hab
  simp only [Aff.DL, mem_ofPred_eq, app_re] at hx hy ⊢
  simp only [add_re, smul_re, smul_eq_mul]
  have hl := A.ell_pos
  have e : A.ell * (a * x.re + b * y.re) + A.ell0 =
      a * (A.ell * x.re + A.ell0) + b * (A.ell * y.re + A.ell0) := by
    have : A.ell0 = (a + b) * A.ell0 := by rw [hab, one_mul]
    linear_combination this
  rw [e]
  set X := A.ell * x.re + A.ell0
  set Y := A.ell * y.re + A.ell0
  have h1 : a * min X Y + b * min X Y ≤ a * X + b * Y := by
    have := mul_le_mul_of_nonneg_left (min_le_left X Y) ha
    have := mul_le_mul_of_nonneg_left (min_le_right X Y) hb
    linarith
  have h2 : a * X + b * Y ≤ a * max X Y + b * max X Y := by
    have := mul_le_mul_of_nonneg_left (le_max_left X Y) ha
    have := mul_le_mul_of_nonneg_left (le_max_right X Y) hb
    linarith
  have hmin : 1 < min X Y := lt_min hx.1 hy.1
  have hmax : max X Y < 3 := max_lt hx.2 hy.2
  have e1 : a * min X Y + b * min X Y = min X Y := by rw [← add_mul, hab, one_mul]
  have e2 : a * max X Y + b * max X Y = max X Y := by rw [← add_mul, hab, one_mul]
  constructor <;> linarith

end GoldbachBoundaries.Paper2.M4a.FillE
