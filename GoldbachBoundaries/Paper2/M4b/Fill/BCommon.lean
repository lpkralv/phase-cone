import GoldbachBoundaries.Paper2.M4b.Rising

/-!
# Fill, group B: shared helpers for the log integral `Ilog` and its contour shifts

* `isOpen_domK1B`, `differentiableAt_k_of_K1B`: (K1) at a point of its open domain.
* `exists_numerator_of_simplePole`: at a pole of order `≥ -1` with residue `R`, `(z - p) f(z)` agrees on `𝓝[≠] p`
  with a function `H` differentiable at `p` with `H p = R`.
* `isBigO_mul_sub_of_numerator`: then `g f - g(p) H(p)/(z - p)` is bounded near `p` (it is the slope of `g H`).
* `tendsto_hInt_of_bound`: a horizontal segment integral of a function `O((1+|y|)^{-3/2})` tends to `0`.
-/

noncomputable section

open Complex Filter Topology Set Metric MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M4b

open GoldbachBoundaries GoldbachBoundaries.Paper2

lemma isOpen_domK1B (A : Aff) : IsOpen A.domK1 := by
  have h1 : IsOpen {p : ℂ × ℂ | p.2 ∈ A.DL} := (M4a.isOpen_DL A).preimage continuous_snd
  have h2 : IsOpen {p : ℂ × ℂ | 0 < p.1.re} :=
    isOpen_lt continuous_const (Complex.continuous_re.comp continuous_fst)
  have h3 : IsOpen {p : ℂ × ℂ | p.1.re < (A.app p.2).re} :=
    isOpen_lt (Complex.continuous_re.comp continuous_fst) ((continuous_app_re' A).comp continuous_snd)
  have : A.domK1 = {p : ℂ × ℂ | p.2 ∈ A.DL} ∩ ({p : ℂ × ℂ | 0 < p.1.re} ∩
      {p : ℂ × ℂ | p.1.re < (A.app p.2).re}) := by
    ext p; simp [Aff.domK1, Aff.Str]
  rw [this]; exact h1.inter (h2.inter h3)

lemma differentiableAt_k_of_K1B {A : Aff} {k : ℂ → ℂ → ℂ} (hK1 : K1 A k) {z s : ℂ} (hs : s ∈ A.DL)
    (hz0 : 0 < z.re) (hzs : z.re < (A.app s).re) :
    DifferentiableAt ℂ (fun p : ℂ × ℂ => k p.1 p.2) (z, s) :=
  hK1.differentiableAt ((isOpen_domK1B A).mem_nhds ⟨hs, hz0, hzs⟩)

/-- At a pole of order `≥ -1` with residue `R`, `(z - p) f(z)` is, near `p`, a function differentiable at `p`
with value `R`. -/
lemma exists_numerator_of_simplePole {f : ℂ → ℂ} {p R : ℂ} (hf : MeromorphicAt f p)
    (hord : -1 ≤ meromorphicOrderAt f p) (hres : HasResidue f p R) :
    ∃ H : ℂ → ℂ, DifferentiableAt ℂ H p ∧ H p = R ∧ ∀ᶠ z in 𝓝[≠] p, (z - p) * f z = H z := by
  have key : ∀ H : ℂ → ℂ, DifferentiableAt ℂ H p → (∀ᶠ z in 𝓝[≠] p, (z - p) * f z = H z) →
      ∃ H : ℂ → ℂ, DifferentiableAt ℂ H p ∧ H p = R ∧ ∀ᶠ z in 𝓝[≠] p, (z - p) * f z = H z := by
    intro H hH hev
    refine ⟨H, hH, ?_, hev⟩
    have h1 : Tendsto H (𝓝[≠] p) (𝓝 (H p)) := hH.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto H (𝓝[≠] p) (𝓝 R) := (tendsto_congr' hev).mp hres
    exact tendsto_nhds_unique h1 h2
  by_cases htop : meromorphicOrderAt f p = ⊤
  · rw [meromorphicOrderAt_eq_top_iff] at htop
    refine key (fun _ => 0) (differentiableAt_const _) ?_
    filter_upwards [htop] with z hz
    simp [hz]
  · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp htop
    obtain ⟨φ, hφ, -, hev⟩ := (meromorphicOrderAt_eq_int_iff hf).mp hn.symm
    have hn1 : -1 ≤ n := by
      rw [← hn] at hord
      have : ((-1 : ℤ) : WithTop ℤ) ≤ (n : WithTop ℤ) := by simpa using hord
      exact_mod_cast this
    refine key (fun z => (z - p) ^ (n + 1).toNat * φ z)
      (((differentiableAt_id.sub_const p).pow _).mul hφ.differentiableAt) ?_
    filter_upwards [hev, self_mem_nhdsWithin] with z hz hzp
    have hzp' : z - p ≠ 0 := sub_ne_zero.mpr hzp
    rw [hz, smul_eq_mul, ← mul_assoc]
    congr 1
    have hnat : ((n + 1).toNat : ℤ) = n + 1 := Int.toNat_of_nonneg (by omega)
    rw [← zpow_natCast, hnat, zpow_add_one₀ hzp']
    ring

/-- If `(z - p) F(z) = H(z)` near `p` with `H` differentiable at `p`, and `g` is differentiable at `p`, then
`g F - g(p) H(p)/(z - p)` is bounded on `𝓝[≠] p`: it is the slope of `g H` at `p`. -/
lemma isBigO_mul_sub_of_numerator {F g H : ℂ → ℂ} {p : ℂ} (hH : DifferentiableAt ℂ H p)
    (hg : DifferentiableAt ℂ g p) (hev : ∀ᶠ z in 𝓝[≠] p, (z - p) * F z = H z) :
    (fun z => g z * F z - g p * H p / (z - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
  have hslope := (hasDerivAt_iff_tendsto_slope.mp (hg.mul hH).hasDerivAt)
  refine (hslope.isBigO_one ℂ).congr' ?_ EventuallyEq.rfl
  filter_upwards [hev, self_mem_nhdsWithin] with z hz hzp
  have hzp' : z - p ≠ 0 := sub_ne_zero.mpr hzp
  rw [slope_def_field]
  have hF : F z = H z / (z - p) := by rw [← hz]; field_simp
  rw [hF]
  simp only [Pi.mul_apply]
  field_simp

/-- A horizontal segment integral of a function bounded by `M (1+|y|)^{-3/2}` for `|y| ≥ Y` tends to `0` as
`y → ±∞`. -/
lemma tendsto_hInt_of_bound {f : ℂ → ℂ} {c c' M Y : ℝ} (hcc : c ≤ c')
    (h : ∀ z : ℂ, c ≤ z.re → z.re ≤ c' → Y ≤ |z.im| → ‖f z‖ ≤ M / (1 + |z.im|) ^ (3 / 2 : ℝ)) :
    Tendsto (fun y : ℝ => ∫ x in c..c', f (x + y * I)) atBot (𝓝 0) ∧
      Tendsto (fun y : ℝ => ∫ x in c..c', f (x + y * I)) atTop (𝓝 0) := by
  have hbound : ∀ y : ℝ, Y ≤ |y| →
      ‖∫ x in c..c', f (x + y * I)‖ ≤ M / (1 + |y|) ^ (3 / 2 : ℝ) * |c' - c| := by
    intro y hy
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    have hx' := uIoc_subset_uIcc hx
    rw [uIcc_of_le hcc] at hx'
    have := h (x + y * I) (by simpa using hx'.1) (by simpa using hx'.2) (by simpa using hy)
    simpa using this
  have hpow : Tendsto (fun t : ℝ => M / (1 + t) ^ (3 / 2 : ℝ) * |c' - c|) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => (1 + t) ^ (3 / 2 : ℝ)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num)).comp (tendsto_atTop_add_const_left _ 1 tendsto_id)
    simpa using (tendsto_const_nhds.div_atTop h1).mul_const |c' - c|
  constructor
  · refine squeeze_zero_norm' ?_ (hpow.comp tendsto_abs_atBot_atTop)
    filter_upwards [(tendsto_abs_atBot_atTop.eventually_ge_atTop Y)] with y hy
    exact hbound y hy
  · refine squeeze_zero_norm' ?_ (hpow.comp tendsto_abs_atTop_atTop)
    filter_upwards [(tendsto_abs_atTop_atTop.eventually_ge_atTop Y)] with y hy
    exact hbound y hy

end GoldbachBoundaries.Paper2.M4b
