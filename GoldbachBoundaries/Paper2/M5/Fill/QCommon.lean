import GoldbachBoundaries.Paper2.M5.General
import GoldbachBoundaries.Paper2.M5.Fill.norm_negLogDerivZeta_le_of_sep

/-!
# Filler group Q: shared helpers for `Qleft_i`, `Qleft_ii`, `Qleft_iii`

* `poleSetQ_cases_RH`: under RH a point of `Σ_Q` is real, a zero, or has real part `≤ 1/4`.
* `norm_Qcont_le_four`: `‖Q(w)‖ ≤ ‖A(w)‖ + ‖A(2w)‖ + ‖A(3w)‖ + ‖sigmaTail 4 w‖` on `Re w > 0`.
* `exists_bound_of_local`: a real function bounded on a punctured neighbourhood (within `D`) of every point of a
  compact `K` is bounded on `K ∩ D`.
* `negLogDerivZeta_local`: near any `p`, `‖A(u)‖ ≤ c/‖u - p‖ + M` (PNT+'s
  `logDeriv_sub_principal_isBigO_one_of_meromorphicOrderAt`).
* `exists_bound_weighted_negLogDeriv`: `(Re u - a)‖A(u)‖` is bounded on `K ∩ {Re u > a}` for compact `K` whose points
  have real part `a` or are regular points of `A`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- Under RH a point of `Σ_Q` is real (`1`, `1/k`), a non-trivial zero (`ρ/1`), or has real part `1/(2n) ≤ 1/4`. -/
lemma poleSetQ_cases_RH (hRH : RiemannHypothesis) {a : ℂ} (ha : a ∈ PoleSetQ) :
    a.im = 0 ∨ a ∈ NontrivialZeros ∨ a.re ≤ 1 / 4 := by
  rcases ha with (ha | ⟨k, -, -, rfl⟩) | ⟨n, hn, -, ρ, hρ, rfl⟩
  · left
    rw [Set.mem_singleton_iff.mp ha]
    simp
  · left
    simp
  · have hre := sigmaFinite_re_eq_half hRH hρ
    rcases eq_or_lt_of_le hn with h1 | h2
    · subst h1
      right; left
      simpa using hρ
    · right; right
      rw [Complex.div_natCast_re, hre]
      have hn' : (2 : ℝ) ≤ n := by exact_mod_cast h2
      rw [div_le_iff₀ (by linarith)]
      nlinarith

/-- The first four terms of the Möbius series and the tail. -/
lemma norm_Qcont_le_four {w : ℂ} (hw : 0 < w.re) :
    ‖Qcont w‖ ≤ ‖negLogDerivZeta w‖ + ‖negLogDerivZeta (2 * w)‖ + ‖negLogDerivZeta (3 * w)‖ +
      ‖sigmaTail 4 w‖ := by
  rw [Qcont_eq_sum_add_tail 4 hw]
  have hterm : ∀ n : ℕ, ‖sigmaTerm n w‖ ≤ ‖negLogDerivZeta ((n : ℂ) * w)‖ := fun n => by
    rw [sigmaTerm, norm_mul]
    calc ‖mu n‖ * ‖negLogDerivZeta ((n : ℂ) * w)‖ ≤ 1 * ‖negLogDerivZeta ((n : ℂ) * w)‖ := by
          gcongr
          exact norm_mu_le_one n
      _ = _ := one_mul _
  have h0 : sigmaTerm 0 w = 0 := by simp [sigmaTerm]
  have h1 := hterm 1
  have h2 := hterm 2
  have h3 := hterm 3
  push_cast at h1 h2 h3
  rw [one_mul] at h1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, h0, zero_add]
  calc ‖sigmaTerm 1 w + sigmaTerm 2 w + sigmaTerm 3 w + sigmaTail 4 w‖
      ≤ ‖sigmaTerm 1 w‖ + ‖sigmaTerm 2 w‖ + ‖sigmaTerm 3 w‖ + ‖sigmaTail 4 w‖ := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        refine (norm_add_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ _ := by gcongr

/-- A real function bounded on a punctured neighbourhood (within `D`) of every point of a compact `K` is bounded on
`K ∩ D`. -/
lemma exists_bound_of_local {K D : Set ℂ} (hK : IsCompact K) (f : ℂ → ℝ)
    (hloc : ∀ x ∈ K, ∃ M : ℝ, ∀ᶠ y in 𝓝 x, y ≠ x → y ∈ D → f y ≤ M) :
    ∃ B : ℝ, ∀ y ∈ K, y ∈ D → f y ≤ B := by
  classical
  choose! M hM using hloc
  obtain ⟨t, htK, hcov⟩ := hK.elim_nhds_subcover (fun x => {y | y ≠ x → y ∈ D → f y ≤ M x})
    fun x hx => hM x hx
  refine ⟨∑ x ∈ t, (|M x| + |f x|), fun y hy hyD => ?_⟩
  obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.mp (hcov hy)
  have hle : |M x| + |f x| ≤ ∑ x ∈ t, (|M x| + |f x|) :=
    Finset.single_le_sum (f := fun x => |M x| + |f x|) (fun _ _ => by positivity) hx
  by_cases hxy : y = x
  · subst hxy
    linarith [le_abs_self (f y), abs_nonneg (M y)]
  · have := hyx hxy hyD
    linarith [le_abs_self (M x), abs_nonneg (f x)]

/-- Near any point `p`, `‖A(u)‖ ≤ c/‖u - p‖ + M` with `c ≥ 0` (`c = |ord_p ζ|`). -/
lemma negLogDerivZeta_local (p : ℂ) :
    ∃ c M : ℝ, 0 ≤ c ∧ ∀ᶠ u in 𝓝 p, u ≠ p → ‖negLogDerivZeta u‖ ≤ c / ‖u - p‖ + M := by
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp (meromorphicOrderAt_riemannZeta_ne_top p)
  have hO := logDeriv_sub_principal_isBigO_one_of_meromorphicOrderAt (meromorphicAt_riemannZeta p) hn.symm
  obtain ⟨M, hM⟩ := hO.bound
  refine ⟨‖(n : ℂ)‖, M, norm_nonneg _, ?_⟩
  have hM' := eventually_nhdsWithin_iff.mp hM
  filter_upwards [hM'] with u hu hup
  have hu' := hu hup
  simp only [Pi.sub_apply, Pi.one_apply, norm_one, mul_one] at hu'
  rw [negLogDerivZeta_eq]
  simp only [norm_neg]
  calc ‖logDeriv riemannZeta u‖
      = ‖(logDeriv riemannZeta u - (n : ℂ) / (u - p)) + (n : ℂ) / (u - p)‖ := by rw [sub_add_cancel]
    _ ≤ ‖logDeriv riemannZeta u - (n : ℂ) / (u - p)‖ + ‖(n : ℂ) / (u - p)‖ := norm_add_le _ _
    _ ≤ M + ‖(n : ℂ)‖ / ‖u - p‖ := by rw [norm_div]; linarith
    _ = _ := by ring

/-- `(Re u - a)‖A(u)‖` is bounded on `K ∩ {Re u > a}`, for a compact `K` each of whose points has real part `a` or
is a regular point of `A`. -/
lemma exists_bound_weighted_negLogDeriv (a : ℝ) {K : Set ℂ} (hK : IsCompact K)
    (hgood : ∀ x ∈ K, x.re = a ∨ (x ≠ 1 ∧ riemannZeta x ≠ 0)) :
    ∃ B : ℝ, ∀ u ∈ K, a < u.re → (u.re - a) * ‖negLogDerivZeta u‖ ≤ B := by
  suffices hloc : ∀ x ∈ K, ∃ M : ℝ, ∀ᶠ y in 𝓝 x, y ≠ x → y ∈ {u : ℂ | a < u.re} →
      (y.re - a) * ‖negLogDerivZeta y‖ ≤ M by
    obtain ⟨B, hB⟩ := exists_bound_of_local hK (fun u => (u.re - a) * ‖negLogDerivZeta u‖) hloc
    exact ⟨B, fun u hu hua => hB u hu hua⟩
  intro x hx
  have hball : ∀ᶠ u in 𝓝 x, ‖u - x‖ < 1 := by
    have := Metric.ball_mem_nhds x one_pos
    filter_upwards [this] with u hu
    rwa [Metric.mem_ball, dist_eq_norm] at hu
  rcases hgood x hx with hre | ⟨hx1, hz⟩
  · obtain ⟨c, M, hc, hloc⟩ := negLogDerivZeta_local x
    refine ⟨c + |M|, ?_⟩
    filter_upwards [hloc, hball] with u hu hu1 hux hua
    have hua' : a < u.re := hua
    have hpos : 0 < ‖u - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hux)
    have hη : u.re - a ≤ ‖u - x‖ := by
      have := Complex.re_le_norm (u - x)
      rw [Complex.sub_re, hre] at this
      exact this
    have hη0 : 0 ≤ u.re - a := by linarith
    have hA := hu hux
    calc (u.re - a) * ‖negLogDerivZeta u‖ ≤ (u.re - a) * (c / ‖u - x‖ + M) :=
          mul_le_mul_of_nonneg_left hA hη0
      _ = (u.re - a) / ‖u - x‖ * c + (u.re - a) * M := by ring
      _ ≤ 1 * c + 1 * |M| := by
          have h1 : (u.re - a) / ‖u - x‖ ≤ 1 := by rw [div_le_one hpos]; exact hη
          have h2 : (u.re - a) * M ≤ 1 * |M| :=
            calc (u.re - a) * M ≤ (u.re - a) * |M| := mul_le_mul_of_nonneg_left (le_abs_self M) hη0
              _ ≤ 1 * |M| := mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg M)
          exact add_le_add (mul_le_mul_of_nonneg_right h1 hc) h2
      _ = c + |M| := by ring
  · have hcont : ContinuousAt negLogDerivZeta x := (analyticAt_negLogDerivZeta hx1 hz).continuousAt
    have hev : ∀ᶠ u in 𝓝 x, ‖negLogDerivZeta u‖ < ‖negLogDerivZeta x‖ + 1 :=
      hcont.norm.eventually (Iio_mem_nhds (lt_add_one _))
    refine ⟨(|x.re - a| + 1) * (‖negLogDerivZeta x‖ + 1), ?_⟩
    filter_upwards [hev, hball] with u hu hu1 _ hua
    have hua' : a < u.re := hua
    have hη : u.re - a ≤ |x.re - a| + 1 := by
      have h1 := Complex.re_le_norm (u - x)
      rw [Complex.sub_re] at h1
      linarith [le_abs_self (x.re - a)]
    exact mul_le_mul hη hu.le (norm_nonneg _) (by positivity)

/-- `log(c a + 3) ≤ 2 log(a + 3)` for `a ≥ 0`, `0 ≤ c ≤ 6` (`c a + 3 ≤ (a + 3)²`). -/
lemma log_mul_add_three_le {a c : ℝ} (ha : 0 ≤ a) (hc0 : 0 ≤ c) (hc : c ≤ 6) :
    Real.log (c * a + 3) ≤ 2 * Real.log (a + 3) := by
  rw [show (2 : ℝ) * Real.log (a + 3) = Real.log ((a + 3) ^ 2) by rw [Real.log_pow]; push_cast; ring]
  refine Real.log_le_log (by positivity) ?_
  nlinarith [mul_le_mul_of_nonneg_right hc ha]

/-- `1 ≤ log(a + 3)` for `a ≥ 0`. -/
lemma one_le_log_add_three {a : ℝ} (ha : 0 ≤ a) : 1 ≤ Real.log (a + 3) := by
  rw [← Real.log_exp 1]
  exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])

/-- `norm_negLogDerivZeta_le_of_sep` with a non-negative constant. -/
lemma exists_sep_bound_nonneg (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 → 2 ≤ |z.im| → riemannZeta z ≠ 0 → ∀ δ : ℝ, 0 < δ →
      δ ≤ 1 → (∀ ρ ∈ NontrivialZeros, |ρ.im - z.im| ≤ 1 → δ ≤ ‖z - ρ‖) →
        ‖negLogDerivZeta z‖ ≤ K / δ * Real.log (|z.im| + 3) := by
  obtain ⟨Ks, hKs⟩ := norm_negLogDerivZeta_le_of_sep hZ1 hZ2 hZ3
  refine ⟨max Ks 0, le_max_right _ _, fun z h1 h2 h3 h4 δ hδ hδ1 hsep => ?_⟩
  refine (hKs z h1 h2 h3 h4 δ hδ hδ1 hsep).trans ?_
  have : 0 ≤ Real.log (|z.im| + 3) := Real.log_nonneg (by linarith [abs_nonneg z.im])
  gcongr
  exact le_max_left _ _

end GoldbachBoundaries.Paper2.M5
