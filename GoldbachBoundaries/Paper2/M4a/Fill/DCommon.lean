import GoldbachBoundaries.Paper2.M4a.Order

/-!
# M4a filler group D (kernel bounds): shared helpers

Helpers for `norm_inv_Gamma_le`, `norm_KerS_le_kernelt`, `integral_kernelt_le` and `K2_kr` (`Kernel.lean`).
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M4a

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

namespace FillD

/-- `‖sin z‖ ≤ e^{|Im z|}`. -/
lemma norm_sin_le_exp_abs_im (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  have h : Complex.sin z = (Complex.exp (-z * I) - Complex.exp (z * I)) * I / 2 := rfl
  rw [h, norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_two]
  have h1 : ‖Complex.exp (-z * I)‖ = Real.exp z.im := by rw [Complex.norm_exp]; simp
  have h2 : ‖Complex.exp (z * I)‖ = Real.exp (-z.im) := by rw [Complex.norm_exp]; simp
  have h3 := norm_sub_le (Complex.exp (-z * I)) (Complex.exp (z * I))
  rw [h1, h2] at h3
  have h4 : Real.exp z.im ≤ Real.exp |z.im| := Real.exp_le_exp.2 (le_abs_self _)
  have h5 : Real.exp (-z.im) ≤ Real.exp |z.im| := Real.exp_le_exp.2 (neg_le_abs _)
  linarith

/-- `(1 + u)^a ≤ (1 + u)^b` for `a ≤ b`, `u ≥ 0`. -/
lemma one_add_rpow_le_of_le {u a b : ℝ} (hu : 0 ≤ u) (hab : a ≤ b) : (1 + u) ^ a ≤ (1 + u) ^ b :=
  Real.rpow_le_rpow_of_exponent_le (by linarith) hab

/-- Polynomial against `e^{-πu}`: `(1 + u)^E e^{-πu} ≤ K/(1 + u)²` for `u ≥ 0`. -/
lemma exists_rpow_mul_exp_le (E : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : ℝ, 0 ≤ u →
      (1 + u) ^ E * Real.exp (-(Real.pi * u)) ≤ K / (1 + u) ^ 2 := by
  set n : ℕ := ⌈max E 0⌉₊ + 2 with hn
  refine ⟨n.factorial * Real.exp 1, by positivity, fun u hu => ?_⟩
  have hpos : 0 < 1 + u := by linarith
  rw [le_div_iff₀ (by positivity)]
  have hE : E + 2 ≤ (n : ℝ) := by
    have := Nat.le_ceil (max E 0)
    have : E ≤ max E 0 := le_max_left _ _
    push_cast [hn]; linarith
  have h1 : (1 + u) ^ E * (1 + u) ^ 2 = (1 + u) ^ (E + 2) := by
    rw [Real.rpow_add hpos]; norm_cast
  have h2 : (1 + u) ^ (E + 2) ≤ (1 + u) ^ n := by
    rw [← Real.rpow_natCast]; exact one_add_rpow_le_of_le hu hE
  have h3 : (1 + u) ^ n ≤ n.factorial * Real.exp (1 + u) := by
    have := Real.pow_div_factorial_le_exp (1 + u) hpos.le n
    rw [div_le_iff₀ (by positivity)] at this; linarith
  have h4 : Real.exp (1 + u) * Real.exp (-(Real.pi * u)) ≤ Real.exp 1 := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.2
    nlinarith [Real.pi_gt_three]
  calc (1 + u) ^ E * Real.exp (-(Real.pi * u)) * (1 + u) ^ 2
      = (1 + u) ^ (E + 2) * Real.exp (-(Real.pi * u)) := by rw [← h1]; ring
    _ ≤ n.factorial * Real.exp (1 + u) * Real.exp (-(Real.pi * u)) := by
        apply mul_le_mul_of_nonneg_right (h2.trans h3) (Real.exp_pos _).le
    _ = n.factorial * (Real.exp (1 + u) * Real.exp (-(Real.pi * u))) := by ring
    _ ≤ n.factorial * Real.exp 1 := by gcongr


/-- `‖Γ(w)‖ ≤ ‖Γ(w + n)‖` when `|Im w| ≥ 1` (each factor `|w + j| ≥ |Im w| ≥ 1`). -/
lemma norm_Gamma_le_norm_Gamma_add_nat {w : ℂ} (hw : 1 ≤ |w.im|) (n : ℕ) :
    ‖Gamma w‖ ≤ ‖Gamma (w + n)‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hne : w + n ≠ 0 := by
      intro h
      have h' := congrArg Complex.im h
      simp at h'
      rw [h'] at hw; norm_num at hw
    have hrec : Gamma (w + ↑(n + 1)) = (w + n) * Gamma (w + n) := by
      rw [← Complex.Gamma_add_one _ hne]; push_cast; ring_nf
    rw [hrec, norm_mul]
    have h1 : 1 ≤ ‖w + n‖ := by
      calc (1 : ℝ) ≤ |w.im| := hw
        _ = |(w + n).im| := by simp
        _ ≤ ‖w + n‖ := Complex.abs_im_le_norm _
    nlinarith [norm_nonneg (Gamma (w + n))]

/-- `norm_inv_Gamma_le` with `C ≥ 0` and `A ≥ 0`. -/
lemma norm_inv_Gamma_le' (hZ6 : Z6) {σ₁ σ₂ : ℝ} (h₁ : 0 < σ₁) (h₁₂ : σ₁ ≤ σ₂) :
    ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧ ∀ σ ∈ Icc σ₁ σ₂, ∀ t : ℝ,
      ‖(Gamma (σ + t * I))⁻¹‖ ≤ C * (1 + |t|) ^ A * Real.exp (Real.pi * |t| / 2) := by
  -- `|t| ≤ 1`: compactness
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ σ ∈ Icc σ₁ σ₂, ∀ t ∈ Icc (-1 : ℝ) 1, ‖(Gamma (σ + t * I))⁻¹‖ ≤ M := by
    have hK : IsCompact ((fun p : ℝ × ℝ => (p.1 : ℂ) + p.2 * I) '' (Icc σ₁ σ₂ ×ˢ Icc (-1) 1)) :=
      (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
    obtain ⟨M, hM⟩ :=
      hK.exists_bound_of_continuousOn Complex.differentiable_one_div_Gamma.continuous.continuousOn
    exact ⟨M, fun σ hσ t ht => hM _ ⟨(σ, t), ⟨hσ, ht⟩, rfl⟩⟩
  -- `|t| ≥ 1`: reflection, a shift by `N`, and (Z6)
  set N : ℕ := ⌈σ₂⌉₊ with hNdef
  have hN : σ₂ ≤ N := Nat.le_ceil _
  obtain ⟨C₀, hC₀⟩ := hZ6 (1 - σ₂ + N) (1 - σ₁ + N) (by linarith) (by linarith)
  refine ⟨max M 0 + max C₀ 0 / Real.pi, 1 - σ₁ + N, by positivity, by linarith, fun σ hσ t => ?_⟩
  have hP : (1 : ℝ) ≤ (1 + |t|) ^ (1 - σ₁ + N) :=
    Real.one_le_rpow (by linarith [abs_nonneg t]) (by linarith)
  have hE : (1 : ℝ) ≤ Real.exp (Real.pi * |t| / 2) := Real.one_le_exp (by positivity)
  have hCnn : 0 ≤ max C₀ 0 / Real.pi := by positivity
  rcases le_or_gt |t| 1 with ht | ht
  · have hb := hM σ hσ t (abs_le.1 ht)
    calc ‖(Gamma (σ + t * I))⁻¹‖ ≤ max M 0 := hb.trans (le_max_left _ _)
      _ ≤ (max M 0 + max C₀ 0 / Real.pi) * 1 * 1 := by linarith
      _ ≤ _ := by gcongr
  · set s : ℂ := σ + t * I with hs
    have hsin : Complex.sin (Real.pi * s) ≠ 0 := by
      intro h0
      obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.1 h0
      have h' := congrArg Complex.im hk
      simp [s] at h'
      rw [h'] at ht; norm_num at ht
    have hΓ : Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp [s]; linarith [hσ.1])
    have hpi0 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hrefl : (Gamma s)⁻¹ = Gamma (1 - s) * Complex.sin (Real.pi * s) / Real.pi := by
      have h := Complex.Gamma_mul_Gamma_one_sub s
      have h2 : Gamma s * Gamma (1 - s) * Complex.sin (Real.pi * s) = (Real.pi : ℂ) := by
        rw [h, div_mul_cancel₀ _ hsin]
      calc (Gamma s)⁻¹ = (Gamma s)⁻¹ * (Real.pi : ℂ) / Real.pi := by field_simp
        _ = (Gamma s)⁻¹ * (Gamma s * Gamma (1 - s) * Complex.sin (Real.pi * s)) / Real.pi := by
            rw [h2]
        _ = _ := by field_simp
    have hw : 1 ≤ |(1 - s).im| := by simp [s]; linarith
    have hshift := norm_Gamma_le_norm_Gamma_add_nat hw N
    have heq : 1 - s + N = ((1 - σ + N : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I := by
      simp only [s]; push_cast; ring
    have hZ := hC₀ (1 - σ + N) ⟨by linarith [hσ.2], by linarith [hσ.1]⟩ (-t)
    rw [← heq, abs_neg] at hZ
    have hsinb := norm_sin_le_exp_abs_im (Real.pi * s)
    have him : ((Real.pi : ℂ) * s).im = Real.pi * t := by simp [s]
    rw [him, abs_mul, abs_of_pos Real.pi_pos] at hsinb
    have hpi : ‖(Real.pi : ℂ)‖ = Real.pi := by simp [abs_of_pos Real.pi_pos]
    rw [hrefl, norm_div, norm_mul, hpi]
    set P := (1 + |t|) ^ (1 - σ₁ + N)
    have hG := hshift.trans hZ
    have hexp : Real.exp (-(Real.pi * |t| / 2)) * Real.exp (Real.pi * |t|) =
        Real.exp (Real.pi * |t| / 2) := by rw [← Real.exp_add]; ring_nf
    have hnn : 0 ≤ C₀ * P * Real.exp (-(Real.pi * |t| / 2)) := (norm_nonneg _).trans hG
    calc ‖Gamma (1 - s)‖ * ‖Complex.sin (Real.pi * s)‖ / Real.pi
        ≤ C₀ * P * Real.exp (-(Real.pi * |t| / 2)) * Real.exp (Real.pi * |t|) / Real.pi := by
          gcongr
      _ = C₀ * P * Real.exp (Real.pi * |t| / 2) / Real.pi := by
          rw [mul_assoc (C₀ * P), hexp]
      _ ≤ max C₀ 0 * P * Real.exp (Real.pi * |t| / 2) / Real.pi := by
          gcongr
          exact le_max_left _ _
      _ = max C₀ 0 / Real.pi * P * Real.exp (Real.pi * |t| / 2) := by ring
      _ ≤ (max M 0 + max C₀ 0 / Real.pi) * P * Real.exp (Real.pi * |t| / 2) := by
          gcongr
          linarith [le_max_right M 0]

/-- `norm_KerS_le_kernelt` with `C ≥ 0` and `A ≥ 0`. -/
lemma norm_KerS_le_kernelt' (hZ6 : Z6) {x₁ x₂ σ₁ σ₂ : ℝ} (hx₁ : 0 < x₁) (hx₁₂ : x₁ ≤ x₂)
    (hxσ : x₂ < σ₁) (hσ₁₂ : σ₁ ≤ σ₂) :
    ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧ ∀ x ∈ Icc x₁ x₂, ∀ y : ℝ, ∀ σ ∈ Icc σ₁ σ₂, ∀ t : ℝ,
      ‖KerS (σ + t * I) (x + y * I)‖ ≤ C * (1 + |y|) ^ A * (1 + |t - y|) ^ A * (1 + |t|) ^ A *
        Real.exp (-(Real.pi / 2 * (|y| + |t - y| - |t|))) := by
  obtain ⟨C₁, hC₁⟩ := hZ6 x₁ x₂ hx₁ hx₁₂
  obtain ⟨C₂, hC₂⟩ := hZ6 (σ₁ - x₂) (σ₂ - x₁) (by linarith) (by linarith)
  obtain ⟨C₃, A₃, hC₃, hA₃, hC₃'⟩ := norm_inv_Gamma_le' hZ6 (by linarith : 0 < σ₁) hσ₁₂
  set A := max (max x₂ (σ₂ - x₁)) A₃ with hA
  have hxA : x₂ ≤ A := le_max_of_le_left (le_max_left _ _)
  have hσA : σ₂ - x₁ ≤ A := le_max_of_le_left (le_max_right _ _)
  have hA₃A : A₃ ≤ A := le_max_right _ _
  refine ⟨max C₁ 0 * max C₂ 0 * C₃, A, by positivity, hA₃.trans hA₃A, fun x hx y σ hσ t => ?_⟩
  have h1 := hC₁ x hx y
  have h2 := hC₂ (σ - x) ⟨by linarith [hx.2, hσ.1], by linarith [hx.1, hσ.2]⟩ (t - y)
  have h3 := hC₃' σ hσ t
  have heq : ((σ : ℂ) + t * I) - (x + y * I) = ((σ - x : ℝ) : ℂ) + ((t - y : ℝ) : ℂ) * I := by
    push_cast; ring
  have b1 : ‖Gamma (x + y * I)‖ ≤ max C₁ 0 * (1 + |y|) ^ A * Real.exp (-(Real.pi * |y| / 2)) := by
    refine h1.trans ?_
    gcongr
    · exact le_max_left _ _
    · linarith [abs_nonneg y]
  have b2 : ‖Gamma (((σ - x : ℝ) : ℂ) + ((t - y : ℝ) : ℂ) * I)‖ ≤
      max C₂ 0 * (1 + |t - y|) ^ A * Real.exp (-(Real.pi * |t - y| / 2)) := by
    refine h2.trans ?_
    gcongr
    · exact le_max_left _ _
    · linarith [abs_nonneg (t - y)]
  have b3 : ‖(Gamma (σ + t * I))⁻¹‖ ≤ C₃ * (1 + |t|) ^ A * Real.exp (Real.pi * |t| / 2) := by
    refine h3.trans ?_
    gcongr
    linarith [abs_nonneg t]
  have hexp : Real.exp (-(Real.pi * |y| / 2)) * Real.exp (-(Real.pi * |t - y| / 2)) *
      Real.exp (Real.pi * |t| / 2) = Real.exp (-(Real.pi / 2 * (|y| + |t - y| - |t|))) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  unfold KerS
  rw [div_eq_mul_inv, norm_mul, norm_mul, heq]
  calc _ ≤ (max C₁ 0 * (1 + |y|) ^ A * Real.exp (-(Real.pi * |y| / 2))) *
        (max C₂ 0 * (1 + |t - y|) ^ A * Real.exp (-(Real.pi * |t - y| / 2))) *
        (C₃ * (1 + |t|) ^ A * Real.exp (Real.pi * |t| / 2)) := by gcongr
    _ = max C₁ 0 * max C₂ 0 * C₃ * (1 + |y|) ^ A * (1 + |t - y|) ^ A * (1 + |t|) ^ A *
        (Real.exp (-(Real.pi * |y| / 2)) * Real.exp (-(Real.pi * |t - y| / 2)) *
          Real.exp (Real.pi * |t| / 2)) := by ring
    _ = _ := by rw [hexp]

/-! ### The integral bound of `cl:lem:kernelt` -/

/-- Off the segment between `0` and `t`, one of `|t - y| = |y| + |t|`, `|y| = |t - y| + |t|` holds. -/
lemma abs_cases_of_not_mem_uIcc {y t : ℝ} (hy : y ∉ uIcc 0 t) :
    |t - y| = |y| + |t| ∨ |y| = |t - y| + |t| := by
  rw [Set.mem_uIcc] at hy
  push Not at hy
  rcases le_total 0 y with h1 | h1 <;> rcases le_total 0 t with h2 | h2 <;>
    rcases le_total y t with h3 | h3
  · exact absurd (hy.1 h1) (not_lt.2 h3)
  · right; rw [abs_of_nonneg h1, abs_of_nonneg h2, abs_of_nonpos (by linarith : t - y ≤ 0)]; ring
  · left; rw [abs_of_nonneg h1, abs_of_nonpos h2, abs_of_nonneg (by linarith : 0 ≤ t - y)]; linarith
  · left; rw [abs_of_nonneg h1, abs_of_nonpos h2, abs_of_nonpos (by linarith : t - y ≤ 0)]; ring
  · left; rw [abs_of_nonpos h1, abs_of_nonneg h2, abs_of_nonneg (by linarith : 0 ≤ t - y)]; ring
  · left; rw [abs_of_nonpos h1, abs_of_nonneg h2, abs_of_nonneg (by linarith : 0 ≤ t - y)]; linarith
  · right; rw [abs_of_nonpos h1, abs_of_nonpos h2, abs_of_nonneg (by linarith : 0 ≤ t - y)]; ring
  · exact absurd (hy.2 h3) (not_lt.2 h1)

lemma rpow_mul_rpow_le_of_add_eq {a b c B : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hB : 0 ≤ B) (h : a + b = c) :
    (1 + a) ^ B * (1 + b) ^ B * Real.exp (-(Real.pi / 2 * (a + b - c))) ≤ (1 + c) ^ (2 * B) := by
  have hc : (1 + c) ^ (2 * B) = (1 + c) ^ B * (1 + c) ^ B := by
    rw [two_mul, Real.rpow_add (by linarith)]
  rw [hc, show a + b - c = 0 by linarith, mul_zero, neg_zero, Real.exp_zero, mul_one]
  gcongr <;> first | linarith | exact Real.rpow_nonneg (by linarith) _

lemma rpow_mul_rpow_le_of_eq_add {a b c B : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hB : 0 ≤ B) (h : b = a + c) :
    (1 + a) ^ B * (1 + b) ^ B * Real.exp (-(Real.pi / 2 * (a + b - c))) ≤
      (1 + c) ^ (2 * B) * ((1 + a) ^ (2 * B) * Real.exp (-(Real.pi * a))) := by
  subst h
  have h1 : (1 + (a + c)) ^ B ≤ (1 + a) ^ B * (1 + c) ^ B := by
    rw [← Real.mul_rpow (by linarith) (by linarith)]
    gcongr; nlinarith
  have h2 : (1 + c) ^ B ≤ (1 + c) ^ (2 * B) := one_add_rpow_le_of_le hc (by linarith)
  have h3 : (1 + a) ^ (2 * B) = (1 + a) ^ B * (1 + a) ^ B := by
    rw [two_mul, Real.rpow_add (by linarith)]
  have he : Real.exp (-(Real.pi / 2 * (a + (a + c) - c))) = Real.exp (-(Real.pi * a)) := by ring_nf
  rw [he, h3]
  have hp1 : 0 ≤ (1 + a) ^ B := by positivity
  have hp2 : 0 ≤ (1 + c) ^ B := by positivity
  have hpe := (Real.exp_pos (-(Real.pi * a))).le
  calc (1 + a) ^ B * (1 + (a + c)) ^ B * Real.exp (-(Real.pi * a))
      ≤ (1 + a) ^ B * ((1 + a) ^ B * (1 + c) ^ B) * Real.exp (-(Real.pi * a)) := by gcongr
    _ = (1 + c) ^ B * ((1 + a) ^ B * (1 + a) ^ B * Real.exp (-(Real.pi * a))) := by ring
    _ ≤ _ := by gcongr

/-- The model profile `φ(u) = (1 + |u|)^{2B} e^{-π|u|}`. -/
def phiK (B : ℝ) (u : ℝ) : ℝ := (1 + |u|) ^ (2 * B) * Real.exp (-(Real.pi * |u|))

lemma phiK_nonneg (B u : ℝ) : 0 ≤ phiK B u := by unfold phiK; positivity

lemma continuous_phiK {B : ℝ} (hB : 0 ≤ B) : Continuous (phiK B) := by
  unfold phiK
  exact ((continuous_const.add continuous_abs).rpow_const fun _ => Or.inr (by linarith)).mul
    (by fun_prop)

lemma integrable_phiK {B : ℝ} (hB : 0 ≤ B) : Integrable (phiK B) := by
  obtain ⟨K, hK, hKb⟩ := exists_rpow_mul_exp_le (2 * B)
  refine ((integrable_inv_one_add_sq).const_mul K).mono' (continuous_phiK hB).aestronglyMeasurable
    (ae_of_all _ fun u => ?_)
  rw [Real.norm_of_nonneg (phiK_nonneg B u)]
  refine (hKb |u| (abs_nonneg u)).trans ?_
  rw [div_eq_mul_inv]
  gcongr
  nlinarith [abs_nonneg u, sq_abs u]

/-- The pointwise bound: `f_t(y) ≤ (1 + |t|)^{2B}(φ(y) + φ(y - t) + 1_{[0,t]}(y))`. -/
lemma kernelt_le_pointwise {B : ℝ} (hB : 0 ≤ B) (t y : ℝ) :
    (1 + |y|) ^ B * (1 + |t - y|) ^ B * Real.exp (-(Real.pi / 2 * (|y| + |t - y| - |t|))) ≤
      (1 + |t|) ^ (2 * B) * (phiK B y + phiK B (y - t) + (uIcc 0 t).indicator (fun _ => (1 : ℝ)) y) := by
  have hφ1 := phiK_nonneg B y
  have hφ2 := phiK_nonneg B (y - t)
  have hP : 0 ≤ (1 + |t|) ^ (2 * B) := by positivity
  by_cases hy : y ∈ uIcc 0 t
  · rw [Set.indicator_of_mem hy]
    have hseg : |y| + |t - y| = |t| := by
      rw [Set.mem_uIcc] at hy
      rcases hy with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [abs_of_nonneg h1, abs_of_nonneg (by linarith : 0 ≤ t - y), abs_of_nonneg (by linarith)]
        ring
      · rw [abs_of_nonpos h2, abs_of_nonpos (by linarith : t - y ≤ 0), abs_of_nonpos (by linarith)]
        ring
    refine (rpow_mul_rpow_le_of_add_eq (abs_nonneg _) (abs_nonneg _) hB hseg).trans ?_
    nlinarith
  · rw [Set.indicator_of_notMem hy, add_zero]
    rcases abs_cases_of_not_mem_uIcc hy with h | h
    · refine (rpow_mul_rpow_le_of_eq_add (abs_nonneg _) (abs_nonneg _) hB h).trans ?_
      have : (1 + |t|) ^ (2 * B) * phiK B y = (1 + |t|) ^ (2 * B) *
          ((1 + |y|) ^ (2 * B) * Real.exp (-(Real.pi * |y|))) := rfl
      nlinarith
    · have h' := rpow_mul_rpow_le_of_eq_add (abs_nonneg (t - y)) (abs_nonneg t) hB h
      have : (1 + |t|) ^ (2 * B) * phiK B (y - t) = (1 + |t|) ^ (2 * B) *
          ((1 + |t - y|) ^ (2 * B) * Real.exp (-(Real.pi * |t - y|))) := by
        rw [phiK, abs_sub_comm]
      rw [mul_comm ((1 + |y|) ^ B), add_comm |y|]
      nlinarith

/-- `integral_kernelt_le`, for fixed `B ≥ 0`. -/
lemma integral_kernelt_le' {B : ℝ} (hB : 0 ≤ B) : ∃ C : ℝ, ∀ t : ℝ,
    Integrable (fun y : ℝ => (1 + |y|) ^ B * (1 + |t - y|) ^ B *
      Real.exp (-(Real.pi / 2 * (|y| + |t - y| - |t|)))) ∧
    ∫ y : ℝ, (1 + |y|) ^ B * (1 + |t - y|) ^ B * Real.exp (-(Real.pi / 2 * (|y| + |t - y| - |t|))) ≤
      C * (1 + |t|) ^ (2 * B + 1) := by
  set I₀ := ∫ u, phiK B u with hI₀
  have hI₀nn : 0 ≤ I₀ := integral_nonneg (phiK_nonneg B)
  refine ⟨2 * I₀ + 1, fun t => ?_⟩
  set f := fun y : ℝ => (1 + |y|) ^ B * (1 + |t - y|) ^ B *
      Real.exp (-(Real.pi / 2 * (|y| + |t - y| - |t|))) with hf
  set g := fun y : ℝ => (1 + |t|) ^ (2 * B) *
      (phiK B y + phiK B (y - t) + (uIcc 0 t).indicator (fun _ => (1 : ℝ)) y) with hg
  have hφ := integrable_phiK hB
  have hind : Integrable ((uIcc 0 t).indicator (fun _ => (1 : ℝ))) :=
    (continuous_const.integrableOn_uIcc).integrable_indicator measurableSet_uIcc
  have hgi : Integrable g := ((hφ.add (hφ.comp_sub_right t)).add hind).const_mul _
  have hfc : Continuous f := by
    have hc1 : Continuous fun y : ℝ => (1 + |y|) ^ B :=
      (continuous_const.add continuous_abs).rpow_const fun _ => Or.inr hB
    have hc2 : Continuous fun y : ℝ => (1 + |t - y|) ^ B :=
      (continuous_const.add (continuous_const.sub continuous_id).abs).rpow_const fun _ => Or.inr hB
    exact (hc1.mul hc2).mul (by fun_prop)
  have hfnn : ∀ y, 0 ≤ f y := fun y => by simp only [hf]; positivity
  have hfg : ∀ y, f y ≤ g y := fun y => kernelt_le_pointwise hB t y
  have hfi : Integrable f := hgi.mono' hfc.aestronglyMeasurable
    (ae_of_all _ fun y => by rw [Real.norm_of_nonneg (hfnn y)]; exact hfg y)
  refine ⟨hfi, ?_⟩
  have hgint : ∫ y, g y = (1 + |t|) ^ (2 * B) * (I₀ + I₀ + |t|) := by
    have h12 : Integrable (fun a => phiK B a + phiK B (a - t)) := hφ.add (hφ.comp_sub_right t)
    simp only [hg]
    rw [integral_const_mul, integral_add h12 hind,
      integral_add hφ (hφ.comp_sub_right t), integral_sub_right_eq_self (phiK B) t,
      integral_indicator_const _ measurableSet_uIcc, smul_eq_mul, mul_one, measureReal_def,
      Real.volume_interval, ENNReal.toReal_ofReal (abs_nonneg _), sub_zero]
  have hP : 0 ≤ (1 + |t|) ^ (2 * B) := by positivity
  have hsplit : (1 + |t|) ^ (2 * B + 1) = (1 + |t|) ^ (2 * B) * (1 + |t|) := by
    rw [Real.rpow_add (by positivity), Real.rpow_one]
  calc ∫ y, f y ≤ ∫ y, g y := integral_mono hfi hgi hfg
    _ = (1 + |t|) ^ (2 * B) * (I₀ + I₀ + |t|) := hgint
    _ ≤ (2 * I₀ + 1) * (1 + |t|) ^ (2 * B + 1) := by
        rw [hsplit]
        have : I₀ + I₀ + |t| ≤ (2 * I₀ + 1) * (1 + |t|) := by nlinarith [abs_nonneg t]
        nlinarith

/-! ### (K2) for `k_r` -/

/-- `K2 Aff.idL (kr r)`. -/
lemma K2_kr' (hZ6 : Z6) (r : ℕ) : K2 Aff.idL (kr r) := by
  intro C hC _ x₁ x₂ hx₁ hx₁₂ hre
  rcases C.eq_empty_or_nonempty with hCe | hne
  · exact ⟨0, fun x _ s hs => absurd hs (by rw [hCe]; exact Set.notMem_empty s)⟩
  simp only [app_idL] at hre
  obtain ⟨s₀, hs₀, hmin⟩ := hC.exists_isMinOn hne Complex.continuous_re.continuousOn
  obtain ⟨R, hR⟩ := hC.isBounded.exists_norm_le
  have hσ₁ : x₂ < s₀.re := hre s₀ hs₀
  have hσ₁R : s₀.re ≤ R := (Complex.re_le_norm s₀).trans (hR s₀ hs₀)
  have hR0 : 0 ≤ R := (norm_nonneg _).trans (hR s₀ hs₀)
  obtain ⟨C₁, A, hC₁, hA, hK⟩ := norm_KerS_le_kernelt' hZ6 hx₁ hx₁₂ hσ₁ hσ₁R
  obtain ⟨K, hK0, hKb⟩ := exists_rpow_mul_exp_le (2 * A + 2 * r)
  have hx₂ : 0 ≤ x₂ := by linarith
  set c₁ : ℝ := (1 + x₂) * (2 * R + 1 + x₂) with hc₁
  have hc₁0 : 0 ≤ c₁ := by positivity
  set D : ℝ := C₁ * (1 + R) ^ A * (1 + R) ^ A * Real.exp (Real.pi * R) * c₁ ^ r with hD
  have hD0 : 0 ≤ D := by positivity
  refine ⟨D * K, fun x hx s hs y => ?_⟩
  set u : ℝ := |y| with hu
  have hu0 : 0 ≤ u := abs_nonneg y
  have hsn : ‖s‖ ≤ R := hR s hs
  have hσ : s.re ∈ Icc s₀.re R := ⟨hmin hs, (Complex.re_le_norm s).trans hsn⟩
  have ht : |s.im| ≤ R := (Complex.abs_im_le_norm s).trans hsn
  have hsre : |s.re| ≤ R := (Complex.abs_re_le_norm s).trans hsn
  have hseq : s = (s.re : ℂ) + (s.im : ℂ) * I := (Complex.re_add_im s).symm
  -- the kernel factor
  have hk := hK x hx y s.re hσ s.im
  rw [← hseq] at hk
  set t := s.im with htdef
  have hty : 1 + |t - y| ≤ (1 + R) * (1 + u) := by
    have := abs_sub (t) y
    nlinarith [abs_nonneg t]
  have hb1 : (1 + |t - y|) ^ A ≤ (1 + R) ^ A * (1 + u) ^ A := by
    rw [← Real.mul_rpow (by linarith) (by linarith)]
    exact Real.rpow_le_rpow (by positivity) hty hA
  have hb2 : (1 + |t|) ^ A ≤ (1 + R) ^ A := Real.rpow_le_rpow (by positivity) (by linarith) hA
  have hb3 : Real.exp (-(Real.pi / 2 * (|y| + |t - y| - |t|))) ≤
      Real.exp (Real.pi * R) * Real.exp (-(Real.pi * u)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have h1 : |y| - |t| ≤ |t - y| := by
      have := abs_sub_abs_le_abs_sub y t; rw [abs_sub_comm] at this; linarith
    have hpi := Real.pi_pos
    nlinarith
  have hKer : ‖KerS s (x + y * I)‖ ≤ C₁ * (1 + R) ^ A * (1 + R) ^ A * Real.exp (Real.pi * R) *
      ((1 + u) ^ A * (1 + u) ^ A * Real.exp (-(Real.pi * u))) := by
    refine hk.trans ?_
    have hp1 : 0 ≤ (1 + u) ^ A := by positivity
    calc C₁ * (1 + |y|) ^ A * (1 + |t - y|) ^ A * (1 + |t|) ^ A *
          Real.exp (-(Real.pi / 2 * (|y| + |t - y| - |t|)))
        ≤ C₁ * (1 + u) ^ A * ((1 + R) ^ A * (1 + u) ^ A) * (1 + R) ^ A *
          (Real.exp (Real.pi * R) * Real.exp (-(Real.pi * u))) := by gcongr
      _ = _ := by ring
  -- the polynomial factor
  have hz1 : ‖(x + y * I : ℂ) - 1‖ ≤ (1 + x₂) * (1 + u) := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp only [sub_re, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, add_zero, one_re, sub_im, add_im, mul_im, zero_add, one_im, sub_zero]
    have : |x - 1| ≤ 1 + x₂ := abs_le.2 ⟨by linarith [hx.1], by linarith [hx.2]⟩
    nlinarith
  have hz2 : ‖s - 1 - (x + y * I : ℂ)‖ ≤ (2 * R + 1 + x₂) * (1 + u) := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp only [sub_re, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, add_zero, one_re, sub_im, add_im, mul_im, zero_add, one_im, sub_zero]
    have h1 : |s.re - 1 - x| ≤ R + 1 + x₂ := by
      rw [abs_le] at hsre ⊢; constructor <;> linarith [hx.1, hx.2]
    have h2 : |s.im - y| ≤ R + u := (abs_sub _ _).trans (by linarith)
    nlinarith
  have hpoly : ‖((x + y * I : ℂ) - 1) * (s - 1 - (x + y * I))‖ ^ r ≤ c₁ ^ r * (1 + u) ^ (2 * r) := by
    rw [norm_mul, pow_mul, ← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    calc ‖(x + y * I : ℂ) - 1‖ * ‖s - 1 - (x + y * I)‖
        ≤ ((1 + x₂) * (1 + u)) * ((2 * R + 1 + x₂) * (1 + u)) := by gcongr
      _ = c₁ * (1 + u) ^ 2 := by ring
  -- combine
  have hcomb : (1 + u) ^ A * (1 + u) ^ A * (1 + u) ^ (2 * r) = (1 + u) ^ (2 * A + 2 * r) := by
    have h1u : 0 < 1 + u := by linarith
    rw [← Real.rpow_add h1u, ← Real.rpow_natCast, ← Real.rpow_add h1u]
    congr 1; push_cast; ring
  have hfin := hKb u hu0
  unfold kr
  rw [norm_mul, norm_pow]
  have hpe : 0 ≤ (1 + u) ^ A * (1 + u) ^ A * Real.exp (-(Real.pi * u)) := by positivity
  calc ‖KerS s (x + y * I)‖ * ‖((x + y * I : ℂ) - 1) * (s - 1 - (x + y * I))‖ ^ r
      ≤ (C₁ * (1 + R) ^ A * (1 + R) ^ A * Real.exp (Real.pi * R) *
          ((1 + u) ^ A * (1 + u) ^ A * Real.exp (-(Real.pi * u)))) * (c₁ ^ r * (1 + u) ^ (2 * r)) := by
        gcongr
    _ = D * ((1 + u) ^ A * (1 + u) ^ A * (1 + u) ^ (2 * r) * Real.exp (-(Real.pi * u))) := by
        rw [hD]; ring
    _ = D * ((1 + u) ^ (2 * A + 2 * r) * Real.exp (-(Real.pi * u))) := by rw [hcomb]
    _ ≤ D * (K / (1 + u) ^ 2) := by gcongr
    _ = D * K / (1 + |y|) ^ 2 := by rw [hu]; ring

end FillD

end GoldbachBoundaries.Paper2.M4a
