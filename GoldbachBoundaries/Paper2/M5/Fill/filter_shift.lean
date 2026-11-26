import GoldbachBoundaries.Paper2.M5.FilterI
import GoldbachBoundaries.Paper2.M5.Fill.filter_rect
import GoldbachBoundaries.Paper2.M5.Fill.filter_rect_limit
import GoldbachBoundaries.Paper2.M5.Fill.norm_resTerm_le

/-!
# Fill: `filter_shift`

Summability: `‖resTerm‖ ≤ μ/η` (`norm_resTerm_le`). The identity: fix `ε > 0`. `HasSum` gives a finite set `u₀` of
zeros with `‖∑_v resTerm - ∑' resTerm‖ < ε` for every finite `v ⊇ u₀`; `filter_rect_limit` (with the constant `C` of
`Qleft_ii`) gives `Y₀`. For `Y ≥ max(3, Y₀, Y₁)` (`Y₁` above every `|γ|`, `ρ ∈ u₀`) `Qleft_ii` provides a good height
`Y' ∈ [Y, Y + 1]` with `|Qcont(x ± iY')| ≤ C log² Y ≤ C log² Y'`; `filter_rect` writes the rectangle as
`midTerm + ∑_{|γ| < Y'} resTerm`, and `{|γ| < Y'} ⊇ u₀`. So `‖(Fil - J) - (midTerm + ∑' resTerm)‖ < 2ε`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

theorem filter_shift (hRH : RiemannHypothesis) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (H : MvPolynomial (Fin 2) ℂ)
    (hHs : ∀ z w, evalH H z w = evalH H w z) (hH1 : ∀ w, evalH H 1 w = 0) {τ₀ η : ℝ} (hη : 0 < η)
    (hη' : η ≤ 1 / 4) :
    Summable (fun ρ : NontrivialZeros => resTerm H (1 + τ₀ * I + η) ρ) ∧
      Fil H (1 + τ₀ * I + η) = Jfil H (1 + τ₀ * I + η) + midTerm H (1 + τ₀ * I + η) +
        ∑' ρ : NontrivialZeros, resTerm H (1 + τ₀ * I + η) ρ := by
  classical
  set s : ℂ := 1 + τ₀ * I + η with hs
  obtain ⟨μ, hμ, hμb⟩ := norm_resTerm_le hRH hZ1 hZ2 hZ3 H τ₀
  have hsum : Summable (fun ρ : NontrivialZeros => resTerm H s ρ) := by
    refine Summable.of_norm_bounded (hμ.div_const η) (fun ρ => ?_)
    have h := hμb η hη hη' ρ
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hη.le] at h
    rw [le_div_iff₀ hη, mul_comm]
    exact h
  refine ⟨hsum, ?_⟩
  set Tot : ℂ := ∑' ρ : NontrivialZeros, resTerm H s ρ with hTot
  obtain ⟨C, hC⟩ := Qleft_ii hRH hZ1 hZ2 hZ3
  suffices h : ∀ ε > 0, ‖(Fil H s - Jfil H s) - (midTerm H s + Tot)‖ < 2 * ε by
    have h0 : (Fil H s - Jfil H s) - (midTerm H s + Tot) = 0 := by
      by_contra hne
      have hpos := norm_pos_iff.mpr hne
      have := h (‖(Fil H s - Jfil H s) - (midTerm H s + Tot)‖ / 2) (by positivity)
      linarith
    linear_combination h0
  intro ε hε
  obtain ⟨Y₀, hY₀⟩ := filter_rect_limit hRH hZ1 hZ2 hZ3 H hHs hH1 hη hη' C ε hε
  obtain ⟨u₀, hu₀⟩ := (Metric.tendsto_atTop.mp hsum.hasSum) ε hε
  set Y₁ : ℝ := ∑ ρ ∈ u₀, |(ρ : ℂ).im| + 1 with hY₁
  set Y : ℝ := max (max 3 Y₀) Y₁ with hY
  have hY3 : 3 ≤ Y := (le_max_left _ _).trans (le_max_left _ _)
  have hYY₀ : Y₀ ≤ Y := (le_max_right _ _).trans (le_max_left _ _)
  have hYY₁ : Y₁ ≤ Y := le_max_right _ _
  obtain ⟨Y', hY'mem, hY'⟩ := hC Y hY3
  have hY'Y : Y ≤ Y' := hY'mem.1
  have hY'pos : 0 < Y' := by linarith
  have hgood : GoodY Y' := fun x hx => ⟨(hY' x hx).1, (hY' x hx).2.1⟩
  have hlogY : 0 < Real.log Y := Real.log_pos (by linarith)
  have hC0 : 0 ≤ C := by
    have h1 := (hY' 1 ⟨by norm_num, le_rfl⟩).2.2.1
    have h2 := norm_nonneg (Qcont ((1 : ℝ) + Y' * I))
    by_contra hneg
    replace hneg := lt_of_not_ge hneg
    have : C * Real.log Y ^ 2 < 0 := mul_neg_of_neg_of_pos hneg (by positivity)
    linarith
  have hlogle : Real.log Y ^ 2 ≤ Real.log Y' ^ 2 :=
    pow_le_pow_left₀ hlogY.le (Real.log_le_log (by linarith) hY'Y) 2
  have hbound : ∀ x ∈ Icc (1 / 3 : ℝ) 1, ‖Qcont (x + Y' * I)‖ ≤ C * Real.log Y' ^ 2 ∧
      ‖Qcont (x - Y' * I)‖ ≤ C * Real.log Y' ^ 2 := by
    intro x hx
    obtain ⟨-, -, h1, h2⟩ := hY' x hx
    have h3 : C * Real.log Y ^ 2 ≤ C * Real.log Y' ^ 2 := mul_le_mul_of_nonneg_left hlogle hC0
    exact ⟨h1.trans h3, h2.trans h3⟩
  have hlim := hY₀ Y' (hYY₀.trans hY'Y) hbound
  obtain ⟨hfin, hrect⟩ := filter_rect hRH H hη hη' hY'pos hgood
  -- the finite sum as a `Finset` sum over the subtype
  set v : Finset NontrivialZeros := hfin.toFinset.subtype (· ∈ NontrivialZeros) with hv
  have hvsum : ∑ᶠ ρ ∈ {ρ : ℂ | ρ ∈ NontrivialZeros ∧ |ρ.im| < Y'}, resTerm H s ρ =
      ∑ ρ ∈ v, resTerm H s ρ := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin, hv,
      Finset.sum_subtype_of_mem (fun ρ => resTerm H s ρ) (p := (· ∈ NontrivialZeros))]
    intro x hx
    exact ((hfin.mem_toFinset).mp hx).1
  have hu₀v : u₀ ≤ v := by
    intro ρ hρ
    rw [hv, Finset.mem_subtype, hfin.mem_toFinset]
    refine ⟨ρ.2, ?_⟩
    have h1 : |(ρ : ℂ).im| ≤ ∑ ρ ∈ u₀, |(ρ : ℂ).im| :=
      Finset.single_le_sum (f := fun ρ : NontrivialZeros => |(ρ : ℂ).im|) (fun _ _ => abs_nonneg _) hρ
    linarith
  have hvT : dist (∑ ρ ∈ v, resTerm H s ρ) Tot < ε := hu₀ v hu₀v
  rw [dist_eq_norm] at hvT
  rw [hvsum] at hrect
  calc ‖(Fil H s - Jfil H s) - (midTerm H s + Tot)‖
      = ‖-(RectangleIntegral' (gH H s) (((2 / 5 : ℝ) : ℂ) - I * Y') ((((1 + η) / 2 : ℝ) : ℂ) + I * Y') -
            (Fil H s - Jfil H s)) + (∑ ρ ∈ v, resTerm H s ρ - Tot)‖ := by
        rw [hrect]; congr 1; ring
    _ ≤ ‖RectangleIntegral' (gH H s) (((2 / 5 : ℝ) : ℂ) - I * Y') ((((1 + η) / 2 : ℝ) : ℂ) + I * Y') -
            (Fil H s - Jfil H s)‖ + ‖∑ ρ ∈ v, resTerm H s ρ - Tot‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_neg]
    _ < ε + ε := add_lt_add hlim hvT
    _ = 2 * ε := by ring

end GoldbachBoundaries.Paper2.M5
