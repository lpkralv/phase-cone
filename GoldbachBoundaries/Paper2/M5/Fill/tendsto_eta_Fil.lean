import GoldbachBoundaries.Paper2.M5.Fill.F3Common
import GoldbachBoundaries.Paper2.M5.Fill.differentiableOn_Jfil
import GoldbachBoundaries.Paper2.M5.Fill.filter_shift
import GoldbachBoundaries.Paper2.M5.Fill.norm_resTerm_le
import GoldbachBoundaries.Paper2.M5.Fill.tendsto_eta_midTerm
import GoldbachBoundaries.Paper2.M5.Fill.tendsto_eta_resTerm

/-!
# Fill, group F3: `tendsto_eta_Fil`

On `0 < η ≤ 1/4` (eventually in `𝓝[>] 0`), `η Fil = η J + η midTerm + ∑' η resTerm` (`filter_shift`, `tsum_mul_left`).
`η J(s₀ + η) → 0` (`J` is continuous at `s₀`, `differentiableOn_Jfil`, `Re s₀ = 1`); `η midTerm → midLim`
(`tendsto_eta_midTerm`); `∑' η resTerm → ∑' limTerm` by `tendsto_tsum_of_dominated_convergence` with the majorant of
`norm_resTerm_le` and the termwise limits `tendsto_eta_resTerm`. `‖limTerm ρ‖ ≤ μ ρ` (`le_of_tendsto`) gives summability.
The skeleton lemmas are used by name.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

theorem tendsto_eta_Fil (hRH : RiemannHypothesis) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3)
    (H : MvPolynomial (Fin 2) ℂ)
    (hHs : ∀ z w, evalH H z w = evalH H w z) (hH1 : ∀ w, evalH H 1 w = 0) {τ₀ : ℝ}
    (hτ : ∀ ρ ∈ NontrivialZeros, ρ.im ≠ τ₀) :
    Summable (fun ρ : NontrivialZeros => limTerm H τ₀ ρ) ∧
      Tendsto (fun η : ℝ => (η : ℂ) * Fil H (1 + τ₀ * I + η)) (𝓝[>] 0)
        (𝓝 (midLim H τ₀ + ∑' ρ : NontrivialZeros, limTerm H τ₀ ρ)) := by
  set s₀ : ℂ := 1 + τ₀ * I with hs₀
  obtain ⟨μ, hμs, hμ⟩ := norm_resTerm_le hRH hZ1 hZ2 hZ3 H τ₀
  have hres : ∀ ρ : NontrivialZeros,
      Tendsto (fun η : ℝ => (η : ℂ) * resTerm H (s₀ + η) ρ) (𝓝[>] 0) (𝓝 (limTerm H τ₀ ρ)) :=
    fun ρ => tendsto_eta_resTerm hRH H ρ.2 (hτ ρ ρ.2)
  have hev : ∀ᶠ η : ℝ in 𝓝[>] 0, 0 < η ∧ η ≤ 1 / 4 := by
    have : Ioo (0 : ℝ) (1 / 4) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by norm_num)
    filter_upwards [this] with η hη using ⟨hη.1, hη.2.le⟩
  have hbound : ∀ᶠ η : ℝ in 𝓝[>] 0, ∀ ρ : NontrivialZeros,
      ‖(η : ℂ) * resTerm H (s₀ + η) ρ‖ ≤ μ ρ := by
    filter_upwards [hev] with η hη using hμ η hη.1 hη.2
  have hlimle : ∀ ρ : NontrivialZeros, ‖limTerm H τ₀ ρ‖ ≤ μ ρ := fun ρ =>
    le_of_tendsto (hres ρ).norm (hbound.mono fun η h => h ρ)
  have hsum : Summable (fun ρ : NontrivialZeros => limTerm H τ₀ ρ) :=
    Summable.of_norm_bounded hμs hlimle
  refine ⟨hsum, ?_⟩
  have hT := tendsto_tsum_of_dominated_convergence hμs hres hbound
  -- `η J → 0`
  have hU : IsOpen {s : ℂ | 9 / 10 < s.re ∧ s.re < 7 / 5} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt Complex.continuous_re continuous_const)
  have hs₀U : s₀ ∈ {s : ℂ | 9 / 10 < s.re ∧ s.re < 7 / 5} := by
    show 9 / 10 < s₀.re ∧ s₀.re < 7 / 5
    simp only [hs₀, add_re, one_re, mul_re, ofReal_re, ofReal_im, I_re, I_im, mul_zero, mul_one, sub_zero,
      add_zero]
    norm_num
  have hJc : ContinuousAt (Jfil H) s₀ :=
    ((differentiableOn_Jfil hRH hZ1 hZ2 hZ3 H).differentiableAt (hU.mem_nhds hs₀U)).continuousAt
  have hJ : Tendsto (fun η : ℝ => (η : ℂ) * Jfil H (s₀ + η)) (𝓝[>] 0) (𝓝 0) := by
    simpa using F3_tendsto_ofReal.mul (F3_tendsto_comp_shift hJc)
  have hmid := tendsto_eta_midTerm hRH H hτ
  have hall := (hJ.add hmid).add hT
  rw [zero_add] at hall
  refine hall.congr' ?_
  filter_upwards [hev] with η hη
  obtain ⟨_, hshift⟩ := filter_shift hRH hZ1 hZ2 hZ3 H hHs hH1 (τ₀ := τ₀) hη.1 hη.2
  rw [hshift, tsum_mul_left]
  ring

end GoldbachBoundaries.Paper2.M5
