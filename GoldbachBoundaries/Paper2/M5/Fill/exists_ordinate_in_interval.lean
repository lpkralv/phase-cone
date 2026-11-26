import GoldbachBoundaries.Paper2.M5.FilterII

/-!
# Filler F4: `exists_ordinate_in_interval`

Littlewood's theorem (`ZLittlewood`) puts an ordinate in every interval of length `ℓ` far out: `log log log t → ∞`, so
eventually `a / log log log t < ℓ/2`, and the theorem applied at the centre `t + ℓ/2` of `(t, t + ℓ)` gives the ordinate.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

theorem exists_ordinate_in_interval (hL : ZLittlewood) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∃ Y₀ : ℝ, ∀ t : ℝ, Y₀ ≤ t → ∃ ρ ∈ NontrivialZeros, t < ρ.im ∧ ρ.im < t + ℓ := by
  obtain ⟨a, ha⟩ := hL
  have hlog3 : Tendsto (fun t : ℝ => Real.log (Real.log (Real.log t))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop)
  have hdiv : Tendsto (fun t : ℝ => a / Real.log (Real.log (Real.log t))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog3
  have hsmall : ∀ᶠ t in atTop, a / Real.log (Real.log (Real.log t)) < ℓ / 2 :=
    hdiv.eventually (gt_mem_nhds (by linarith))
  obtain ⟨Y, hY⟩ := eventually_atTop.mp (ha.and hsmall)
  refine ⟨Y, fun t ht => ?_⟩
  obtain ⟨⟨ρ, hρ, hlt⟩, hs⟩ := hY (t + ℓ / 2) (by linarith)
  have h := lt_trans hlt hs
  rw [abs_lt] at h
  exact ⟨ρ, hρ, by linarith [h.1], by linarith [h.2]⟩

end GoldbachBoundaries.Paper2.M5
