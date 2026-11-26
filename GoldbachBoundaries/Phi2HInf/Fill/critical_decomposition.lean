import GoldbachBoundaries.Phi2HInf.Fill.pairCat_geometry
import GoldbachBoundaries.Phi2HInf.Fill.summable_norm_zeroCoef_hinf

/-! Absolute convergence permits the critical/exceptional partition on HH. -/
noncomputable section
open Complex Filter Topology Set Metric
namespace GoldbachBoundaries.Phi2HInf
open GoldbachBoundaries Paper2 Phi2Proof

/-- Even at a candidate pole the totalized terms have an absolutely summable series. -/
theorem summable_norm_pairTerm_hinf (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2)
    (hStir : StirlingStrip) {s : ℂ} (hs : s ∈ HH) :
    Summable (fun p : NontrivialZeros × NontrivialZeros =>
      ‖zeroCoef p.1 * zeroCoef p.2 / (s - p.1 - p.2)‖) := by
  have ha := summable_norm_zeroCoef_hinf hZ1 hZ2 hStir
  have hp := Summable.mul_norm (f := fun ρ : NontrivialZeros => zeroCoef ρ)
    (g := fun ρ : NontrivialZeros => zeroCoef ρ) ha ha
  obtain ⟨E, d, hd, hbound⟩ := pairCat_denominator_bound hH isCompact_singleton
    (show ({s} : Set ℂ) ⊆ HH by simpa)
  apply (hp.div_const d).of_norm_bounded_eventually
  have hev : ∀ᶠ p in cofinite, p ∉ E := E.finite_toSet.compl_mem_cofinite
  filter_upwards [hev] with p hpE
  rw [Real.norm_of_nonneg (norm_nonneg _), norm_div]
  exact div_le_div_of_nonneg_left (norm_nonneg _) hd (hbound s (mem_singleton _) p hpE)

/-- Equation (20) holds on HH only; W alone extends to the larger half-plane. -/
theorem critical_decomposition (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hStir : StirlingStrip) :
    EqOn Phi2cHInf (fun s => W s + criticalC s / Gamma s) HH := by
  classical
  intro s hs
  let P : Set (NontrivialZeros × NontrivialZeros) :=
    {p | (p.1 : ℂ).re = 1 / 2 ∧ (p.2 : ℂ).re = 1 / 2}
  let f (p : NontrivialZeros × NontrivialZeros) : ℂ :=
    zeroCoef p.1 * zeroCoef p.2 / (s - p.1 - p.2)
  let e : (CriticalZero × CriticalZero) ≃ P :=
    { toFun := fun p => ⟨(p.1.1, p.2.1), p.1.2, p.2.2⟩
      invFun := fun p => (⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2⟩)
      left_inv := fun p => by rfl
      right_inv := fun p => by rfl }
  let eE : ↥(Pᶜ) ≃ {p : NontrivialZeros × NontrivialZeros //
      (p.1 : ℂ).re ≠ 1 / 2 ∨ (p.2 : ℂ).re ≠ 1 / 2} :=
    Equiv.subtypeEquivRight (fun p => not_and_or)
  have hcc : criticalC s = ∑' p : P, f p.1 := e.tsum_eq (fun p : P => f p.1)
  have hexc : (∑' p : ↥(Pᶜ), f p.1) = exceptionalC s :=
    eE.tsum_eq (fun p => f p.1)
  have hsum : Summable f := (summable_norm_pairTerm_hinf hH hZ1 hZ2 hStir hs).of_norm
  have hsplit : criticalC s + exceptionalC s = C s := by
    rw [hcc, ← hexc]
    exact hsum.tsum_subtype_add_tsum_subtype_compl P
  unfold Phi2cHInf W
  rw [← hsplit]
  ring

end GoldbachBoundaries.Phi2HInf
