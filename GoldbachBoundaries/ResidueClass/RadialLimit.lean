import GoldbachBoundaries.ResidueClass.CauchySquare

/-! # Radial limits of the binary Cauchy series -/

noncomputable section

open Complex Filter Set Topology

namespace GoldbachBoundaries.ResidueClass

variable {q : ℕ} [NeZero q]

/-- The ordered representations of a boundary ordinate as a sum. -/
def pairFibre (q : ℕ) [NeZero q] (τ : ℝ) : Set (OrdinatePair q) :=
  {p | (p.1 : ℝ) + (p.2 : ℝ) = τ}

/-- The summed coefficient at a boundary point. -/
def pairResidue (q : ℕ) [NeZero q] (τ : ℝ) : ℂ :=
  ∑' p : pairFibre q τ, pairWeight q p.1

theorem pairPoint_eq_iff (p : OrdinatePair q) (τ : ℝ) :
    pairPoint q p = 1 + (τ : ℂ) * I ↔ p ∈ pairFibre q τ := by
  constructor
  · intro h
    simpa [pairFibre] using congrArg Complex.im h
  · intro hp
    change (p.1 : ℝ) + (p.2 : ℝ) = τ at hp
    apply Complex.ext <;> simp [hp]

/-- The radial limit exists at every point and equals the sum over its exact
ordered representations. The absolute Gamma-weight sum dominates the limit. -/
theorem tendsto_radial_cauchySquare (hGRH : GRH q) (τ : ℝ) :
    Tendsto (fun η : ℝ ↦ (η : ℂ) * cauchySquare q (1 + τ * I + η))
      (𝓝[>] 0) (𝓝 (pairResidue q τ)) := by
  classical
  let z : ℂ := 1 + (τ : ℂ) * I
  let F (η : ℝ) (p : OrdinatePair q) := (η : ℂ) * (pairWeight q p / (z + η - pairPoint q p))
  let L (p : OrdinatePair q) := if p ∈ pairFibre q τ then pairWeight q p else 0
  have hη : Tendsto (fun η : ℝ ↦ (η : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (Complex.continuous_ofReal.tendsto 0).mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have hlim (p : OrdinatePair q) :
      Tendsto (fun η : ℝ ↦ F η p) (𝓝[>] 0) (𝓝 (L p)) := by
    by_cases hp : p ∈ pairFibre q τ
    · have he : pairPoint q p = z := (pairPoint_eq_iff p τ).mpr hp
      have hev : (fun η : ℝ ↦ F η p) =ᶠ[𝓝[>] 0] fun _ ↦ pairWeight q p := by
        filter_upwards [self_mem_nhdsWithin] with η hpos
        dsimp [F]
        rw [he, add_sub_cancel_left]
        exact mul_div_cancel₀ _ (ofReal_ne_zero.mpr (ne_of_gt hpos))
      simpa only [L, ite_eq_left hp] using tendsto_const_nhds.congr' hev.symm
    · have hn : z - pairPoint q p ≠ 0 :=
        sub_ne_zero.mpr fun he ↦ hp ((pairPoint_eq_iff p τ).mp he.symm)
      have hd : Tendsto (fun η : ℝ ↦ z + η - pairPoint q p) (𝓝[>] 0)
          (𝓝 (z - pairPoint q p)) := by
        simpa using ((tendsto_const_nhds (x := z)).add hη).sub_const (pairPoint q p)
      simpa only [F, L, ite_eq_right hp, zero_mul, Pi.div_apply] using
        hη.mul ((tendsto_const_nhds (x := pairWeight q p)).div hd hn)
  have hbound : ∀ᶠ η : ℝ in 𝓝[>] 0, ∀ p, ‖F η p‖ ≤ ‖pairWeight q p‖ := by
    filter_upwards [self_mem_nhdsWithin] with η hη' p
    have hη₀ : 0 < η := hη'
    have hnorm : η ≤ ‖z + (η : ℂ) - pairPoint q p‖ := by
      have h := re_le_norm (z + (η : ℂ) - pairPoint q p)
      simpa [z] using h
    have hp : 0 < ‖z + (η : ℂ) - pairPoint q p‖ := hη₀.trans_le hnorm
    dsimp [F]
    rw [norm_mul, norm_div, norm_real, Real.norm_of_nonneg hη₀.le,
      mul_div_assoc', div_le_iff₀ hp]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right hnorm (norm_nonneg (pairWeight q p))
  have h := tendsto_tsum_of_dominated_convergence (summable_norm_pairWeight hGRH) hlim hbound
  have hL : (∑' p, L p) = pairResidue q τ :=
    (tsum_subtype (pairFibre q τ) (pairWeight q)).symm
  rw [hL] at h
  simpa only [F, cauchySquare, z, tsum_mul_left] using h

end GoldbachBoundaries.ResidueClass
