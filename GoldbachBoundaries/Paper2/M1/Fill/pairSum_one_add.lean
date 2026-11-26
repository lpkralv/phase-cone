import GoldbachBoundaries.Paper2.M1.Residue

/-!
# Fill: `pairSum_one_add`

Both `(1, u)` and `(u, 1)` are pairs (`1 ∈ Σ_Q`), so `pinchPairs (1 + u) = {(1, u), (u, 1)}`; the `tsum` is the finite
sum over this set. For `u = 1` it is `R_1² Γ(1)²/Γ(2) = 1`; for `u ≠ 1` it is `2 R_u Γ(u)/Γ(1 + u) = 2 R_u/u`
(`Γ(1 + u) = uΓ(u)`, `Γ(u) ≠ 0` as `Re u > 0`).
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M1

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **The pair sum at `1 + u`** when `(1, u)`, `(u, 1)` are the only pairs: `2R_u/u` for `u ≠ 1` (`R_1 = 1`,
`Γ(1 + u) = uΓ(u)`, `u ≠ 0`, `Γ(u) ≠ 0`), and `R_1² Γ(1)²/Γ(2) = 1` for `u = 1` (one pair). Both pairs are in
`pinchPairs (1 + u)` since `1 ∈ Σ_Q`. Uses: `Rcoef_one'`. Size: 80–150 lines. -/
theorem pairSum_one_add {u : ℂ} (hu : u ∈ PoleSetQ) (hpairs : pinchPairs (1 + u) ⊆ {(1, u), (u, 1)}) :
    pairSum (1 + u) = if u = 1 then 1 else 2 * Rcoef u / u := by
  classical
  have h1 : (1 : ℂ) ∈ PoleSetQ := Or.inl (Or.inl rfl)
  have hset : pinchPairs (1 + u) = ↑({(1, u), (u, 1)} : Finset (ℂ × ℂ)) := by
    rw [Finset.coe_insert, Finset.coe_singleton]
    refine hpairs.antisymm ?_
    rintro p (rfl | rfl)
    · exact ⟨h1, hu, rfl⟩
    · exact ⟨hu, h1, add_comm _ _⟩
  have hre : 0 < u.re := re_pos_of_mem_poleSetQ hu
  have hu0 : u ≠ 0 := by rintro rfl; simp at hre
  have hG : Gamma u ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hre
  rw [pairSum, hset, Finset.tsum_subtype' (s := ({(1, u), (u, 1)} : Finset (ℂ × ℂ)))
    (f := fun p : ℂ × ℂ => Rcoef p.1 * Rcoef p.2 * betaB p.1 p.2)]
  split_ifs with h
  · subst h
    simp [Rcoef_one', betaB]
    norm_num [Complex.Gamma_one, show (2 : ℂ) = 1 + 1 by norm_num, Complex.Gamma_add_one]
  · have hne : ((1 : ℂ), u) ≠ (u, 1) := by
      intro he
      exact h (Prod.mk.inj he).1.symm
    rw [Finset.sum_pair hne]
    simp only [Rcoef_one', betaB, Complex.Gamma_one]
    rw [add_comm (1 : ℂ) u, Complex.Gamma_add_one u hu0]
    field_simp
    ring

end GoldbachBoundaries.Paper2.M1
