import GoldbachBoundaries.Paper2.M2.Single

/-!
# Filler (Group D): `singleRep_points_infinite`

`y > 0`: `thm_single_infinite_proof` with `ε' = min ε (y/2) < y`, and the set for `ε'` is a subset.
`y ≥ 0`: the case `y' = y + ε/2 > 0` with radius `ε/2`, since `|u - iy| ≤ |u - iy'| + ε/2`.
`y < 0`: conjugation maps the set for `-y` injectively into the set for `y` (`ρ̄` is a zero by paper 1's
`conj_mem_nontrivialZeros`, and single representation is preserved by conjugating representations).
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M2

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- The set of `singleRep_points_infinite`. -/
private def SRset (y ε : ℝ) : Set ℂ :=
  {u : ℂ | ∃ ρ ∈ NontrivialZeros, ρ.re = 1 / 2 ∧ ∃ q : ℕ, q.Prime ∧ IsSingleRep ρ q ∧
    u = ρ / (q : ℂ) ∧ ‖u - y * I‖ < ε}

private lemma SRset_mono_center {y y' ε ε' : ℝ} (h : |y - y'| + ε' ≤ ε) : SRset y' ε' ⊆ SRset y ε := by
  rintro u ⟨ρ, hρ, hre, q, hq, hs, rfl, hu⟩
  refine ⟨ρ, hρ, hre, q, hq, hs, rfl, ?_⟩
  have hyy : ‖(y' : ℂ) * I - y * I‖ = |y - y'| := by
    rw [← sub_mul, norm_mul, Complex.norm_I, mul_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_sub_comm]
  calc ‖ρ / (q : ℂ) - y * I‖ = ‖(ρ / (q : ℂ) - y' * I) + ((y' : ℂ) * I - y * I)‖ := by ring_nf
    _ ≤ ‖ρ / (q : ℂ) - y' * I‖ + ‖(y' : ℂ) * I - y * I‖ := norm_add_le _ _
    _ < ε' + |y - y'| := by rw [hyy]; linarith
    _ ≤ ε := by linarith

private lemma SRset_infinite_pos (hZ1 : Z1) (hZ2 : Z2) (hZ4 : Z4) (hZ5 : Z5) {y ε : ℝ} (hy : 0 < y)
    (hε : 0 < ε) : (SRset y ε).Infinite := by
  have hε' : 0 < min ε (y / 2) := lt_min hε (by linarith)
  have hε'y : min ε (y / 2) < y := (min_le_right _ _).trans_lt (by linarith)
  refine (thm_single_infinite_proof hZ1 hZ2 hZ4 hZ5 hy hε' hε'y).mono ?_
  exact SRset_mono_center (by simp)

private lemma SRset_infinite_nonneg (hZ1 : Z1) (hZ2 : Z2) (hZ4 : Z4) (hZ5 : Z5) {y ε : ℝ} (hy : 0 ≤ y)
    (hε : 0 < ε) : (SRset y ε).Infinite := by
  refine (SRset_infinite_pos hZ1 hZ2 hZ4 hZ5 (y := y + ε / 2) (by linarith) (half_pos hε)).mono ?_
  refine SRset_mono_center ?_
  rw [show y - (y + ε / 2) = -(ε / 2) by ring, abs_neg, abs_of_pos (half_pos hε)]
  linarith

/-- Conjugation maps the set for `-y` into the set for `y`. -/
private lemma conj_mapsTo_SRset (y ε : ℝ) : MapsTo (starRingEnd ℂ) (SRset (-y) ε) (SRset y ε) := by
  rintro u ⟨ρ, hρ, hre, q, hq, hs, rfl, hu⟩
  refine ⟨conj ρ, conj_mem_nontrivialZeros hρ, by simpa using hre, q, hq, ?_, by simp, ?_⟩
  · rintro ρ' k ⟨hρ', hk, hsq, heq⟩
    have hrep : IsRep (ρ / (q : ℂ)) (conj ρ') k := by
      refine ⟨conj_mem_nontrivialZeros hρ', hk, hsq, ?_⟩
      have := congrArg conj heq
      simpa using this
    obtain ⟨h1, h2⟩ := hs (conj ρ') k hrep
    refine ⟨?_, h2⟩
    rw [← h1, Complex.conj_conj]
  · have : conj (ρ / (q : ℂ)) - (y : ℂ) * I = conj (ρ / (q : ℂ) - ((-y : ℝ) : ℂ) * I) := by
      simp [map_mul, Complex.conj_I, Complex.conj_ofReal]; ring
    rw [this, Complex.norm_conj]
    exact hu

/-- **Single-representation points near every `iy`** (Z1, Z2, Z4, Z5; the remarks after `nr:thm:single`).
`y > 0`: `thm_single_infinite_proof` with `ε' = min ε (y/2)` (so `ε' < y`), and the set for `ε'` is a subset.
`y < 0`: apply the case `-y`; `u ↦ ū` is injective (`Set.Infinite.image` with `conj` injective) and maps the set for
`-y` into the set for `y`: `ρ̄` is a zero (paper 1's `conj_mem_nontrivialZeros`, no (Z1) needed) with `Re ρ̄ = 1/2`,
`IsSingleRep ρ̄ q` (a representation `(ρ', k)` of `ρ̄/q` conjugates to the representation `(ρ̄', k)` of `ρ/q`, so
`ρ̄' = ρ`, `k = q`), and `|ū - iy| = |u - i(-y)|`. `y = 0`: the case `y' = ε/2`, `ε' = ε/4`, since
`|u| ≤ |u - iε/2| + ε/2 < 3ε/4`. Size: 150–250 lines. -/
theorem singleRep_points_infinite (hZ1 : Z1) (hZ2 : Z2) (hZ4 : Z4) (hZ5 : Z5) (y : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    {u : ℂ | ∃ ρ ∈ NontrivialZeros, ρ.re = 1 / 2 ∧ ∃ q : ℕ, q.Prime ∧ IsSingleRep ρ q ∧
      u = ρ / (q : ℂ) ∧ ‖u - y * I‖ < ε}.Infinite := by
  show (SRset y ε).Infinite
  rcases le_or_gt 0 y with hy | hy
  · exact SRset_infinite_nonneg hZ1 hZ2 hZ4 hZ5 hy hε
  · have hinf := SRset_infinite_pos hZ1 hZ2 hZ4 hZ5 (y := -y) (by linarith) hε
    have himg := hinf.image (starRingEnd ℂ).injective.injOn
    exact himg.mono (conj_mapsTo_SRset y ε).image_subset

/-! ## Real lemmas of `LW.lean` that use `singleRep_points_infinite` -/

/-- Part 1 of `cor_LW`: every continuation of `Q` has infinitely many poles in every disc about a point of the
imaginary axis. -/
theorem poles_Qc_accumulate (hZ1 : Z1) (hZ2 : Z2) (hZ4 : Z4) (hZ5 : Z5) :
    ∀ Qc : ℂ → ℂ, IsQCont Qc → ∀ y : ℝ, ∀ ε : ℝ, 0 < ε →
      {a | a ∈ halfPlane 0 ∧ ‖a - y * I‖ < ε ∧ meromorphicOrderAt Qc a < 0}.Infinite := by
  intro Qc hQc y ε hε
  refine (singleRep_points_infinite hZ1 hZ2 hZ4 hZ5 y hε).mono ?_
  rintro u ⟨ρ, hρ, hre, q, hq, hs, rfl, hu⟩
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hpos : 0 < (ρ / (q : ℂ)).re := by
    have : (ρ / (q : ℂ)).re = ρ.re / q := by simp
    rw [this]
    exact div_pos hρ.2.1 hq0
  have hmem : ρ / (q : ℂ) ∈ PoleSetQ := Or.inr ⟨q, hq.one_lt.le, hq.squarefree, ρ, hρ, rfl⟩
  refine ⟨hpos, hu, ?_⟩
  rw [meromorphicOrderAt_congr ((isQCont_eventuallyEq hQc).2 _ hpos), meromorphicOrderAt_Qcont_neg_iff hmem,
    (Rcoef_div_of_isSingleRep hρ hq hs).1]
  have hm : zetaMult ρ ≠ 0 := by
    have := one_le_zetaMult hρ
    omega
  exact div_ne_zero (by exact_mod_cast hm) (by exact_mod_cast hq.ne_zero)

/-- `Qcont` has no meromorphic extension across any point of the imaginary axis. -/
theorem noMeromorphicExtensionAt_Qcont (hZ1 : Z1) (hZ2 : Z2) (hZ4 : Z4) (hZ5 : Z5) (y : ℝ) :
    NoMeromorphicExtensionAt Qcont (halfPlane 0) ((y : ℂ) * I) := by
  refine noMeromorphicExtensionAt_of_poles_in_every_ball (isOpen_halfPlane 0) fun ε hε => ?_
  obtain ⟨a, ha⟩ := (poles_Qc_accumulate hZ1 hZ2 hZ4 hZ5 Qcont isQCont_Qcont y ε hε).nonempty
  refine ⟨a, ha.1, ?_, ?_, ha.2.2⟩
  · intro h
    have h0 : (0 : ℝ) < a.re := ha.1
    rw [h] at h0
    simp at h0
  · rw [mem_ball, dist_eq_norm]
    exact ha.2.1

end GoldbachBoundaries.Paper2.M2
