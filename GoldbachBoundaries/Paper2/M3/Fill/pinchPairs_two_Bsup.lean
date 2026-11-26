import GoldbachBoundaries.Paper2.M3.AConst

/-!
# Fill: `pinchPairs_two_Bsup`

`1/2 < B < 1` (M1's `lem_B_iv_proof`). `⊇`: `(ρ, ρ̄)` with `β = B` (both are zeros, `ρ = ρ/1`) and `(1, 1/k)`,
`(1/k, 1)` when `2B = 1 + 1/k`. `⊆`: for `a + b = 2B` with `a, b ∈ Σ_Q`: if `a = 1`, then `b = 2B - 1` is real, not `1`
(`B < 1`), and not `ρ/n` (that would make `ρ` a real zero in `(0, 1)`), so `b = 1/k`; likewise if `b = 1`. Otherwise
`Re a, Re b ≤ B` force `Re a = Re b = B > 1/2`, so both are zeros, and `Im b = -Im a` gives `b = ā`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M3

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1 GoldbachBoundaries.Paper2.M2

/-- A real point of `Σ_Q` other than `1` is some `1/k`, `k ≥ 2` squarefree (`ζ` has no zero in `(0, 1)`). -/
lemma groupB_real_mem_poleSetQ {b : ℂ} (hb : b ∈ PoleSetQ) (him : b.im = 0) (hb1 : b ≠ 1) :
    ∃ k : ℕ, 2 ≤ k ∧ Squarefree k ∧ b = 1 / (k : ℂ) := by
  rcases hb with (hb | hk) | ⟨n, hn, -, ρ, hρ, rfl⟩
  · exact absurd (mem_singleton_iff.mp hb) hb1
  · exact hk
  · exfalso
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hρim : ρ.im = 0 := by
      rw [Complex.div_natCast_im] at him
      exact (div_eq_zero_iff.mp him).resolve_right hn0.ne'
    have hρeq : ρ = (ρ.re : ℂ) := Complex.ext (by simp) (by simp [hρim])
    have hz := hρ.1
    rw [hρeq] at hz
    exact riemannZeta_ne_zero_of_mem_Ioo ⟨hρ.2.1, hρ.2.2⟩ hz

lemma groupB_one_mem_poleSetQ : (1 : ℂ) ∈ PoleSetQ := Or.inl (Or.inl rfl)

lemma groupB_inv_mem_poleSetQ {k : ℕ} (hk : 2 ≤ k) (hsq : Squarefree k) : 1 / (k : ℂ) ∈ PoleSetQ :=
  Or.inl (Or.inr ⟨k, hk, hsq, rfl⟩)

lemma groupB_zero_mem_poleSetQ {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) : ρ ∈ PoleSetQ :=
  Or.inr ⟨1, le_rfl, squarefree_one, ρ, hρ, by simp⟩

/-- The case `a = 1`: `b = 2B - 1` is some `1/k` with `2B = 1 + 1/k`. -/
lemma groupB_case_one {b : ℂ} (hb : b ∈ PoleSetQ) (hB : Bsup < 1)
    (hsum : 1 + b = ((2 * Bsup : ℝ) : ℂ)) :
    ∃ k : ℕ, 2 ≤ k ∧ Squarefree k ∧ 2 * Bsup = 1 + 1 / (k : ℝ) ∧ b = 1 / (k : ℂ) := by
  have hbim : b.im = 0 := by
    have := congrArg Complex.im hsum
    simpa using this
  have hbre : b.re = 2 * Bsup - 1 := by
    have := congrArg Complex.re hsum
    simp at this
    linarith
  have hb1 : b ≠ 1 := by
    rintro rfl
    simp at hbre
    linarith
  obtain ⟨k, hk, hsq, rfl⟩ := groupB_real_mem_poleSetQ hb hbim hb1
  refine ⟨k, hk, hsq, ?_, rfl⟩
  have h := congrArg Complex.re hsum
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  rw [show (1 : ℂ) / (k : ℂ) = ((1 / (k : ℝ) : ℝ) : ℂ) by push_cast; rfl] at h
  simp only [add_re, one_re, ofReal_re] at h
  linarith

/-- **The pairs with sum `2B`** (Z1; `B_∞ < B`). By M1's `lem_B_iv_proof`, `1/2 < B < 1`. `⊇`: `(ρ, ρ̄)` with `β = B`
lies in `Σ_Q²` (`ρ = ρ/1`; `ρ̄` is a zero, paper 1's `conj_mem_nontrivialZeros`) and sums to `2B`; `(1, 1/k)` and
`(1/k, 1)` sum to `1 + 1/k = 2B`. `⊆`: let `a + b = 2B`, `a, b ∈ Σ_Q`. If `a, b ≠ 1`: `Re a, Re b ≤ B` (M1's
`poleSetQ_re_le_Bsup`) force `Re a = Re b = B > 1/2`, so both are zeros (`poleSetQ_re_bounds`: a point of `Σ_Q` that is
not `1` and not a zero has `Re ≤ 1/2`), and `Im b = -Im a` gives `b = ā`. If `a = 1`: `b = 2B - 1 ∈ (0, 1)` is real, so
`b = 1/k` with `k ≥ 2` squarefree (`b ≠ 1`, and `b = ρ/n` real would make `ρ` a real zero in `(0, 1)`); likewise
`b = 1`. Size: 150–250 lines. -/
theorem pinchPairs_two_Bsup (hZ1 : Z1) (h : Binf < Bsup) :
    pinchPairs ((2 * Bsup : ℝ) : ℂ) =
      (fun ρ => (ρ, conj ρ)) '' {ρ | ρ ∈ NontrivialZeros ∧ ρ.re = Bsup} ∪
        {p | ∃ k : ℕ, 2 ≤ k ∧ Squarefree k ∧ 2 * Bsup = 1 + 1 / (k : ℝ) ∧
          (p = (1, 1 / (k : ℂ)) ∨ p = (1 / (k : ℂ), 1))} := by
  obtain ⟨hB1, hB2, -, -⟩ := lem_B_iv_proof hZ1 h
  ext ⟨a, b⟩
  constructor
  · rintro ⟨ha, hb, hab⟩
    simp only at ha hb hab
    by_cases ha1 : a = 1
    · subst ha1
      obtain ⟨k, hk, hsq, hkB, rfl⟩ := groupB_case_one hb hB2 hab
      exact Or.inr ⟨k, hk, hsq, hkB, Or.inl rfl⟩
    by_cases hb1 : b = 1
    · subst hb1
      obtain ⟨k, hk, hsq, hkB, rfl⟩ := groupB_case_one ha hB2 (by rw [add_comm]; exact hab)
      exact Or.inr ⟨k, hk, hsq, hkB, Or.inr rfl⟩
    have hare := poleSetQ_re_le_Bsup hZ1 ha ha1
    have hbre := poleSetQ_re_le_Bsup hZ1 hb hb1
    have hre := congrArg Complex.re hab
    have him := congrArg Complex.im hab
    simp only [add_re, ofReal_re, add_im, ofReal_im] at hre him
    have hae : a.re = Bsup := by linarith
    have hbe : b.re = Bsup := by linarith
    have haZ : a ∈ NontrivialZeros := by
      by_contra hn
      have := (poleSetQ_re_bounds ha).2.2 ha1 hn
      linarith
    refine Or.inl ⟨a, ⟨haZ, hae⟩, ?_⟩
    simp only [Prod.mk.injEq, true_and]
    exact Complex.ext (by simp [hae, hbe]) (by simp; linarith)
  · rintro (⟨ρ, ⟨hρ, hre⟩, he⟩ | ⟨k, hk, hsq, hkB, hp | hp⟩)
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      refine ⟨groupB_zero_mem_poleSetQ hρ, groupB_zero_mem_poleSetQ (conj_mem_nontrivialZeros hρ), ?_⟩
      simp only
      rw [Complex.add_conj, hre]
    · simp only [Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      refine ⟨groupB_one_mem_poleSetQ, groupB_inv_mem_poleSetQ hk hsq, ?_⟩
      simp only
      rw [hkB]
      push_cast
      ring
    · simp only [Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      refine ⟨groupB_inv_mem_poleSetQ hk hsq, groupB_one_mem_poleSetQ, ?_⟩
      simp only
      rw [hkB]
      push_cast
      ring

end GoldbachBoundaries.Paper2.M3
