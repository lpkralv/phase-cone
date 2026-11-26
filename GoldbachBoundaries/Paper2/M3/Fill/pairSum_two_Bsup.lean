import GoldbachBoundaries.Paper2.M3.AConst
import GoldbachBoundaries.Paper2.M3.Fill.pinchPairs_two_Bsup

/-!
# Fill: `pairSum_two_Bsup`

By `pinchPairs_two_Bsup`, `pinchPairs (2B)` is the image of the finite set `S = {ρ : β = B}` (M1's `lem_B_iv_proof`)
under the injective `ρ ↦ (ρ, ρ̄)`, together with the pairs `(1, 1/k)`, `(1/k, 1)` when `2B = 1 + 1/k`, `k ≥ 2`
squarefree (this `k` is unique). The two parts are disjoint (`Re 1 = 1 ≠ B`). The `tsum` is the finite sum over the
union. The term at `(ρ, ρ̄)` is `R_ρ R_{ρ̄} Γ(ρ)Γ(ρ̄)/Γ(2B) = m(ρ)²|Γ(ρ)|²/Γ(2B)` (`Rcoef_of_half_le_re`, M1's
`Rcoef_real_conj` for `R_{ρ̄} = R_ρ`, `Complex.Gamma_conj`, `ρ + ρ̄ = 2B`), and these sum to `A`: `A`'s `tsum` runs over
every zero with `β = B`, so it already counts both `ρ` and `ρ̄`, as do the ordered pairs `(ρ, ρ̄)` and `(ρ̄, ρ)`. The
pairs `(1, 1/k)`, `(1/k, 1)` each give `R_1 R_{1/k} Γ(1)Γ(1/k)/Γ(1 + 1/k) = μ(k)` (`Rcoef_one'`, `Rcoef_inv`,
`Γ(1 + 1/k) = Γ(1/k)/k`); for `k` not squarefree there are none and `μ(k) = 0`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M3

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1 GoldbachBoundaries.Paper2.M2

/-- `2B = 1 + 1/k` determines `k`. -/
lemma groupB_k_unique {k k' : ℕ} (hk : 2 ≤ k) (hk' : 2 ≤ k')
    (h : 2 * Bsup = 1 + 1 / (k : ℝ)) (h' : 2 * Bsup = 1 + 1 / (k' : ℝ)) : k = k' := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hk0' : (0 : ℝ) < k' := by exact_mod_cast (by omega : 0 < k')
  have h1 : 1 / (k : ℝ) = 1 / (k' : ℝ) := by linarith
  rw [one_div, one_div, inv_inj] at h1
  exact_mod_cast h1

/-- The term of `pairSum` at `(1, 1/k)` is `μ(k)`. -/
lemma groupB_term_one_inv {k : ℕ} (hk : 2 ≤ k) (hsq : Squarefree k) :
    Rcoef 1 * Rcoef (1 / (k : ℂ)) * betaB 1 (1 / (k : ℂ)) = mu k := by
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hu0 : (1 / (k : ℂ)) ≠ 0 := one_div_ne_zero hk0
  have hG : Gamma (1 / (k : ℂ)) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (one_div_natCast_re_pos (by omega : k ≠ 0))
  rw [Rcoef_one', Rcoef_inv hk hsq, betaB, Complex.Gamma_one, add_comm (1 : ℂ),
    Complex.Gamma_add_one _ hu0]
  field_simp

/-- The term of `pairSum` at `(1/k, 1)` is `μ(k)`. -/
lemma groupB_term_inv_one {k : ℕ} (hk : 2 ≤ k) (hsq : Squarefree k) :
    Rcoef (1 / (k : ℂ)) * Rcoef 1 * betaB (1 / (k : ℂ)) 1 = mu k := by
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hu0 : (1 / (k : ℂ)) ≠ 0 := one_div_ne_zero hk0
  have hG : Gamma (1 / (k : ℂ)) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (one_div_natCast_re_pos (by omega : k ≠ 0))
  rw [Rcoef_one', Rcoef_inv hk hsq, betaB, Complex.Gamma_one, Complex.Gamma_add_one _ hu0]
  field_simp

/-- The term of `pairSum` at `(ρ, ρ̄)`, `β = B ≥ 1/2`, is `m(ρ)²|Γ(ρ)|²/Γ(2B)`. -/
lemma groupB_term_conj (hZ1 : Z1) (hB1 : 1 / 2 ≤ Bsup) {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros)
    (hre : ρ.re = Bsup) :
    Rcoef ρ * Rcoef (conj ρ) * betaB ρ (conj ρ) =
      (((zetaMult ρ : ℝ) ^ 2 * ‖Gamma ρ‖ ^ 2 : ℝ) : ℂ) / (Real.Gamma (2 * Bsup) : ℂ) := by
  have hmem : ρ ∈ PoleSetQ := Or.inr ⟨1, le_rfl, squarefree_one, ρ, hρ, by simp⟩
  rw [(Rcoef_real_conj hZ1 hmem).2, Rcoef_of_half_le_re hρ (by rw [hre]; exact hB1), betaB,
    Complex.Gamma_conj]
  have hsum : ρ + conj ρ = ((2 * Bsup : ℝ) : ℂ) := by
    rw [Complex.add_conj, hre]
  rw [hsum, Complex.Gamma_ofReal, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

/-- `𝓡(2B) = A + ∑` over the `(1, 1/k)`-type pairs, given those pairs as a `Finset`. -/
lemma groupB_pairSum_eq (hZ1 : Z1) (h : Binf < Bsup) (KF : Finset (ℂ × ℂ))
    (hKF : {p : ℂ × ℂ | ∃ k : ℕ, 2 ≤ k ∧ Squarefree k ∧ 2 * Bsup = 1 + 1 / (k : ℝ) ∧
      (p = (1, 1 / (k : ℂ)) ∨ p = (1 / (k : ℂ), 1))} = ↑KF) :
    pairSum ((2 * Bsup : ℝ) : ℂ) = Aconst + ∑ p ∈ KF, Rcoef p.1 * Rcoef p.2 * betaB p.1 p.2 := by
  classical
  obtain ⟨hB1, hB2, hS, -⟩ := lem_B_iv_proof hZ1 h
  set S : Set ℂ := {ρ | ρ ∈ NontrivialZeros ∧ ρ.re = Bsup} with hSdef
  set SF := hS.toFinset with hSF
  set g : ℂ → ℂ × ℂ := fun ρ => (ρ, conj ρ) with hg
  have hset : pinchPairs ((2 * Bsup : ℝ) : ℂ) = ↑(SF.image g ∪ KF) := by
    rw [pinchPairs_two_Bsup hZ1 h, hKF, Finset.coe_union, Finset.coe_image, hSF, hS.coe_toFinset]
  have hdisj : Disjoint (SF.image g) KF := by
    rw [Finset.disjoint_left]
    intro p hp hpK
    have hpK' : p ∈ ({p : ℂ × ℂ | ∃ k : ℕ, 2 ≤ k ∧ Squarefree k ∧ 2 * Bsup = 1 + 1 / (k : ℝ) ∧
        (p = (1, 1 / (k : ℂ)) ∨ p = (1 / (k : ℂ), 1))} : Set (ℂ × ℂ)) := by
      rw [hKF]
      exact hpK
    obtain ⟨ρ, hρS, rfl⟩ := Finset.mem_image.mp hp
    have hρ := (hS.mem_toFinset.mp hρS)
    obtain ⟨k, -, -, -, he | he⟩ := hpK'
    · have := congrArg (fun q : ℂ × ℂ => q.1.re) he
      simp only [hg, one_re] at this
      linarith [hρ.2]
    · have := congrArg (fun q : ℂ × ℂ => q.2.re) he
      simp only [hg, conj_re, one_re] at this
      linarith [hρ.2]
  have hinj : ∀ a ∈ SF, ∀ b ∈ SF, g a = g b → a = b := fun a _ b _ hab => (Prod.mk.inj hab).1
  rw [pairSum, hset, Finset.tsum_subtype' (s := SF.image g ∪ KF) (f := fun p : ℂ × ℂ => Rcoef p.1 * Rcoef p.2 * betaB p.1 p.2),
    Finset.sum_union hdisj, Finset.sum_image hinj]
  congr 1
  -- the zeros part is `A`
  have hA : (∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ ρ.re = Bsup},
      (zetaMult (ρ : ℂ) : ℝ) ^ 2 * ‖Gamma (ρ : ℂ)‖ ^ 2) =
      ∑ ρ ∈ SF, (zetaMult ρ : ℝ) ^ 2 * ‖Gamma ρ‖ ^ 2 := by
    rw [← Finset.tsum_subtype' SF (fun ρ : ℂ => (zetaMult ρ : ℝ) ^ 2 * ‖Gamma ρ‖ ^ 2), hSF,
      hS.coe_toFinset]
    rfl
  rw [Aconst, hA, ofReal_div, ofReal_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun ρ hρS => ?_
  have hρ := hS.mem_toFinset.mp hρS
  exact groupB_term_conj hZ1 hB1.le hρ.1 hρ.2

/-- **`𝓡(2B)`** (Z1; `B_∞ < B`). `pinchPairs (2B)` is finite (M1's `pinchPairs_finite`, `2B > 2B_∞`), so `pairSum` is
the finite sum over `pinchPairs_two_Bsup`; the two parts are disjoint (`Re 1 = 1 ≠ B`). The zeros with `β = B` form a
finite set (M1's `Bsup_attained`), and `ρ ↦ (ρ, ρ̄)` is injective; the term is
`R_ρ R_{ρ̄} Γ(ρ)Γ(ρ̄)/Γ(2B) = m(ρ)²|Γ(ρ)|²/Γ(2B)` (`Rcoef_of_half_le_re` at `ρ` and at `ρ̄`, which has `β = B` too,
with `m(ρ̄) = m(ρ)` by (Z1); `Complex.Gamma_conj`, `mul_conj`; `ρ + ρ̄ = 2B`, `Complex.Gamma_ofReal`), whose sum is
`Aconst` (its `tsum` over a finite subtype, `tsum_fintype` after `Set.Finite.fintype`, or `tsum_subtype`). The pairs
`(1, 1/k)`, `(1/k, 1)` (present iff `2B = 1 + 1/k` with `k` squarefree; `k` is then unique) give
`2R_1R_{1/k}Γ(1)Γ(1/k)/Γ(1 + 1/k) = 2μ(k)` (M1's `Rcoef_one'`, `Rcoef_inv`; `Γ(1 + 1/k) = Γ(1/k)/k`); for `k` not
squarefree there are none and `μ(k) = 0`. Size: 250–400 lines. -/
theorem pairSum_two_Bsup (hZ1 : Z1) (h : Binf < Bsup) :
    (∀ k : ℕ, 2 ≤ k → 2 * Bsup = 1 + 1 / (k : ℝ) →
        pairSum ((2 * Bsup : ℝ) : ℂ) = Aconst + 2 * mu k) ∧
      ((∀ k : ℕ, 2 ≤ k → 2 * Bsup ≠ 1 + 1 / (k : ℝ)) → pairSum ((2 * Bsup : ℝ) : ℂ) = Aconst) := by
  classical
  refine ⟨fun k hk hkB => ?_, fun hno => ?_⟩
  · by_cases hsq : Squarefree k
    · have hne : ((1 : ℂ), 1 / (k : ℂ)) ≠ (1 / (k : ℂ), 1) := by
        intro he
        have h1 := (Prod.mk.inj he).1
        have hk1 : (k : ℂ) = 1 := by
          rw [eq_div_iff (by exact_mod_cast (by omega : k ≠ 0)), one_mul] at h1
          exact h1
        have : k = 1 := by exact_mod_cast hk1
        omega
      have hKF : {p : ℂ × ℂ | ∃ k : ℕ, 2 ≤ k ∧ Squarefree k ∧ 2 * Bsup = 1 + 1 / (k : ℝ) ∧
          (p = (1, 1 / (k : ℂ)) ∨ p = (1 / (k : ℂ), 1))} =
          ↑({((1 : ℂ), 1 / (k : ℂ)), (1 / (k : ℂ), 1)} : Finset (ℂ × ℂ)) := by
        ext p
        simp only [mem_ofPred_eq, Finset.coe_insert, Finset.coe_singleton, mem_insert_iff,
          mem_singleton_iff]
        constructor
        · rintro ⟨k', hk', -, hkB', hp⟩
          obtain rfl := groupB_k_unique hk hk' hkB hkB'
          exact hp
        · intro hp
          exact ⟨k, hk, hsq, hkB, hp⟩
      rw [groupB_pairSum_eq hZ1 h _ hKF, Finset.sum_pair hne]
      simp only
      rw [groupB_term_one_inv hk hsq, groupB_term_inv_one hk hsq]
      ring
    · have hKF : {p : ℂ × ℂ | ∃ k : ℕ, 2 ≤ k ∧ Squarefree k ∧ 2 * Bsup = 1 + 1 / (k : ℝ) ∧
          (p = (1, 1 / (k : ℂ)) ∨ p = (1 / (k : ℂ), 1))} = ↑(∅ : Finset (ℂ × ℂ)) := by
        rw [Finset.coe_empty, Set.eq_empty_iff_forall_notMem]
        rintro p ⟨k', hk', hsq', hkB', -⟩
        obtain rfl := groupB_k_unique hk hk' hkB hkB'
        exact hsq hsq'
      rw [groupB_pairSum_eq hZ1 h _ hKF, Finset.sum_empty]
      have hmu : ArithmeticFunction.moebius k = 0 :=
        ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq
      simp [mu, hmu]
  · have hKF : {p : ℂ × ℂ | ∃ k : ℕ, 2 ≤ k ∧ Squarefree k ∧ 2 * Bsup = 1 + 1 / (k : ℝ) ∧
        (p = (1, 1 / (k : ℂ)) ∨ p = (1 / (k : ℂ), 1))} = ↑(∅ : Finset (ℂ × ℂ)) := by
      rw [Finset.coe_empty, Set.eq_empty_iff_forall_notMem]
      rintro p ⟨k', hk', -, hkB', -⟩
      exact hno k' hk' hkB'
    rw [groupB_pairSum_eq hZ1 h _ hKF, Finset.sum_empty, add_zero]

end GoldbachBoundaries.Paper2.M3
