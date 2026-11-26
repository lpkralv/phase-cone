import GoldbachBoundaries.Paper2.M5.Fill.evalH_root_bound
import GoldbachBoundaries.Paper2.M5.Fill.exists_ordinate_in_interval
import GoldbachBoundaries.Paper2.M5.Fill.CH_eq_two_terms
import GoldbachBoundaries.Paper2.M1.Fill.BCommon

/-!
# Filler F4: `exists_tau0_CH_ne_zero` (the claim of Theorem F(iii))

The paper's construction. `M` = the number of zeros with `|γ| ≤ |τ| + ε`; `E`, `d` from `evalH_root_bound`;
`N = d + M + 3`; `ℓ = 2ε/N`; `Y₀` from `exists_ordinate_in_interval`. A zero `ρ₁` with `γ₁` above `max(Y₀, 0) + |τ| + ε`
and above every `‖z‖`, `z ∈ E` (so `ρ₁ ∉ E`). For `i < N` an ordinate `γ'_i` in
`(γ₁ - τ - ε + iℓ, γ₁ - τ - ε + (i+1)ℓ)`; `τ_i = γ₁ - γ'_i` lies in `(τ - ε, τ + ε)` and `i ↦ τ_i` is injective. The
indices with `H(ρ₁, ρ̄'_i) = 0` (at most `d`), with `τ_i` an ordinate (at most `M`), with `τ_i = 0` or `τ_i = τ` (at most
one each) do not exhaust the `N` indices. For a remaining `i`, `CH_eq_two_terms` gives `C_H(τ_i) ≠ 0`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- `m(ρ) ≠ 0` (as a complex number) at a non-trivial zero. -/
lemma F4_zetaMult_ne_zero {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) : (zetaMult ρ : ℂ) ≠ 0 := by
  have hne : ρ ≠ 1 := fun h => by
    have := hρ.2.2
    rw [h, Complex.one_re] at this
    exact lt_irrefl _ this
  have := one_le_zetaMult_of_zero hne hρ.1
  exact Nat.cast_ne_zero.mpr (by omega)

theorem exists_tau0_CH_ne_zero (hRH : RiemannHypothesis) (hL : ZLittlewood) (hF : HypF)
    (H : MvPolynomial (Fin 2) ℂ) (hH0 : H ≠ 0) (hHs : ∀ z w, evalH H z w = evalH H w z) (τ : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ τ₀ : ℝ, τ₀ ≠ τ ∧ |τ₀ - τ| < ε ∧ τ₀ ≠ 0 ∧ (∀ ρ ∈ NontrivialZeros, ρ.im ≠ τ₀) ∧ CH H τ₀ ≠ 0 := by
  classical
  -- the zeros of small height, the exceptional set `E` and the degree bound `d`
  set ZI : Set ℂ := {ρ : ℂ | ρ ∈ NontrivialZeros ∧ |ρ.im| ≤ |τ| + ε} with hZI_def
  have hZI : ZI.Finite := finite_zeros_abs_im_le _
  obtain ⟨E, d, hE, hroot⟩ := evalH_root_bound H hH0
  set N : ℕ := d + ZI.ncard + 3 with hN
  have hNpos : (0 : ℝ) < N := by positivity
  set ℓ : ℝ := 2 * ε / N with hℓ_def
  have hℓ : 0 < ℓ := by positivity
  have hNℓ : (N : ℝ) * ℓ = 2 * ε := by
    rw [hℓ_def]; field_simp
  obtain ⟨Y₀, hY₀⟩ := exists_ordinate_in_interval hL hℓ
  obtain ⟨R, hR⟩ := hE.isBounded.exists_norm_le
  -- the zero `ρ₁`
  obtain ⟨ρ₁, h₁, hγ₁⟩ := exists_nontrivialZero_im_gt (max (max Y₀ 0 + |τ| + ε) R)
  have hγ₁a : max Y₀ 0 + |τ| + ε < ρ₁.im := lt_of_le_of_lt (le_max_left _ _) hγ₁
  have hγ₁R : R < ρ₁.im := lt_of_le_of_lt (le_max_right _ _) hγ₁
  have hρ₁E : ρ₁ ∉ E := fun h => by
    have h1 := hR ρ₁ h
    have h2 := Complex.abs_im_le_norm ρ₁
    have h3 := le_abs_self ρ₁.im
    linarith
  obtain ⟨hrfin, hrcard⟩ := hroot ρ₁ hρ₁E
  have hY0 : 0 ≤ max Y₀ 0 := le_max_right _ _
  have hτ_le : τ ≤ |τ| := le_abs_self τ
  -- the left ends of the `N` subintervals
  set t : Fin N → ℝ := fun i => ρ₁.im - τ - ε + ((i : ℕ) : ℝ) * ℓ with ht_def
  have ht_ge : ∀ i : Fin N, max Y₀ 0 ≤ t i := by
    intro i
    have : 0 ≤ ((i : ℕ) : ℝ) * ℓ := by positivity
    simp only [ht_def]
    linarith
  choose ρ' hρ'mem hlo hhi using fun i : Fin N => hY₀ (t i) ((le_max_left _ _).trans (ht_ge i))
  -- the ordinates `γ'_i` are strictly increasing
  have hmono : StrictMono fun i : Fin N => (ρ' i).im := by
    intro i j hij
    have hij' : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by
      have : (i : ℕ) + 1 ≤ (j : ℕ) := hij
      exact_mod_cast this
    have h1 := hhi i
    have h2 := hlo j
    have h3 : t i + ℓ ≤ t j := by
      simp only [ht_def]
      nlinarith
    simp only
    linarith
  have hinjim : Function.Injective fun i : Fin N => (ρ' i).im := hmono.injective
  set τi : Fin N → ℝ := fun i => ρ₁.im - (ρ' i).im with hτi_def
  have hinjτ : Function.Injective τi := by
    intro i j h
    apply hinjim
    simp only [hτi_def] at h
    simp only
    linarith
  have hτi_win : ∀ i : Fin N, |τi i - τ| < ε := by
    intro i
    have h1 := hhi i
    have h2 := hlo i
    have hi : ((i : ℕ) : ℝ) + 1 ≤ N := by
      have : (i : ℕ) + 1 ≤ N := i.isLt
      exact_mod_cast this
    have hi0 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
    have hb : (((i : ℕ) : ℝ) + 1) * ℓ ≤ 2 * ε := by
      rw [← hNℓ]; exact mul_le_mul_of_nonneg_right hi hℓ.le
    have hb0 : 0 ≤ ((i : ℕ) : ℝ) * ℓ := by positivity
    simp only [ht_def] at h1 h2
    rw [abs_lt]
    simp only [hτi_def]
    constructor <;> nlinarith
  -- the bad indices
  set B1 : Set (Fin N) := {i | evalH H ρ₁ (conj (ρ' i)) = 0} with hB1
  set B2 : Set (Fin N) := {i | ∃ ρ ∈ NontrivialZeros, ρ.im = τi i} with hB2
  set B3 : Set (Fin N) := {i | τi i = 0} with hB3
  set B4 : Set (Fin N) := {i | τi i = τ} with hB4
  have hc1 : B1.ncard ≤ d := by
    refine le_trans (Set.ncard_le_ncard_of_injOn (fun i => conj (ρ' i)) (fun i hi => hi)
      (fun i _ j _ h => ?_) hrfin) hrcard
    apply hinjim
    have h' : ρ' i = ρ' j := (starRingEnd ℂ).injective h
    simp only [h']
  have hc2 : B2.ncard ≤ ZI.ncard := by
    refine le_trans (Set.ncard_le_ncard_of_injOn τi (t := Complex.im '' ZI) (fun i hi => ?_)
      (fun i _ j _ h => hinjτ h) (hZI.image _)) (Set.ncard_image_le hZI)
    obtain ⟨ρ, hρ, hρim⟩ := hi
    refine ⟨ρ, ⟨hρ, ?_⟩, hρim⟩
    have hw := hτi_win i
    rw [hρim]
    rw [abs_lt] at hw
    rw [abs_le]
    constructor <;> cases abs_cases τ <;> linarith
  have hc3 : B3.ncard ≤ 1 := by
    rw [Set.ncard_le_one]
    intro i hi j hj
    exact hinjτ (by rw [show τi i = 0 from hi, show τi j = 0 from hj])
  have hc4 : B4.ncard ≤ 1 := by
    rw [Set.ncard_le_one]
    intro i hi j hj
    exact hinjτ (by rw [show τi i = τ from hi, show τi j = τ from hj])
  have hgood : ∃ i : Fin N, i ∉ B1 ∪ B2 ∪ B3 ∪ B4 := by
    by_contra hcon
    push Not at hcon
    have hsub : (Set.univ : Set (Fin N)) ⊆ B1 ∪ B2 ∪ B3 ∪ B4 := fun i _ => hcon i
    have h1 := Set.ncard_le_ncard hsub
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at h1
    have h2 := Set.ncard_union_le (B1 ∪ B2 ∪ B3) B4
    have h3 := Set.ncard_union_le (B1 ∪ B2) B3
    have h4 := Set.ncard_union_le B1 B2
    omega
  obtain ⟨i, hi⟩ := hgood
  simp only [Set.mem_union, not_or] at hi
  obtain ⟨⟨⟨hi1, hi2⟩, hi3⟩, hi4⟩ := hi
  -- the good index
  refine ⟨τi i, hi4, hτi_win i, hi3, fun ρ hρ hρim => hi2 ⟨ρ, hρ, hρim⟩, ?_⟩
  have h₂ := conj_mem_nontrivialZeros (hρ'mem i)
  have hpos' : 0 < (ρ' i).im := lt_of_le_of_lt (hY0.trans (ht_ge i)) (hlo i)
  have hγ₁pos : 0 < ρ₁.im := by
    have : 0 ≤ |τ| := abs_nonneg τ
    linarith
  have hsum : ρ₁ + conj (ρ' i) = 1 + (τi i : ℂ) * I := by
    apply Complex.ext
    · simp only [Complex.add_re, Complex.conj_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
        Complex.I_re, Complex.ofReal_im, Complex.I_im]
      rw [sigmaFinite_re_eq_half hRH h₁, sigmaFinite_re_eq_half hRH (hρ'mem i)]
      norm_num
    · simp [hτi_def]
      ring
  have hne : ρ₁ ≠ conj (ρ' i) := by
    intro h
    have := congrArg Complex.im h
    rw [Complex.conj_im] at this
    linarith
  rw [CH_eq_two_terms hRH hF H hHs hi3 h₁ h₂ hsum hne]
  refine mul_ne_zero two_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (F4_zetaMult_ne_zero h₁)
    (F4_zetaMult_ne_zero h₂)) (div_ne_zero (mul_ne_zero (Complex.Gamma_ne_zero_of_re_pos h₁.2.1)
      (Complex.Gamma_ne_zero_of_re_pos h₂.2.1)) (Complex.Gamma_ne_zero_of_re_pos ?_))) hi1)
  simp

end GoldbachBoundaries.Paper2.M5
