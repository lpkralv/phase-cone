import GoldbachBoundaries.Paper2.M4a.Restrict
import GoldbachBoundaries.Paper2.M4a.Fill.scaledPinch_facts
import GoldbachBoundaries.Paper2.M4a.Fill.analyticOnNhd_bracket
import GoldbachBoundaries.Paper2.M4a.Fill.bracket_meromorphic_of_K4
import GoldbachBoundaries.Paper2.M4a.Fill.not_eventually_zero_of_eqOn_bracket

/-!
# M4a: hypothesis (H3) (`cl:thm:class`, its sufficient conditions; `cl:rem:order` for `k₀`)

All three targets go through one criterion (`H3_of_eventually`, real): near each point `s₀` of the line, every
scaled-zero pinch `α = L⁻¹(1 + ρ/n)` (`n` prime) close to `s₀` has `X_α ≢ 0` on `D_L`; such pinches exist in every
disc (`prop_catalogue_ii_proof`).

* **From the bracket** (`thm_class_H3_of_bracket`): the meromorphic extension `f` of `𝔟` is not `≡ 0` near `s₀`, so
  `f ≠ 0` on a punctured disc; a pinch `α` there is in `D_L`, so `𝔟(α) = f(α) ≠ 0`, and
  `X'_α(α) = ℓc₁c_b𝔟(α) ≠ 0` (`lem_J_ii_proof`, `lem_P_iv_values_proof`), so `X_α ≢ 0`.
* **Under (K4)** (`thm_class_H3_of_K4`): `𝔟 = k(1, ·) + k(L(·) - 1, ·)` is the sum of two line restrictions
  (`Restrict.lean`), patched with `𝔟` on `D_L`; it is not `≡ 0` near `s₀` because `𝔟 ≢ 0` on the connected `D_L`.
* **For `k₀`** (`rem_order_H3`): `𝔟 ≡ 0`, but `X_{1+b} = c₁c_b(b - 1)/b · δ² + O(δ³)` with a non-zero leading
  coefficient (`rem_order_coeff_proof`).
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M4a

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-! ## Lemmas

Proved in `Fill/`, one file per lemma (same name, same statement): `scaledPinch_facts`, `analyticOnNhd_bracket`, `bracket_meromorphic_of_K4`, `not_eventually_zero_of_eqOn_bracket`. -/

/-! ## Real lemmas -/

/-- **(H3) from a local criterion at the scaled-zero pinches** (RH, through `prop_catalogue_ii_proof`). -/
lemma H3_of_eventually (hRH : RiemannHypothesis) (A : Aff) (k : ℂ → ℂ → ℂ)
    (h : ∀ s₀ ∈ A.lineL, ∃ r₁ : ℝ, 0 < r₁ ∧ ∀ α ∈ ball s₀ r₁, ∀ ρ ∈ NontrivialZeros, ∀ n : ℕ, n.Prime →
      A.app α = 1 + ρ / (n : ℂ) → ∃ s ∈ A.DL, Xcoef A k α s ≠ 0) :
    H3 A k := by
  intro s₀ hs₀ r hr
  obtain ⟨r₁, hr₁, h₁⟩ := h s₀ hs₀
  obtain ⟨α, ρ, hρ, n, hn, hα, hball⟩ :=
    ((prop_catalogue_ii_proof hRH A s₀ hs₀ (min r r₁) (lt_min hr hr₁)).1).nonempty
  refine ⟨α, (scaledPinch_facts A hρ hn.one_lt.le hn.squarefree hα).2.2.2.2.2.2, ?_,
    h₁ α (ball_subset_ball (min_le_right _ _) hball) ρ hρ n hn hα⟩
  rw [mem_ball, dist_eq_norm] at hball
  exact lt_of_lt_of_le hball (min_le_left _ _)

/-! ## Targets -/

/-- `thm_class_H3_of_bracket` of `Paper2/Statements.lean`, statement verbatim. -/
theorem thm_class_H3_of_bracket_proof (hRH : RiemannHypothesis) (hZ1 : Z1) (A : Aff) (k : ℂ → ℂ → ℂ)
    (hK1 : K1 A k)
    (hb : ∀ s₀ ∈ A.lineL, ∃ r : ℝ, 0 < r ∧ ∃ f : ℂ → ℂ, MeromorphicOn f (ball s₀ r) ∧
      EqOn f (bracket A k) (ball s₀ r ∩ A.DL) ∧ ¬ (∀ᶠ s in 𝓝[≠] s₀, f s = 0)) :
    H3 A k := by
  apply H3_of_eventually hRH A k
  intro s₀ hs₀
  obtain ⟨r, hr, f, hfm, hfeq, hfne⟩ := hb s₀ hs₀
  have hev : ∀ᶠ s in 𝓝[≠] s₀, f s ≠ 0 :=
    ((hfm s₀ (mem_ball_self hr)).eventually_eq_zero_or_eventually_ne_zero).resolve_left hfne
  obtain ⟨r₂, hr₂, h₂⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hev)
  refine ⟨min r r₂, lt_min hr hr₂, fun α hα ρ hρ n hn hαe => ?_⟩
  obtain ⟨hcat, hDL, hnline, hbS, hb1, hbe, -⟩ := scaledPinch_facts A hρ hn.one_lt.le hn.squarefree hαe
  have hαne : α ≠ s₀ := fun h => hnline (h ▸ hs₀)
  have hbr : bracket A k α ≠ 0 := by
    rw [← hfeq ⟨ball_subset_ball (min_le_left _ _) hα, hDL⟩]
    exact h₂ (lt_of_lt_of_le (mem_ball.mp hα) (min_le_right _ _)) hαne
  have hb1' : A.app α - 1 ≠ 1 := by rw [hbe]; exact hb1
  have hd := (lem_J_ii_proof hRH A k hK1 hcat).2.2.2.1 hb1'
  have hcb : cP (A.app α - 1) ≠ 0 := ((lem_P_iv_values_proof hRH hZ1).1 _ (hbe ▸ hbS)).2.2
  have hl : (A.ell : ℂ) ≠ 0 := by exact_mod_cast A.ell_pos.ne'
  have hne : (A.ell : ℂ) * cP 1 * cP (A.app α - 1) * bracket A k α ≠ 0 := by
    rw [(lem_P_iv_values_proof hRH hZ1).2.1]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hl (neg_ne_zero.mpr one_ne_zero)) hcb) hbr
  exact exists_ne_zero_of_hasDerivAt hd hne ((isOpen_DL A).mem_nhds hDL)

/-- `thm_class_H3_of_K4` of `Paper2/Statements.lean`, statement verbatim. -/
theorem thm_class_H3_of_K4_proof (hRH : RiemannHypothesis) (hZ1 : Z1) (A : Aff) (k : ℂ → ℂ → ℂ)
    (hK1 : K1 A k) (hK4 : K4 k) (hb : ∃ s ∈ A.DL, bracket A k s ≠ 0) : H3 A k := by
  refine thm_class_H3_of_bracket_proof hRH hZ1 A k hK1 fun s₀ hs₀ => ?_
  obtain ⟨r, hr, f, hfm, hfeq⟩ := bracket_meromorphic_of_K4 A k hK1 hK4 s₀ hs₀
  exact ⟨r, hr, f, hfm, hfeq, not_eventually_zero_of_eqOn_bracket A k hK1 hb hs₀ hr hfeq⟩

/-- `rem_order_H3` of `Paper2/Statements.lean`, statement verbatim. -/
theorem rem_order_H3_proof (hRH : RiemannHypothesis) (hZ1 : Z1) : H3 Aff.idL k0 := by
  apply H3_of_eventually hRH Aff.idL k0
  intro s₀ _
  refine ⟨1, one_pos, fun α _ ρ hρ n hn hαe => ?_⟩
  obtain ⟨-, hDL, -, hbS, hb1, -, -⟩ := scaledPinch_facts Aff.idL hρ hn.one_lt.le hn.squarefree hαe
  rw [app_idL] at hαe
  subst hαe
  have hb0 : ρ / (n : ℂ) ≠ 0 := fun h => by
    have := (poleSetQ_re_bounds hbS).1; rw [h] at this; simp at this
  have hc : cP 1 * cP (ρ / (n : ℂ)) * ((ρ / (n : ℂ) - 1) / (ρ / (n : ℂ))) ≠ 0 := by
    rw [(lem_P_iv_values_proof hRH hZ1).2.1]
    exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr one_ne_zero)
      ((lem_P_iv_values_proof hRH hZ1).1 _ hbS).2.2) (div_ne_zero (sub_ne_zero.mpr hb1) hb0)
  exact exists_ne_zero_of_isBigO_pow hc ((rem_order_coeff_proof hRH).1 _ ⟨hbS, hb1⟩)
    ((isOpen_DL Aff.idL).mem_nhds hDL)

end GoldbachBoundaries.Paper2.M4a
