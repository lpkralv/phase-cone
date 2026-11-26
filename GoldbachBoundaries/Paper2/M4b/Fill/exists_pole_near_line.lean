import GoldbachBoundaries.Paper2.M4b.Mero

/-! Filler for `exists_pole_near_line` (M4b, group C2). The argument of M4a's `thm_class_H3_of_bracket_proof`. -/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M4b

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **Poles of `D^log` accumulate at every point of the line** (RH, (K1), (K2), (R), (K4), `𝔟 ≢ 0`). Fix
`ε > 0`. M4a's `bracket_meromorphic_of_K4` gives `r > 0` and `f` meromorphic on `ball s₀ r` with `f = 𝔟` on
`ball s₀ r ∩ D_L`; `not_eventually_zero_of_eqOn_bracket` (with `hb`) says `f` is not eventually `0` at `s₀`, so
(`MeromorphicAt.eventually_eq_zero_or_eventually_ne_zero`) `f ≠ 0` on a punctured ball `ball s₀ r₂ ∖ {s₀}`. By M4a's
`prop_catalogue_ii_proof` there is a scaled-zero pinch `α`, `L(α) = 1 + ρ/n` with `n` prime, in
`ball s₀ (min ε (min r r₂))`. M4a's `scaledPinch_facts`: `α ∈ D_L`, `α ∉` the line (so `α ≠ s₀`),
`b = ρ/n ∈ Σ_Q ∖ {1}`, `L(α) - 1 = b`; under RH `Re L(α) = 1 + 1/(2n) < 2`, so `α ∈ stripL`, and
`𝔟(α) = f(α) ≠ 0`. Then `Fmero_strip_facts` gives `meromorphicOrderAt (Fmero A k W) α < 0`, and
`eventuallyEq_Fmero` (`meromorphicOrderAt_congr`) transfers it to `F`. `α ∈ ℍ_L` since `Re L(α) > 1`. (The same
argument as M4a's `thm_class_H3_of_bracket_proof`.) Size: 100–200 lines. -/
theorem exists_pole_near_line (hRH : RiemannHypothesis) (A : Aff) (k : ℂ → ℂ → ℂ) (W : ℂ → ℕ → ℕ → ℂ)
    (hK1 : K1 A k) (hK2 : K2 A k) (hR : HypR A k W Q) (hK4 : K4 k) (hb : ∃ s ∈ A.DL, bracket A k s ≠ 0)
    {F : ℂ → ℂ} (hF : MeromorphicOn F A.HL) (hFW : F =ᶠ[codiscreteWithin A.RL] Dser W) {s₀ : ℂ}
    (hs₀ : s₀ ∈ A.lineL) :
    ∀ ε > 0, ∃ a ∈ A.HL, a ≠ s₀ ∧ a ∈ ball s₀ ε ∧ meromorphicOrderAt F a < 0 := by
  intro ε hε
  obtain ⟨r, hr, f, hfm, hfeq⟩ := M4a.bracket_meromorphic_of_K4 A k hK1 hK4 s₀ hs₀
  have hne := M4a.not_eventually_zero_of_eqOn_bracket A k hK1 hb hs₀ hr hfeq
  have hev : ∀ᶠ s in 𝓝[≠] s₀, f s ≠ 0 :=
    ((hfm s₀ (mem_ball_self hr)).eventually_eq_zero_or_eventually_ne_zero).resolve_left hne
  obtain ⟨r₂, hr₂, h₂⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hev)
  have hδ : 0 < min ε (min r r₂) := lt_min hε (lt_min hr hr₂)
  obtain ⟨α, ρ, hρ, n, hn, hαe, hball⟩ :=
    ((M4a.prop_catalogue_ii_proof hRH A s₀ hs₀ _ hδ).1).nonempty
  obtain ⟨-, hDL, hnline, hbS, hb1, -, -⟩ := M4a.scaledPinch_facts A hρ hn.one_lt.le hn.squarefree hαe
  have hdist : dist α s₀ < min ε (min r r₂) := mem_ball.mp hball
  have hαne : α ≠ s₀ := fun h => hnline (h ▸ hs₀)
  have hbr : bracket A k α ≠ 0 := by
    rw [← hfeq ⟨mem_ball.mpr (lt_of_lt_of_le hdist ((min_le_right _ _).trans (min_le_left _ _))), hDL⟩]
    exact h₂ (lt_of_lt_of_le hdist ((min_le_right _ _).trans (min_le_right _ _))) hαne
  -- under RH, `Re(ρ/n) ≤ 1/2`, so `α` lies in the strip `1 < Re L < 2`
  have hhalf : (ρ / (n : ℂ)).re ≤ 1 / 2 := by
    refine not_lt.mp fun h => hb1 ?_
    have hmem : ρ / (n : ℂ) ∈ PoleSetQ ∩ halfPlane (1 / 2) := ⟨hbS, h⟩
    rw [(lem_Sigma_iv_proof hRH).1] at hmem
    exact hmem
  have hst : α ∈ stripL A := by
    refine ⟨hDL.1, ?_⟩
    rw [hαe, add_re, one_re]
    linarith
  have hord : meromorphicOrderAt (Fmero A k W) α < 0 :=
    ((Fmero_strip_facts hRH A k W hK1 hK2).1 α hst).2.mpr ⟨ρ / (n : ℂ), ⟨hbS, hb1⟩, hαe, hbr⟩
  have hαHL : α ∈ A.HL := hDL.1
  refine ⟨α, hαHL, hαne, mem_ball.mpr (lt_of_lt_of_le hdist (min_le_left _ _)), ?_⟩
  rw [meromorphicOrderAt_congr (eventuallyEq_Fmero hRH A k W hK1 hK2 hR hF hFW α hαHL)]
  exact hord

end GoldbachBoundaries.Paper2.M4b
