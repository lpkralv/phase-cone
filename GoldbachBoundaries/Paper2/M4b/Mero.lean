import GoldbachBoundaries.Paper2.M4b.Rising
import GoldbachBoundaries.Paper2.M4b.Fill.norm_integrand_le_far
import GoldbachBoundaries.Paper2.M4b.Fill.differentiableAt_integrand
import GoldbachBoundaries.Paper2.M4b.Fill.differentiableOn_Ilog
import GoldbachBoundaries.Paper2.M4b.Fill.Ilog_eq_of_no_pole
import GoldbachBoundaries.Paper2.M4b.Fill.isBigO_mul_sub_residue
import GoldbachBoundaries.Paper2.M4b.Fill.Ilog_step_one
import GoldbachBoundaries.Paper2.M4b.Fill.Ilog_step_sub_one
import GoldbachBoundaries.Paper2.M4b.Fill.differentiableOn_Iminus_Iplus
import GoldbachBoundaries.Paper2.M4b.Fill.Fmero_eq_upper
import GoldbachBoundaries.Paper2.M4b.Fill.Fmero_eq_strip
import GoldbachBoundaries.Paper2.M4b.Fill.meromorphicOn_Fmero
import GoldbachBoundaries.Paper2.M4b.Fill.mero_mul_Qcont_app
import GoldbachBoundaries.Paper2.M4b.Fill.Fmero_strip_facts
import GoldbachBoundaries.Paper2.M4b.Fill.Fmero_upper_facts
import GoldbachBoundaries.Paper2.M4b.Fill.eventuallyEq_Fmero
import GoldbachBoundaries.Paper2.M4b.Fill.exists_differentiableOn_of_order_nonneg
import GoldbachBoundaries.Paper2.M4b.Fill.order_Fmero_nonneg

/-!
# M4b: Theorem E (`cl:thm:mero`) (i), (ii)

The paper's proof, made explicit (Section `cl:sec:mero`). Under RH the poles of `Q` in `Re z > 1/2` are only `z = 1`
(paper 1's `lem_Sigma_iv_proof`, `analyticAt_Qcont_of_RH`), and `|Q(w)| ≪ log |Im w|` on `Re w ≥ 1/2 + ε` (paper 1's
`norm_Qcont_le_log`). So on a line `Re z = c` with `1/2 < c`, `c ≠ 1`, `Re L(s) - c > 1/2`, `≠ 1`, the integrand
`k(z,s)Q(z)Q(L(s)-z)` has no pole and is `O((1+|y|)^{-3/2})` by (K2) (`norm_integrand_le_far`), uniformly for `s` in
compacts of `D_L`; that gives integrability and holomorphy in `s` (`differentiableOn_Ilog`). Three line moves:

* no pole between the lines (`Ilog_eq_of_no_pole`), so `I` and `I⁺` are holomorphic (`differentiableOn_Iminus_Iplus`);
* Step 2, across `z = 1` (`Ilog_step_one`): `D^log = I⁺ + k(1,s)Q(L(s)-1)` on `3/2 < Re L < 3` (`Fmero_eq_upper`);
* Step 3, across `z = L(s) - 1` (`Ilog_step_sub_one`): `I⁺ = I + k(L(s)-1,s)Q(L(s)-1)`, hence `(cl:eq:strip)` on
  `1 < Re L < 2` (`Fmero_eq_strip`).

`Fmero` (Defs) glues the three expressions; it is meromorphic on `ℍ_L` (`meromorphicOn_Fmero`), and its poles and
residues are those of `g(s)Q(L(s)-1)` with `g = 𝔟` or `g = k(1,·)` holomorphic (`mero_mul_Qcont_app`):
`Fmero_strip_facts`, `Fmero_upper_facts`. Any meromorphic `F` equal to the series off a discrete subset of `R_L`
equals `Fmero` near every point of `ℍ_L` (`eventuallyEq_Fmero`). For (ii), `Fmero` has order `≥ 0` everywhere when
`𝔟 ≡ 0` (`order_Fmero_nonneg`, using `k(1, s₂) = 𝔟(s₂)/2`), and its removable singularities are filled in by
`exists_differentiableOn_of_order_nonneg` (the point `s₂` is one: `k(1,s₂)Q(L(s₂)-1)` is `0·Q(1)` in Lean, not the
limit).

(Z1)-(Z3) of the signed-off statements are not used: under RH the growth of `Q` is paper 1's (review choice 2; a
premise that is not needed only strengthens the statement).
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M4b

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-! ## Lemmas: the integrand and the line integrals

Proved in `Fill/`, one file per lemma (same name, same statement): `norm_integrand_le_far`, `differentiableAt_integrand`, `differentiableOn_Ilog`, `Ilog_eq_of_no_pole`, `isBigO_mul_sub_residue`, `Ilog_step_one`, `Ilog_step_sub_one`. -/

/-! ## Lemmas: the continuation `Fmero`

Proved in `Fill/`, one file per lemma (same name, same statement): `differentiableOn_Iminus_Iplus`, `Fmero_eq_upper`, `Fmero_eq_strip`, `meromorphicOn_Fmero`, `mero_mul_Qcont_app`, `Fmero_strip_facts`, `Fmero_upper_facts`, `eventuallyEq_Fmero`, `exists_differentiableOn_of_order_nonneg`, `order_Fmero_nonneg`. -/

/-! ## Real lemmas -/

/-- A residue only depends on the function on a punctured neighbourhood. -/
lemma hasResidue_congr_nhdsNE {f g : ℂ → ℂ} {a c : ℂ} (h : HasResidue f a c) (hfg : f =ᶠ[𝓝[≠] a] g) :
    HasResidue g a c :=
  Tendsto.congr' (hfg.mono fun s hs => by simp only [hs]) h

/-! ## Targets -/

/-- `thm_mero_i` of `Paper2/Statements.lean`, statement verbatim. -/
theorem thm_mero_i_proof (hRH : RiemannHypothesis) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (A : Aff)
    (k : ℂ → ℂ → ℂ) (W : ℂ → ℕ → ℕ → ℂ) (hK1 : K1 A k) (hK2 : K2 A k) (hR : HypR A k W Q) :
    (∃ F : ℂ → ℂ, MeromorphicOn F A.HL ∧ EqOn F (Dser W) A.RL ∧
      ∃ I : ℂ → ℂ, DifferentiableOn ℂ I {s | 1 < (A.app s).re ∧ (A.app s).re < 2} ∧
        ∀ Qc : ℂ → ℂ, IsQCont Qc → ∀ s : ℂ, 1 < (A.app s).re → (A.app s).re < 2 →
          A.app s - 1 ∉ PoleSetQ → F s = I s + bracket A k s * Qc (A.app s - 1)) ∧
    ∀ F : ℂ → ℂ, MeromorphicOn F A.HL → F =ᶠ[codiscreteWithin A.RL] Dser W →
      (∀ s : ℂ, 1 < (A.app s).re → (A.app s).re < 2 → -1 ≤ meromorphicOrderAt F s ∧
        (meromorphicOrderAt F s < 0 ↔
          ∃ b ∈ PoleSetQ \ {1}, A.app s = 1 + b ∧ bracket A k s ≠ 0)) ∧
      (∀ b ∈ PoleSetQ \ {1}, ∀ α : ℂ, A.app α = 1 + b →
        HasResidue F α (Rcoef b * bracket A k α / A.ell)) ∧
      ∀ s₂ : ℂ, A.app s₂ = 2 → -1 ≤ meromorphicOrderAt F s₂ ∧
        HasResidue F s₂ (k 1 s₂ / A.ell) ∧ (k 1 s₂ = 0 → 0 ≤ meromorphicOrderAt F s₂) := by
  have _ := hZ1  -- (Z1)-(Z3) are not used: under RH the growth of `Q` is paper 1's `norm_Qcont_le_log`
  have _ := hZ2
  have _ := hZ3
  refine ⟨⟨Fmero A k W, meromorphicOn_Fmero hRH A k W hK1 hK2 hR, fun s hs => Fmero_of_RL A k W hs,
    Iminus A k, (differentiableOn_Iminus_Iplus hRH A k hK1 hK2).1, fun Qc hQc s h1 h2 hsQ => ?_⟩, ?_⟩
  · rw [Fmero_eq_strip hRH A k W hK1 hK2 ⟨h1, h2⟩]
    have hpos : 0 < (A.app s - 1).re := by rw [sub_re, one_re]; linarith
    rw [(isQCont_eventuallyEq hQc).1 _ ⟨hpos, hsQ⟩]
  · intro F hF hFW
    have hev := eventuallyEq_Fmero hRH A k W hK1 hK2 hR hF hFW
    obtain ⟨hstrip, hres⟩ := Fmero_strip_facts hRH A k W hK1 hK2
    have hs2 := (Fmero_upper_facts hRH A k W hK1 hK2 hR).1
    refine ⟨fun s h1 h2 => ?_, fun b hb α hα => ?_, fun s₂ hs₂ => ?_⟩
    · rw [meromorphicOrderAt_congr (hev s h1)]
      exact hstrip s ⟨h1, h2⟩
    · have hαHL : α ∈ A.HL := by
        show 1 < (A.app α).re
        rw [hα, add_re, one_re]
        linarith [(poleSetQ_re_bounds hb.1).1]
      exact hasResidue_congr_nhdsNE (hres b hb α hα) (hev α hαHL).symm
    · have hs₂HL : s₂ ∈ A.HL := by
        show 1 < (A.app s₂).re
        rw [hs₂]; norm_num
      obtain ⟨h1, h2, h3⟩ := hs2 s₂ hs₂
      rw [meromorphicOrderAt_congr (hev s₂ hs₂HL)]
      exact ⟨h1, hasResidue_congr_nhdsNE h2 (hev s₂ hs₂HL).symm, h3⟩

/-- `thm_mero_ii` of `Paper2/Statements.lean`, statement verbatim. -/
theorem thm_mero_ii_proof (hRH : RiemannHypothesis) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (A : Aff)
    (k : ℂ → ℂ → ℂ) (W : ℂ → ℕ → ℕ → ℂ) (hK1 : K1 A k) (hK2 : K2 A k) (hR : HypR A k W Q)
    (hb : ∀ s ∈ A.DL, bracket A k s = 0) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F A.HL ∧ EqOn F (Dser W) A.RL := by
  have _ := hZ1  -- (Z1)-(Z3) are not used, as in `thm_mero_i_proof`
  have _ := hZ2
  have _ := hZ3
  obtain ⟨g, hg, hgeq⟩ := exists_differentiableOn_of_order_nonneg (M4a.isOpen_HL A)
    (meromorphicOn_Fmero hRH A k W hK1 hK2 hR) (order_Fmero_nonneg hRH A k W hK1 hK2 hR hb)
  refine ⟨g, hg, fun s hs => ?_⟩
  have hs' : 2 < (A.app s).re := hs
  have hsHL : s ∈ A.HL := by show 1 < (A.app s).re; linarith
  have hs2 : A.app s ≠ 2 := fun h => by rw [h] at hs'; norm_num at hs'
  rw [hgeq s hsHL ((Fmero_upper_facts hRH A k W hK1 hK2 hR).2 s (Or.inr hs) hs2),
    Fmero_of_RL A k W hs']

end GoldbachBoundaries.Paper2.M4b
