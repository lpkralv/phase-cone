import GoldbachBoundaries.Paper2.M4b.Fill.C2Common
import GoldbachBoundaries.Paper2.M4b.Fill.differentiableOn_Iminus_Iplus
import GoldbachBoundaries.Paper2.M4b.Fill.Fmero_eq_strip

/-! Filler for `Fmero_strip_facts` (M4b, group C2). -/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M4b

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- On the strip, `Fmero` agrees near `s` with `Iminus + 𝔟·Q(L - 1)`, and both summands but `Q(L-1)` are analytic. -/
lemma FillC2.strip_local (hRH : RiemannHypothesis) (A : Aff) (k : ℂ → ℂ → ℂ) (W : ℂ → ℕ → ℕ → ℂ)
    (hK1 : K1 A k) (hK2 : K2 A k) {s : ℂ} (hs : s ∈ stripL A) :
    Fmero A k W =ᶠ[𝓝 s] (fun t => Iminus A k t + bracket A k t * Qcont (A.app t - 1)) ∧
      AnalyticAt ℂ (Iminus A k) s ∧ AnalyticAt ℂ (bracket A k) s := by
  have hn : stripL A ∈ 𝓝 s := (isOpen_stripL A).mem_nhds hs
  refine ⟨Filter.mem_of_superset hn fun t ht => Fmero_eq_strip hRH A k W hK1 hK2 ht,
    (differentiableOn_Iminus_Iplus hRH A k hK1 hK2).1.analyticAt hn,
    M4a.analyticOnNhd_bracket A k hK1 s (stripL_subset_DL A hs)⟩

lemma FillC2.Rcoef_ne_zero (hRH : RiemannHypothesis) {b : ℂ} (hb : b ∈ PoleSetQ) : Rcoef b ≠ 0 := fun h =>
  M4a.cP_ne_zero_of_RH hRH hb (by simp [cP, h])

/-- Under RH a point of `Σ_Q ∖ {1}` has real part in `(0, 1/2]`. -/
lemma FillC2.re_le_half (hRH : RiemannHypothesis) {b : ℂ} (hb : b ∈ PoleSetQ \ {1}) :
    0 < b.re ∧ b.re ≤ 1 / 2 := by
  refine ⟨(poleSetQ_re_bounds hb.1).1, not_lt.mp fun h => hb.2 ?_⟩
  have hmem : b ∈ PoleSetQ ∩ halfPlane (1 / 2) := ⟨hb.1, h⟩
  rw [(lem_Sigma_iv_proof hRH).1] at hmem
  exact hmem

/-- **Poles and residues in the strip** (RH, (K1), (K2)). On the open `stripL`, `Fmero = Iminus + 𝔟·Q(L - 1)`
(`Fmero_eq_strip`), so orders and residues are those of this expression (`meromorphicOrderAt_congr`). If
`b = L(s) - 1 ∉ Σ_Q` (`Re b ∈ (0, 1)`), `Qcont` is analytic at `b`, so the order is `≥ 0` and there is no `b` in the
right side (`b ∈ Σ_Q` is false). If `b ∈ Σ_Q`, `b ≠ 1` (`Re b < 1`) and `mero_mul_Qcont_app` with `g = 𝔟` (holomorphic on
`D_L`, M4a's `analyticOnNhd_bracket`) plus the holomorphic `Iminus` give order `≥ -1`, residue `𝔟(α)R_b/ℓ`, and a pole
iff `𝔟(α)R_b ≠ 0`, i.e. iff `𝔟(α) ≠ 0`, since `R_b = -c_b ≠ 0` under RH (M4a's `cP_ne_zero_of_RH`). Residues: for
`b ∈ Σ_Q ∖ {1}`, under RH `0 < Re b ≤ 1/2` (paper 1's `lem_Sigma_iv_proof`, M1's `poleSetQ_re_bounds`), so `α` with
`L(α) = 1 + b` lies in `stripL`. Size: 150–250 lines. -/
theorem Fmero_strip_facts (hRH : RiemannHypothesis) (A : Aff) (k : ℂ → ℂ → ℂ) (W : ℂ → ℕ → ℕ → ℂ)
    (hK1 : K1 A k) (hK2 : K2 A k) :
    (∀ s ∈ stripL A, -1 ≤ meromorphicOrderAt (Fmero A k W) s ∧
      (meromorphicOrderAt (Fmero A k W) s < 0 ↔
        ∃ b ∈ PoleSetQ \ {1}, A.app s = 1 + b ∧ bracket A k s ≠ 0)) ∧
    ∀ b ∈ PoleSetQ \ {1}, ∀ α : ℂ, A.app α = 1 + b →
      HasResidue (Fmero A k W) α (Rcoef b * bracket A k α / A.ell) := by
  have hl : (A.ell : ℂ) ≠ 0 := by exact_mod_cast A.ell_pos.ne'
  refine ⟨fun s hs => ?_, fun b hb α hα => ?_⟩
  · obtain ⟨hev, hI, hB⟩ := FillC2.strip_local hRH A k W hK1 hK2 hs
    have hord := meromorphicOrderAt_congr (hev.filter_mono nhdsWithin_le_nhds)
    rw [hord]
    have hre0 : 0 < (A.app s - 1).re := by rw [sub_re, one_re]; linarith [hs.1]
    by_cases hbP : A.app s - 1 ∈ PoleSetQ
    · have hα : A.app s = 1 + (A.app s - 1) := by ring
      obtain ⟨hm, hr⟩ := FillC2.add_mul_Qcont_app_facts A hI hB hbP hα
      have hb1 : A.app s - 1 ≠ 1 := fun h => by
        have := congrArg Complex.re h
        rw [sub_re, one_re] at this
        linarith [hs.2]
      refine ⟨hr.neg_one_le_meromorphicOrderAt hm, ?_⟩
      rw [FillC2.order_neg_iff_of_hasResidue hm hr]
      have hR := FillC2.Rcoef_ne_zero hRH hbP
      constructor
      · intro h
        refine ⟨A.app s - 1, ⟨hbP, hb1⟩, hα, fun h0 => h ?_⟩
        rw [h0, zero_mul, zero_div]
      · rintro ⟨b', -, hb', hne⟩
        exact div_ne_zero (mul_ne_zero hne hR) hl
    · have han : AnalyticAt ℂ (fun t => Iminus A k t + bracket A k t * Qcont (A.app t - 1)) s := by
        have hQ : AnalyticAt ℂ Qcont (A.app s - 1) := E1_analyticAt_Qcont hre0 hbP
        have hap : AnalyticAt ℂ (fun t => A.app t - 1) s := by unfold Aff.app; fun_prop
        exact hI.add (hB.mul (hQ.comp_of_eq hap rfl))
      have h0 := han.meromorphicOrderAt_nonneg
      refine ⟨le_trans (by decide) h0, ⟨fun h => absurd h (not_lt.mpr h0), ?_⟩⟩
      rintro ⟨b', hb', hb'e, -⟩
      exact absurd (by rw [hb'e]; ring_nf; exact hb'.1 : A.app s - 1 ∈ PoleSetQ) hbP
  · obtain ⟨hb0, hbh⟩ := FillC2.re_le_half hRH hb
    have hs : α ∈ stripL A := by
      have h := congrArg Complex.re hα
      rw [add_re, one_re] at h
      exact ⟨by linarith, by linarith⟩
    obtain ⟨hev, hI, hB⟩ := FillC2.strip_local hRH A k W hK1 hK2 hs
    obtain ⟨-, hr⟩ := FillC2.add_mul_Qcont_app_facts A hI hB hb.1 hα
    rw [show Rcoef b * bracket A k α / A.ell = bracket A k α * Rcoef b / A.ell by ring]
    exact hr.congr (hev.filter_mono nhdsWithin_le_nhds).symm

end GoldbachBoundaries.Paper2.M4b
