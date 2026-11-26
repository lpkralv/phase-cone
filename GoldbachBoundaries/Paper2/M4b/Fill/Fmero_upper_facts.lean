import GoldbachBoundaries.Paper2.M4b.Fill.C2Common
import GoldbachBoundaries.Paper2.M4b.Fill.differentiableOn_Iminus_Iplus
import GoldbachBoundaries.Paper2.M4b.Fill.Fmero_eq_upper

/-! Filler for `Fmero_upper_facts` (M4b, group C2). -/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M4b

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- On `upperL`, `Fmero` agrees near `s` with `Iplus + k(1,·)Q(L - 1)`, and `Iplus`, `k(1, ·)` are analytic at `s`. -/
lemma FillC2.upper_local (hRH : RiemannHypothesis) (A : Aff) (k : ℂ → ℂ → ℂ) (W : ℂ → ℕ → ℕ → ℂ)
    (hK1 : K1 A k) (hK2 : K2 A k) (hR : HypR A k W Q) {s : ℂ} (hs : s ∈ upperL A) :
    Fmero A k W =ᶠ[𝓝 s] (fun t => Iplus A k t + k 1 t * Qcont (A.app t - 1)) ∧
      AnalyticAt ℂ (Iplus A k) s ∧ AnalyticAt ℂ (fun t => k 1 t) s := by
  have hn : upperL A ∈ 𝓝 s := (isOpen_upperL A).mem_nhds hs
  refine ⟨Filter.mem_of_superset hn fun t ht => Fmero_eq_upper hRH A k W hK1 hK2 hR ht,
    (differentiableOn_Iminus_Iplus hRH A k hK1 hK2).2.analyticAt hn, ?_⟩
  have hd : DifferentiableOn ℂ (fun t => k 1 t) A.DL := by
    intro t ht
    have hd := M4a.FillE.differentiableAt_of_K1 hK1 ht (M4a.FillE.one_mem_Str ht).1
      (M4a.FillE.one_mem_Str ht).2
    have hc : DifferentiableAt ℂ (fun u : ℂ => ((1 : ℂ), u)) t := by fun_prop
    exact (DifferentiableAt.comp (g := fun p : ℂ × ℂ => k p.1 p.2) (f := fun u : ℂ => ((1 : ℂ), u)) t hd
      hc).differentiableWithinAt
  exact hd.analyticAt ((M4a.isOpen_DL A).mem_nhds (upperL_subset_DL A hs))

/-- **The pinch `s₂` and the rest of `3/2 < Re L`** (RH, (K1), (K2), (R)). On the open `upperL`,
`Fmero = Iplus + k(1,·)Q(L - 1)` (`Fmero_eq_upper`). The only point of `Σ_Q` with real part in `(1/2, 2)` is `1`
(RH), so `Q(L(s) - 1)` is analytic on `upperL` except at `s₂` (`L(s₂) = 2`, `Re = 2 ∈ (3/2, 3)`), and `Fmero` is analytic
at every other point of `upperL`; on `R_L` it is the holomorphic series ((R), `Fmero_of_RL`). At `s₂`:
`mero_mul_Qcont_app` with `g = k(1, ·)` (holomorphic on `D_L` by (K1), `1 ∈ Str(s)`) and `b = 1`, `R_1 = 1`
(`Rcoef_one'`): order `≥ -1`, residue `k(1,s₂)/ℓ`, and order `≥ 0` when `k(1,s₂) = 0`. Size: 100–200 lines. -/
theorem Fmero_upper_facts (hRH : RiemannHypothesis) (A : Aff) (k : ℂ → ℂ → ℂ) (W : ℂ → ℕ → ℕ → ℂ)
    (hK1 : K1 A k) (hK2 : K2 A k) (hR : HypR A k W Q) :
    (∀ s₂ : ℂ, A.app s₂ = 2 → -1 ≤ meromorphicOrderAt (Fmero A k W) s₂ ∧
      HasResidue (Fmero A k W) s₂ (k 1 s₂ / A.ell) ∧
      (k 1 s₂ = 0 → 0 ≤ meromorphicOrderAt (Fmero A k W) s₂)) ∧
    ∀ s ∈ upperL A ∪ A.RL, A.app s ≠ 2 → AnalyticAt ℂ (Fmero A k W) s := by
  refine ⟨fun s₂ hs₂ => ?_, fun s hs hs2 => ?_⟩
  · have hs : s₂ ∈ upperL A := by
      show 3 / 2 < (A.app s₂).re ∧ (A.app s₂).re < 3
      rw [hs₂]; norm_num
    obtain ⟨hev, hI, hk⟩ := FillC2.upper_local hRH A k W hK1 hK2 hR hs
    have h1P : (1 : ℂ) ∈ PoleSetQ := Or.inl (Or.inl rfl)
    have hα : A.app s₂ = 1 + 1 := by rw [hs₂]; norm_num
    obtain ⟨hm, hr⟩ := FillC2.add_mul_Qcont_app_facts A hI hk h1P hα
    rw [Rcoef_one', mul_one] at hr
    have hord := meromorphicOrderAt_congr (hev.filter_mono nhdsWithin_le_nhds)
    rw [hord]
    refine ⟨hr.neg_one_le_meromorphicOrderAt hm, hr.congr (hev.filter_mono nhdsWithin_le_nhds).symm,
      fun h0 => ?_⟩
    have := (FillC2.order_neg_iff_of_hasResidue hm hr).not.mpr (by rw [h0, zero_div]; exact not_not.mpr rfl)
    exact not_lt.mp this
  · by_cases hRL : s ∈ A.RL
    · have hn : A.RL ∈ 𝓝 s := (isOpen_RL A).mem_nhds hRL
      have han : AnalyticAt ℂ (Dser W) s := hR.2.1.analyticAt hn
      refine han.congr (Filter.mem_of_superset hn fun t ht => ?_)
      exact (Fmero_of_RL A k W ht).symm
    · have hsu : s ∈ upperL A := hs.resolve_right hRL
      obtain ⟨hev, hI, hk⟩ := FillC2.upper_local hRH A k W hK1 hK2 hR hsu
      have hre : 1 / 2 < (A.app s - 1).re := by rw [sub_re, one_re]; linarith [hsu.1]
      have hne : A.app s - 1 ≠ 1 := fun h => hs2 (by linear_combination h)
      have hQ : AnalyticAt ℂ Qcont (A.app s - 1) := TIdentity.analyticAt_Qcont_of_RH hRH hre hne
      have hap : AnalyticAt ℂ (fun t => A.app t - 1) s := by unfold Aff.app; fun_prop
      exact (hI.add (hk.mul (hQ.comp_of_eq hap rfl))).congr hev.symm

end GoldbachBoundaries.Paper2.M4b
