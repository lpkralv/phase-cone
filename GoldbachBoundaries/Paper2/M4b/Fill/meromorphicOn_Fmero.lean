import GoldbachBoundaries.Paper2.M4b.Fill.differentiableOn_Iminus_Iplus
import GoldbachBoundaries.Paper2.M4b.Fill.Fmero_eq_strip
import GoldbachBoundaries.Paper2.M4b.Fill.Fmero_eq_upper

/-!
# M4b filler C1: `meromorphicOn_Fmero`

`ℍ_L ⊆ stripL ∪ upperL ∪ R_L`, three open sets; on each `Fmero` equals a meromorphic expression on the whole set.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M4b

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- **`D^log` continues meromorphically to `ℍ_L`** (RH, (K1), (K2), (R)). On the open `stripL`,
`Fmero = Iminus + 𝔟·Q(L - 1)` (`Fmero_eq_strip`); on the open `upperL`, `Fmero = Iplus + k(1,·)Q(L - 1)`
(`Fmero_eq_upper`); on the open `R_L`, `Fmero = Dser W` (`Fmero_of_RL`), holomorphic by (R). `Iminus`, `Iplus`
are holomorphic (`differentiableOn_Iminus_Iplus`), `𝔟` and `k(1, ·)` are holomorphic on `D_L`, and
`s ↦ Qcont(L(s) - 1)` is meromorphic on `ℍ_L` (`FillC1.meromorphicAt_Qcont_app`). -/
theorem meromorphicOn_Fmero (hRH : RiemannHypothesis) (A : Aff) (k : ℂ → ℂ → ℂ) (W : ℂ → ℕ → ℕ → ℂ)
    (hK1 : K1 A k) (hK2 : K2 A k) (hR : HypR A k W Q) : MeromorphicOn (Fmero A k W) A.HL := by
  intro s hs
  obtain ⟨hI, hIp⟩ := differentiableOn_Iminus_Iplus hRH A k hK1 hK2
  rcases HL_subset A hs with (hst | hup) | hRL
  · have hn : stripL A ∈ 𝓝 s := (isOpen_stripL A).mem_nhds hst
    have hev : (fun t => Iminus A k t + bracket A k t * Qcont (A.app t - 1)) =ᶠ[𝓝 s] Fmero A k W := by
      filter_upwards [hn] with t ht
      exact (Fmero_eq_strip hRH A k W hK1 hK2 ht).symm
    have hm : MeromorphicAt (fun t => Iminus A k t + bracket A k t * Qcont (A.app t - 1)) s :=
      (hI.analyticAt hn).meromorphicAt.add
        ((M4a.analyticOnNhd_bracket A k hK1 s (stripL_subset_DL A hst)).meromorphicAt.mul
          (FillC1.meromorphicAt_Qcont_app A hs))
    exact hm.congr (hev.filter_mono nhdsWithin_le_nhds)
  · have hn : upperL A ∈ 𝓝 s := (isOpen_upperL A).mem_nhds hup
    have hev : (fun t => Iplus A k t + k 1 t * Qcont (A.app t - 1)) =ᶠ[𝓝 s] Fmero A k W := by
      filter_upwards [hn] with t ht
      exact (Fmero_eq_upper hRH A k W hK1 hK2 hR ht).symm
    have hm : MeromorphicAt (fun t => Iplus A k t + k 1 t * Qcont (A.app t - 1)) s :=
      (hIp.analyticAt hn).meromorphicAt.add
        ((FillC1.analyticOnNhd_k_one A k hK1 s (upperL_subset_DL A hup)).meromorphicAt.mul
          (FillC1.meromorphicAt_Qcont_app A hs))
    exact hm.congr (hev.filter_mono nhdsWithin_le_nhds)
  · have hn : A.RL ∈ 𝓝 s := (isOpen_RL A).mem_nhds hRL
    have hev : Dser W =ᶠ[𝓝 s] Fmero A k W := by
      filter_upwards [hn] with t ht
      exact (Fmero_of_RL A k W ht).symm
    exact (hR.2.1.analyticAt hn).meromorphicAt.congr (hev.filter_mono nhdsWithin_le_nhds)

end GoldbachBoundaries.Paper2.M4b
