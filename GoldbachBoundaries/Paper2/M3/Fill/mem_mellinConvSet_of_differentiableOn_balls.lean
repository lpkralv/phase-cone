import GoldbachBoundaries.Paper2.M3.Landau
import GoldbachBoundaries.Paper2.M3.Fill.measurable_phiH
import GoldbachBoundaries.Paper2.M3.Fill.laplaceConvSet_phiH
import GoldbachBoundaries.Paper2.M3.Fill.laplace_phiH_eq_Mcal

/-!
# Fill: `mem_mellinConvSet_of_differentiableOn_balls` (filler group F)

Step 2 of `nr:thm:test`. If some `x > a` were outside `S = mellinConvSet`, then `S` (an up-set containing every
`y > 2`) is bounded below by `x`, so `σ_c = sInf S ∈ (a, 2]`. The identity theorem on the preconnected set
`V = ⋃_{i ∈ [σ_c, 2]} ((Δ(i, r i) ∩ {Re > σ_c}) ∪ (σ_c, 2])` (each piece convex and meeting the real segment, all
containing `2`) gives `Mt = 𝓛 φ` on `Δ(σ_c, r σ_c) ∩ {Re > σ_c}`, contradicting Landau (`laplace_no_extension`).
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M3

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-- `mellinConvSet` is an up-set. -/
theorem mellinConvSet_upset_F {y y' : ℝ} (hy : y ∈ mellinConvSet) (hyy : y ≤ y') : y' ∈ mellinConvSet := by
  have hy' : IntegrableOn (fun t : ℝ => hErr t ^ 2 * t ^ (y - 1)) (Ioc (0 : ℝ) 1) := hy
  show IntegrableOn (fun t : ℝ => hErr t ^ 2 * t ^ (y' - 1)) (Ioc (0 : ℝ) 1)
  have hc : ContinuousOn (fun t : ℝ => hErr t ^ 2 * t ^ (y' - 1)) (Ioc (0 : ℝ) 1) := by
    refine ((TIdentity.continuousOn_hErr.mono Ioc_subset_Ioi_self).pow 2).mul ?_
    intro t ht
    exact (Real.continuousAt_rpow_const _ _ (Or.inl ht.1.ne')).continuousWithinAt
  refine Integrable.mono' hy' (hc.aestronglyMeasurable measurableSet_Ioc) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_
  have ht0 : 0 < t := ht.1
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg ht0.le _))]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge ht0 ht.2 (by linarith)) (sq_nonneg _)

/-- **Step 2 of `nr:thm:test`, in general form** (unconditional). Let `S = mellinConvSet = laplaceConvSet phiH`; it
contains every `x > 2` (`mem_mellinConvSet_of_two_lt`) and is an up-set. If `S` is not bounded below every real is in
it. Otherwise `σ_c = sInf S ≤ 2`, and it suffices to show `σ_c ≤ a` (then `x > a ≥ σ_c` gives some `y ∈ S`, `y < x`,
so `x ∈ S`). Suppose `σ_c > a`; then `σ_c ∈ (a, 2]` is a centre. `V = ballsU a 2 r ∩ {σ > σ_c}` is open and
connected: each `Δ(x, r x) ∩ {σ > σ_c}` is convex, and if non-empty contains a real point (the real part of any of its
points); the real points of `V` form an interval (a union of intervals `(x - r x, x + r x)` around the points of the
interval `(a, 2]`, intersected with `(σ_c, ∞)`). `𝓜 = 𝓛` is holomorphic on `{σ > σ_c}` (`laplace_phiH_eq_Mcal`,
`lem_Landau_proof` (ii) with `measurable_phiH`), `Mt` on `V`, and they agree on the non-empty open set
`V ∩ {σ > 2}` (it contains `2 + ε` for small `ε`), hence on `V` (`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`).
So `Mt` is holomorphic on `Δ(σ_c, r σ_c)` and equals `𝓛` on its right half, against `lem_Landau_proof` (iii).
Size: 200–350 lines. -/
theorem mem_mellinConvSet_of_differentiableOn_balls {a : ℝ} (ha : a < 2) {r : ℝ → ℝ}
    (hr : ∀ x ∈ Ioc a 2, 0 < r x) {Mt : ℂ → ℂ} (hMt : DifferentiableOn ℂ Mt (ballsU a 2 r))
    (hEq : EqOn Mt Mcal (ballsU a 2 r ∩ halfPlane 2)) : ∀ x : ℝ, a < x → x ∈ mellinConvSet := by
  intro x hax
  by_contra hxS
  have hlow : ∀ y ∈ mellinConvSet, x < y := fun y hy =>
    lt_of_not_ge fun hyx => hxS (mellinConvSet_upset_F hy hyx)
  have hne : mellinConvSet.Nonempty := ⟨3, mem_mellinConvSet_of_two_lt (by norm_num)⟩
  have hB : BddBelow mellinConvSet := ⟨x, fun y hy => (hlow y hy).le⟩
  set σ := sInf mellinConvSet with hσ
  have hxσ : x ≤ σ := le_csInf hne fun y hy => (hlow y hy).le
  have hσ2 : σ ≤ 2 :=
    le_of_forall_pos_le_add fun ε hε => csInf_le hB (mem_mellinConvSet_of_two_lt (by linarith))
  have hσI : σ ∈ Ioc a 2 := ⟨by linarith, hσ2⟩
  have hρ : 0 < r σ := hr σ hσI
  -- the Laplace side
  have hLS : laplaceConvSet phiH = mellinConvSet := laplaceConvSet_phiH
  have hφ0 : ∀ u, 0 < u → 0 ≤ phiH u := fun u _ => sq_nonneg _
  have hcov : ∀ s : ℂ, σ < s.re → ∃ y ∈ mellinConvSet, y < s.re := fun s hs => by
    obtain ⟨y, hy, hys⟩ := exists_lt_of_csInf_lt hne hs
    exact ⟨y, hy, hys⟩
  have hLdiff : DifferentiableOn ℂ (laplace phiH) (halfPlane σ) := by
    refine (differentiableOn_laplace phiH measurable_phiH hφ0).mono fun s hs => ?_
    show ∃ y ∈ laplaceConvSet phiH, y < s.re
    rw [hLS]; exact hcov s hs
  have hLM : ∀ s : ℂ, σ < s.re → laplace phiH s = Mcal s := fun s hs =>
    laplace_phiH_eq_Mcal (hcov s hs)
  have hballs_open : IsOpen (ballsU a 2 r) := isOpen_biUnion fun _ _ => isOpen_ball
  have hhalf_open : ∀ c : ℝ, IsOpen (halfPlane c) := fun c => isOpen_lt continuous_const continuous_re
  have hball_sub : ∀ i ∈ Ioc a 2, ball (i : ℂ) (r i) ⊆ ballsU a 2 r := fun i hi =>
    subset_biUnion_of_mem (u := fun j : ℝ => ball (j : ℂ) (r j)) hi
  -- key: `Mt = 𝓛 φ` on the right half of the disc about `σ`
  have hkey : EqOn Mt (laplace phiH) (ball (σ : ℂ) (r σ) ∩ halfPlane σ) := by
    rcases eq_or_lt_of_le hσ2 with h2 | h2
    · -- `σ = 2`: direct
      intro s hs
      have hs2 : 2 < s.re := by have := hs.2; simp only [halfPlane, mem_ofPred_eq] at this; linarith
      rw [hEq ⟨hball_sub σ hσI hs.1, hs2⟩, hLM s (by rw [h2]; exact hs2)]
    · -- `σ < 2`: identity theorem on a preconnected union
      have hIcc : ∀ i ∈ Icc σ 2, i ∈ Ioc a 2 := fun i hi => ⟨by linarith [hi.1], hi.2⟩
      let L : Set ℂ := ofReal '' Ioc σ 2
      let P : Icc σ 2 → Set ℂ := fun i => ball ((i : ℝ) : ℂ) (r i) ∩ halfPlane σ
      let V : Set ℂ := ⋃ i, (P i ∪ L)
      have h2L : (2 : ℂ) ∈ L := ⟨2, ⟨h2, le_rfl⟩, by simp⟩
      have hLpre : IsPreconnected L := isPreconnected_Ioc.image _ continuous_ofReal.continuousOn
      have hPL : ∀ i : Icc σ 2, (P i ∩ L).Nonempty := by
        rintro ⟨i, hi⟩
        have hri : 0 < r i := hr i (hIcc i hi)
        set t : ℝ := min 2 (i + r i / 2) with ht
        have hti : i ≤ t := le_min hi.2 (by linarith)
        have hti' : t ≤ i + r i / 2 := min_le_right _ _
        have htσ : σ < t := lt_min h2 (by linarith [hi.1])
        refine ⟨(t : ℂ), ⟨?_, ?_⟩, ⟨t, ⟨htσ, min_le_left _ _⟩, rfl⟩⟩
        · rw [mem_ball, dist_eq, ← ofReal_sub, norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
          linarith
        · show σ < (t : ℂ).re
          rw [ofReal_re]; exact htσ
      have hVpre : IsPreconnected V := by
        refine isPreconnected_iUnion ⟨2, mem_iInter.2 fun i => Or.inr h2L⟩ fun i => ?_
        exact IsPreconnected.union' (hPL i)
          ((convex_ball _ _).inter (convex_halfSpace_re_gt σ)).isPreconnected hLpre
      have hVsub : V ⊆ ballsU a 2 r ∩ halfPlane σ := by
        intro v hv
        obtain ⟨i, hv⟩ := mem_iUnion.mp hv
        rcases hv with hv | ⟨t, ht, rfl⟩
        · exact ⟨hball_sub i (hIcc i i.2) hv.1, hv.2⟩
        · have hta : t ∈ Ioc a 2 := ⟨by linarith [ht.1], ht.2⟩
          refine ⟨hball_sub t hta (mem_ball_self (hr t hta)), ?_⟩
          show σ < (t : ℂ).re
          rw [ofReal_re]; exact ht.1
      have hMtA : AnalyticOnNhd ℂ Mt V := fun v hv =>
        hMt.analyticAt (hballs_open.mem_nhds (hVsub hv).1)
      have hLA : AnalyticOnNhd ℂ (laplace phiH) V := fun v hv =>
        hLdiff.analyticAt ((hhalf_open σ).mem_nhds (hVsub hv).2)
      -- agreement near `z₁ = 2 + r 2 / 2`
      have h2I : (2 : ℝ) ∈ Icc σ 2 := ⟨hσ2, le_rfl⟩
      have hr2 : 0 < r 2 := hr 2 (hIcc 2 h2I)
      set z₁ : ℂ := ((2 + r 2 / 2 : ℝ) : ℂ) with hz₁
      have hz₁O : z₁ ∈ ball ((2 : ℝ) : ℂ) (r 2) ∩ halfPlane 2 := by
        refine ⟨?_, ?_⟩
        · rw [hz₁, mem_ball, dist_eq, ← ofReal_sub, norm_real, Real.norm_eq_abs,
            abs_of_nonneg (by linarith)]
          linarith
        · show 2 < z₁.re
          rw [hz₁, ofReal_re]; linarith
      have hz₁V : z₁ ∈ V :=
        mem_iUnion.2 ⟨⟨2, h2I⟩, Or.inl ⟨hz₁O.1, by
          show σ < z₁.re
          rw [hz₁, ofReal_re]; linarith⟩⟩
      have hev : Mt =ᶠ[𝓝 z₁] laplace phiH := by
        filter_upwards [(isOpen_ball.inter (hhalf_open 2)).mem_nhds hz₁O] with s hs
        have hs2 : 2 < s.re := hs.2
        rw [hEq ⟨hball_sub 2 (hIcc 2 h2I) hs.1, hs.2⟩, hLM s (by linarith)]
      have hEqV := hMtA.eqOn_of_preconnected_of_eventuallyEq hLA hVpre hz₁V hev
      intro s hs
      exact hEqV (mem_iUnion.2 ⟨⟨σ, ⟨le_rfl, hσ2⟩⟩, Or.inl hs⟩)
  -- contradiction with Landau
  have hS' : (laplaceConvSet phiH).Nonempty := by rw [hLS]; exact hne
  have hB' : BddBelow (laplaceConvSet phiH) := by rw [hLS]; exact hB
  apply laplace_no_extension phiH measurable_phiH hφ0 hS' hB' hρ
  rw [hLS]
  exact ⟨Mt, hMt.mono (hball_sub σ hσI), hkey⟩

end GoldbachBoundaries.Paper2.M3
