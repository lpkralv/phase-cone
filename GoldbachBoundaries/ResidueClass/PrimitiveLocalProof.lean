import GoldbachBoundaries.ResidueClass.ExceptionalZeros
import GoldbachBoundaries.ResidueClass.PrimitiveReflection
import GoldbachBoundaries.ResidueClass.ZeroWindows
import PrimeNumberTheoremAnd.StrongPNT

/-! # The unit-window expansion for primitive Dirichlet L-functions with eventually critical zeros -/

noncomputable section

open Complex Filter Metric Set
open scoped Topology

namespace GoldbachBoundaries.ResidueClass

variable {m : ℕ} [NeZero m] (ψ : DirichletCharacter ℂ m)

private def stripZeros : Set ℂ := {ρ | ψ.LFunction ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1}

private def lWindow (z : ℂ) : Set ℂ := {ρ ∈ stripZeros ψ | |ρ.im - z.im| ≤ 1}

private def lWindowSum (z : ℂ) : ℂ :=
  ∑ᶠ ρ ∈ lWindow ψ z, (analyticOrderNatAt ψ.LFunction ρ : ℂ) / (z - ρ)

private theorem finite_zeros_on_compact {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {c : ℂ} (hc : f c ≠ 0) {K : Set ℂ} (hK : IsCompact K) : (K ∩ f ⁻¹' {0}).Finite := by
  have ha : AnalyticOnNhd ℂ f univ := fun w _ ↦ hf.analyticAt w
  have hdisc := ha.preimage_zero_mem_codiscrete hc
  rw [Set.preimage_compl] at hdisc
  have hh := compl_mem_codiscrete_iff.mp hdisc
  exact (hK.inter_right hh.1).finite (hh.2.mono inter_subset_right)

private theorem finite_lWindow (hn : ψ ≠ 1) (z : ℂ) : (lWindow ψ z).Finite := by
  let K := (equivRealProdCLM : ℂ → ℝ × ℝ) ⁻¹' (Icc 0 1 ×ˢ Icc (z.im - 1) (z.im + 1))
  have hK : IsCompact K :=
    equivRealProdCLM.toHomeomorph.isCompact_preimage.mpr (isCompact_Icc.prod isCompact_Icc)
  refine (finite_zeros_on_compact (DirichletCharacter.differentiable_LFunction hn)
    (ψ.LFunction_ne_zero_of_one_le_re (s := 2) (.inl hn) (by norm_num)) hK).subset ?_
  intro ρ hρ
  obtain ⟨hl, hu⟩ := abs_le.mp hρ.2
  refine ⟨⟨⟨hρ.1.2.1.le, hρ.1.2.2.le⟩, ?_⟩, hρ.1.1⟩
  change z.im - 1 ≤ ρ.im ∧ ρ.im ≤ z.im + 1
  exact ⟨by linarith, by linarith⟩

private theorem window_ne_real {z ρ : ℂ} (hz : 2 ≤ |z.im|) (hρ : ρ ∈ lWindow ψ z) :
    ρ.im ≠ 0 := by
  intro h
  have := hρ.2
  rw [h, zero_sub, abs_neg] at this
  linarith

private theorem exists_right_local_bound (hn : ψ ≠ 1)
    {T : ℝ} (hline : ∀ ρ ∈ stripZeros ψ, T ≤ |ρ.im| → ρ.re = 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, 1 / 2 ≤ z.re → z.re ≤ 2 → max 2 (T + 1) ≤ |z.im| →
      ψ.LFunction z ≠ 0 →
      ‖logDeriv ψ.LFunction z - lWindowSum ψ z‖ ≤ C * Real.log (2 + |z.im|) := by
  classical
  let K : ℝ := 32 * (m : ℝ) * max 1 ‖riemannZeta 2‖
  let D : ℝ := (16 * (15 / 16)^2 / (15 / 16 - 4 / 5)^3 +
      1 / (((31 / 32)^2 / (19 / 20) - 19 / 20) * Real.log ((31 / 32) / (19 / 20)))) / 2 +
    1 / Real.log ((31 / 32) / (15 / 16))
  have hD : 0 ≤ D := by
    dsimp [D]
    have h₁ : 0 < Real.log ((31 / 32) / (19 / 20)) := Real.log_pos (by norm_num)
    have h₂ : 0 < Real.log ((31 / 32) / (15 / 16)) := Real.log_pos (by norm_num)
    positivity
  have hK : 1 ≤ K := by
    have hm : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)
    calc
      _ ≤ 32 * (1 : ℝ) * 1 := by norm_num
      _ ≤ K := by dsimp [K]; gcongr; exact le_max_left _ _
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlogK := Real.log_nonneg hK
  refine ⟨D * (1 + Real.log K / Real.log 4), by positivity, fun z hz₀ hz₂ hzim hLz ↦ ?_⟩
  -- Scale by two to use the PNT+ estimates on the unit disk.
  let c : ℂ := 2 + (z.im : ℂ) * I
  let a : ℂ → ℂ := fun w ↦ c + 2 * w
  let b : ℂ → ℂ := fun s ↦ (s - c) / 2
  let u : ℂ := b z
  let f : ℂ → ℂ := fun w ↦ ψ.LFunction (a w) / ψ.LFunction c
  let B : ℝ := K * (2 + |z.im|)
  have hre : c.re = 2 := by simp [c]
  have him : c.im = z.im := by simp [c]
  have hab (s : ℂ) : a (b s) = s := by dsimp [a, b]; ring
  have hba (w : ℂ) : b (a w) = w := by dsimp [a, b]; ring
  have ha : Function.Injective a := fun x y h ↦ by simpa only [hba] using congrArg b h
  have hL : Differentiable ℂ ψ.LFunction := DirichletCharacter.differentiable_LFunction hn
  have hc : ψ.LFunction c ≠ 0 :=
    ψ.LFunction_ne_zero_of_one_le_re (.inl hn) (by rw [hre]; norm_num)
  have hf : Differentiable ℂ f := (hL.comp (by dsimp [a]; fun_prop)).div_const _
  have hf0 : f 0 = 1 := by simp [f, a, hc]
  have hfu : f u ≠ 0 := by simpa [f, u, hab, hc] using hLz
  have hzero (w : ℂ) : f w = 0 ↔ ψ.LFunction (a w) = 0 := by simp [f, hc]
  have hfA : AnalyticOnNhd ℂ f univ := fun w _ ↦ hf.analyticAt w
  have hfinite : (SetOfZeros 1 f).Finite := by
    have hset : SetOfZeros 1 f = closedBall 0 1 ∩ f ⁻¹' {0} := by
      ext w
      simp [SetOfZeros, mem_closedBall, dist_zero_right]
    rw [hset]
    exact finite_zeros_on_compact hf (c := 0) (by simp [hf0]) (isCompact_closedBall _ _)
  have huim : u.im = 0 := by simp [u, b, div_ofNat_im, him]
  have hure : u.re = (z.re - 2) / 2 := by simp [u, b, div_ofNat_re, hre]
  have hu : u ∈ closedBall (0 : ℂ) (4 / 5) := by
    rw [mem_closedBall, dist_zero_right]
    refine (norm_le_abs_re_add_abs_im u).trans ?_
    rw [huim, abs_zero, add_zero, hure, abs_of_nonpos (by linarith)]
    linarith
  have hB : 1 < B := by
    dsimp [B]
    nlinarith [abs_nonneg z.im, mul_nonneg (sub_nonneg.mpr hK) (abs_nonneg z.im)]
  have hbound (w : ℂ) (hw : ‖w‖ ≤ 31 / 32) : ‖f w‖ ≤ B := by
    have hnorm : ‖2 * w‖ ≤ 31 / 16 := by rw [norm_mul, norm_ofNat]; linarith
    have hR : 1 / 16 ≤ (a w).re := by
      change 1 / 16 ≤ (c + 2 * w).re
      rw [add_re, hre]
      linarith [(abs_le.mp ((abs_re_le_norm (2 * w)).trans hnorm)).1]
    have hpos : 0 < (a w).re := by linarith
    have hn' : ‖a w‖ ≤ |z.im| + 4 := by
      have hc' : ‖c‖ ≤ 2 + |z.im| := by
        simpa [c, norm_mul, Real.norm_eq_abs] using norm_add_le (2 : ℂ) ((z.im : ℂ) * I)
      exact (norm_add_le _ _).trans (by linarith)
    have hne : 0 < ‖riemannZeta 2‖ := norm_pos_iff.mpr
      (riemannZeta_ne_zero_of_one_le_re (by norm_num))
    simp only [f, norm_div]
    calc
      _ ≤ ‖ψ.LFunction (a w)‖ / ‖riemannZeta 2‖⁻¹ :=
        div_le_div_of_nonneg_left (norm_nonneg _) (inv_pos.mpr hne)
          (inv_norm_zeta_two_le_norm_lFunction (ψ := ψ) hre)
      _ = ‖ψ.LFunction (a w)‖ * ‖riemannZeta 2‖ := by rw [div_inv_eq_mul]
      _ ≤ (m : ℝ) * (|z.im| + 4) / (1 / 16) * ‖riemannZeta 2‖ := by
        exact mul_le_mul_of_nonneg_right ((norm_lFunction_le hn hpos).trans
          (div_le_div₀ (by positivity) (by gcongr) (by norm_num) hR)) (norm_nonneg _)
      _ ≤ B := by
        dsimp [B, K]
        calc
          _ = (16 * (m : ℝ) * (|z.im| + 4)) * ‖riemannZeta 2‖ := by ring
          _ ≤ (16 * (m : ℝ) * (2 * (2 + |z.im|))) * max 1 ‖riemannZeta 2‖ := by
            gcongr
            · linarith [abs_nonneg z.im]
            · exact le_max_right _ _
          _ = _ := by ring
  have hfClosed : AnalyticOnNhd ℂ f (closedBall 0 1) := hfA.mono (subset_univ _)
  let F : Finset ℂ := (finiteSetOfZeros_mono (show (15 / 16 : ℝ) < 1 by norm_num) hfinite).toFinset
  have hF (w : ℂ) : w ∈ F ↔ ‖w‖ ≤ 15 / 16 ∧ f w = 0 := by
    simp only [F, Finite.mem_toFinset, SetOfZeros, mem_ofPred_eq]
  have hlocal := FinalBound (r' := 4 / 5) (r := 15 / 16) (R' := 19 / 20) (R := 31 / 32)
    hB (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hfClosed hf0 hfinite hbound (show u ∈ closedBall 0 (4 / 5) \ SetOfZeros (19 / 20) f from
      ⟨hu, fun hh ↦ hfu hh.2⟩)
  have hmass := ZerosBound (r := 15 / 16) (R := 31 / 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hfClosed hf0 hfinite hbound
  rw [Nat.cast_sum] at hmass
  change (∑ w ∈ F, (analyticOrderNatAt f w : ℝ)) ≤ _ at hmass
  -- The height window is a subset of the disk zeros because its zeros lie on the critical line.
  let W := F.filter fun w ↦ |(a w).im - z.im| ≤ 1
  have hW (w : ℂ) : w ∈ W ↔ w ∈ F ∧ |(a w).im - z.im| ≤ 1 := Finset.mem_filter
  have hwim (w : ℂ) : (a w).im - z.im = 2 * w.im := by simp [a, mul_im, him]
  have hmapped : Set.BijOn a (↑W : Set ℂ) (lWindow ψ z) := by
    refine ⟨?_, ha.injOn, ?_⟩
    · intro w hw
      obtain ⟨hwF, hwim'⟩ := (hW w).mp hw
      obtain ⟨hwn, hwz⟩ := (hF w).mp hwF
      have hnorm : ‖2 * w‖ ≤ 15 / 8 := by rw [norm_mul, norm_ofNat]; linarith
      have hp : 0 < (a w).re := by
        change 0 < (c + 2 * w).re
        rw [add_re, hre]
        linarith [(abs_le.mp ((abs_re_le_norm (2 * w)).trans hnorm)).1]
      have hzero' := (hzero w).mp hwz
      have hlt : (a w).re < 1 := lt_of_not_ge fun h ↦
        ψ.LFunction_ne_zero_of_one_le_re (.inl hn) h hzero'
      exact ⟨⟨hzero', hp, hlt⟩, hwim'⟩
    · intro ρ hρ
      have hline' := hline ρ hρ.1 (by
        have hzT := (le_max_right (2 : ℝ) (T + 1)).trans hzim
        linarith [abs_sub_abs_le_abs_sub z.im ρ.im, abs_sub_comm z.im ρ.im, hρ.2])
      have hnr : ‖b ρ‖ ≤ 15 / 16 := by
        rw [Complex.norm_def, Real.sqrt_le_iff]
        refine ⟨by norm_num, ?_⟩
        rw [normSq_apply]
        have hbr : (b ρ).re = -(3 / 4 : ℝ) := by norm_num [b, div_ofNat_re, hline', hre]
        have hbi : (b ρ).im = (ρ.im - z.im) / 2 := by simp [b, div_ofNat_im, him]
        rw [hbr, hbi]
        obtain ⟨hl, hh⟩ := abs_le.mp hρ.2
        nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - (ρ.im - z.im))
          (by linarith : 0 ≤ 1 + (ρ.im - z.im))]
      exact ⟨b ρ, (hW _).mpr ⟨(hF _).mpr ⟨hnr, (hzero _).mpr (by rw [hab]; exact hρ.1.1)⟩,
        by rw [hab]; exact hρ.2⟩, hab ρ⟩
  have haDeriv (w : ℂ) : HasDerivAt a 2 w := by
    simpa [a] using ((hasDerivAt_id' w).const_mul (2 : ℂ)).const_add c
  have horder (w : ℂ) : analyticOrderNatAt f w = analyticOrderNatAt ψ.LFunction (a w) := by
    have haA : AnalyticAt ℂ a w := by dsimp [a]; fun_prop
    have hfA' := (hL.analyticAt (a w)).comp haA
    unfold analyticOrderNatAt
    congr 1
    change analyticOrderAt ((ψ.LFunction ∘ a) * fun _ ↦ (ψ.LFunction c)⁻¹) w = _
    rw [analyticOrderAt_mul hfA' analyticAt_const,
      (analyticAt_const (v := (ψ.LFunction c)⁻¹)).analyticOrderAt_eq_zero.mpr (inv_ne_zero hc),
      add_zero, analyticOrderAt_comp_of_deriv_ne_zero haA (by rw [(haDeriv w).deriv]; norm_num)]
  let term : ℂ → ℂ := fun w ↦ (analyticOrderNatAt f w : ℂ) / (u - w)
  have hsum : ∑ w ∈ W, term w = 2 * lWindowSum ψ z := by
    have hWfin : (↑W : Set ℂ).Finite := W.finite_toSet
    have hfin : (lWindow ψ z).Finite := hmapped.image_eq ▸ hWfin.image a
    calc
      _ = ∑ᶠ w ∈ (↑W : Set ℂ), term w := by
        simpa only [Finset.finite_toSet_toFinset] using
          (finsum_mem_eq_finite_toFinset_sum term hWfin).symm
      _ = ∑ᶠ ρ ∈ lWindow ψ z, 2 * ((analyticOrderNatAt ψ.LFunction ρ : ℂ) / (z - ρ)) := by
        refine finsum_mem_eq_of_bijOn a hmapped fun w _ ↦ ?_
        simp only [term, horder]
        have he : z - a w = 2 * (u - w) := by dsimp [a, u, b]; ring
        rw [he, ← mul_div_assoc, mul_div_mul_left _ _ (two_ne_zero : (2 : ℂ) ≠ 0)]
      _ = _ := by
        simp only [lWindowSum, finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.mul_sum]
  -- The discarded fractions have bounded reciprocal denominators.
  have hdiff : ‖∑ w ∈ F \ W, term w‖ ≤ 2 * ∑ w ∈ F, (analyticOrderNatAt f w : ℝ) := by
    calc
      _ ≤ ∑ w ∈ F \ W, ‖term w‖ := norm_sum_le _ _
      _ ≤ ∑ w ∈ F \ W, 2 * (analyticOrderNatAt f w : ℝ) := by
        apply Finset.sum_le_sum
        intro w hw
        obtain ⟨hwF, hwW⟩ := Finset.mem_sdiff.mp hw
        have hwim' : 1 < |(a w).im - z.im| := lt_of_not_ge (fun h ↦ hwW ((hW _).mpr ⟨hwF, h⟩))
        rw [hwim, abs_mul, abs_of_pos two_pos] at hwim'
        have hd := abs_im_le_norm (u - w)
        rw [sub_im, huim, zero_sub, abs_neg] at hd
        have hd' : 1 / 2 ≤ ‖u - w‖ := by linarith
        simp only [term, norm_div, Complex.norm_natCast]
        calc
          _ ≤ (analyticOrderNatAt f w : ℝ) / (1 / 2) :=
            div_le_div_of_nonneg_left (by positivity) (by norm_num) hd'
          _ = _ := by ring
      _ ≤ _ := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (by intros; positivity)
  have hlogDeriv : logDeriv f u = 2 * logDeriv ψ.LFunction z := by
    change logDeriv (fun w ↦ (ψ.LFunction ∘ a) w / ψ.LFunction c) u = _
    simp only [div_eq_mul_inv]
    rw [logDeriv_mul_const _ _ (inv_ne_zero hc), logDeriv_comp (hL.differentiableAt)
      (haDeriv u).differentiableAt, (haDeriv u).deriv, show a u = z from hab z, mul_comm]
  change ‖logDeriv f u - ∑ w ∈ F, term w‖ ≤ _ at hlocal
  have hsplit : ∑ w ∈ F \ W, term w + ∑ w ∈ W, term w = ∑ w ∈ F, term w :=
    Finset.sum_sdiff (Finset.filter_subset _ _)
  have htotal : ‖logDeriv ψ.LFunction z - lWindowSum ψ z‖ ≤ D * Real.log B := by
    have he : 2 * (logDeriv ψ.LFunction z - lWindowSum ψ z) =
        (logDeriv f u - ∑ w ∈ F, term w) + ∑ w ∈ F \ W, term w := by
      rw [← hsplit, hlogDeriv, hsum]
      ring
    have hn' := norm_add_le (logDeriv f u - ∑ w ∈ F, term w) (∑ w ∈ F \ W, term w)
    rw [← he, norm_mul, norm_ofNat] at hn'
    dsimp [D]
    linarith [mul_le_mul_of_nonneg_left hmass (show (0 : ℝ) ≤ 2 by norm_num)]
  refine htotal.trans ?_
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hD
  have hz₂' : 2 ≤ |z.im| := (le_max_left _ _).trans hzim
  have hx : Real.log 4 ≤ Real.log (2 + |z.im|) := Real.log_le_log (by norm_num) (by linarith)
  have hk : Real.log K ≤ Real.log K / Real.log 4 * Real.log (2 + |z.im|) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog4]
    exact mul_le_mul_of_nonneg_left hx (Real.log_nonneg hK)
  dsimp only [B]
  rw [Real.log_mul (ne_of_gt (zero_lt_one.trans_le hK)) (by positivity)]
  linarith

private theorem windowSum_reflection (hψ : ψ.IsPrimitive) (hn : ψ ≠ 1)
    {z : ℂ} (hz : 2 ≤ |z.im|) :
    lWindowSum ψ z = -lWindowSum ψ⁻¹ (1 - z) := by
  let flip : ℂ → ℂ := fun w ↦ 1 - w
  have hinv : Function.Involutive flip := fun w ↦ by dsimp [flip]; ring
  have him (w : ℂ) : (flip w).im = -w.im := by simp [flip]
  have hre (w : ℂ) : (flip w).re = 1 - w.re := by simp [flip]
  have habs (ρ : ℂ) : |(flip ρ).im - (flip z).im| = |ρ.im - z.im| := by
    rw [him, him, show -ρ.im - -z.im = -(ρ.im - z.im) by ring, abs_neg]
  have hmem (ρ : ℂ) (hρ : ρ.im ≠ 0) : ρ ∈ lWindow ψ z ↔ flip ρ ∈ lWindow ψ⁻¹ (flip z) := by
    change (ψ.LFunction ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1) ∧ |ρ.im - z.im| ≤ 1 ↔
      ((ψ⁻¹).LFunction (flip ρ) = 0 ∧ 0 < (flip ρ).re ∧ (flip ρ).re < 1) ∧
        |(flip ρ).im - (flip z).im| ≤ 1
    rw [habs, hre, lFunction_reflection_zero_iff ψ hψ hρ]
    constructor <;> rintro ⟨⟨h₀, h₁, h₂⟩, h₃⟩ <;> exact ⟨⟨h₀, by linarith, by linarith⟩, h₃⟩
  have hbij : Set.BijOn flip (lWindow ψ z) (lWindow ψ⁻¹ (flip z)) := by
    refine ⟨fun ρ hρ ↦ (hmem ρ (window_ne_real ψ hz hρ)).mp hρ, hinv.injective.injOn, ?_⟩
    intro ρ hρ
    have hz' : 2 ≤ |(flip z).im| := by simpa [him] using hz
    have hr := window_ne_real ψ⁻¹ hz' hρ
    refine ⟨flip ρ, (hmem _ (by simpa [him] using hr)).mpr ?_, hinv ρ⟩
    rwa [hinv]
  unfold lWindowSum
  have hn' : ψ⁻¹ ≠ 1 := by simpa using hn
  rw [← finsum_mem_neg_distrib _ (finite_lWindow ψ⁻¹ hn' (1 - z))]
  refine finsum_mem_eq_of_bijOn flip hbij fun ρ hρ ↦ ?_
  rw [lFunction_reflection_order ψ hψ hn (window_ne_real ψ hz hρ)]
  rw [show flip z - flip ρ = -(z - ρ) by dsimp [flip]; ring, div_neg, neg_neg]

private theorem exists_lFunction_local_bound (hψ : ψ.IsPrimitive) (hn : ψ ≠ 1)
    {T : ℝ} (hT : 0 < T) (hline : ∀ ρ ∈ stripZeros ψ, T ≤ |ρ.im| → ρ.re = 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, 0 < z.re → z.re ≤ 2 → max 2 (T + 1) ≤ |z.im| → ψ.LFunction z ≠ 0 →
      ‖logDeriv ψ.LFunction z - lWindowSum ψ z‖ ≤ C * Real.log (2 + |z.im|) := by
  have hn' : ψ⁻¹ ≠ 1 := by simpa using hn
  have hline' (ρ : ℂ) (hρ : ρ ∈ stripZeros ψ⁻¹) (hρT : T ≤ |ρ.im|) : ρ.re = 1 / 2 := by
    have him : ρ.im ≠ 0 := by
      intro he
      simp only [he, abs_zero] at hρT
      linarith
    have hR : (1 - ρ).im ≠ 0 := by simpa using him
    have hz := (lFunction_reflection_zero_iff ψ hψ hR).mpr (by
      rw [show (1 : ℂ) - (1 - ρ) = ρ by ring]
      exact hρ.1)
    have h₀ := hρ.2.1
    have h₁ := hρ.2.2
    have hs : (1 - ρ).re = 1 / 2 := hline _ ⟨hz, by simp; linarith, by simp; linarith⟩ (by simpa using hρT)
    simp only [sub_re, one_re] at hs
    linarith
  obtain ⟨R, hR, hright⟩ := exists_right_local_bound ψ hn hline
  obtain ⟨S, hS, hright'⟩ := exists_right_local_bound ψ⁻¹ hn' hline'
  obtain ⟨A, hA, hflip⟩ := exists_lFunction_reflection_logDeriv_bound ψ hψ hn
  refine ⟨max R (A + S), hR.trans (le_max_left _ _), fun z hz₀ hz₂ hz hnz ↦ ?_⟩
  have hlog : 0 ≤ Real.log (2 + |z.im|) := Real.log_nonneg (by linarith [abs_nonneg z.im])
  by_cases h : 1 / 2 ≤ z.re
  · exact (hright z h hz₂ hz hnz).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hlog)
  have hz₂' : 2 ≤ |z.im| := (le_max_left _ _).trans hz
  have him : z.im ≠ 0 := by intro hi; norm_num [hi] at hz₂'
  have hflim : |(1 - z).im| = |z.im| := by simp
  have hnz' := fun he ↦ hnz ((lFunction_reflection_zero_iff ψ hψ him).mpr he)
  have hr := hright' (1 - z) (by simp; linarith) (by simp; linarith) (by rwa [hflim]) hnz'
  rw [hflim] at hr
  let L := logDeriv ψ.LFunction z
  let L' := logDeriv (ψ⁻¹).LFunction (1 - z)
  let W' := lWindowSum ψ⁻¹ (1 - z)
  rw [windowSum_reflection ψ hψ hn hz₂']
  change ‖L - (-W')‖ ≤ _
  have he : L - (-W') = (L + L') - (L' - W') := by ring
  rw [he]
  calc
    _ ≤ ‖L + L'‖ + ‖L' - W'‖ := norm_sub_le _ _
    _ ≤ A * Real.log (2 + |z.im|) + S * Real.log (2 + |z.im|) :=
      add_le_add (hflip z hz₀ (by linarith) hz₂' hnz) hr
    _ ≤ _ := by rw [← add_mul]; exact mul_le_mul_of_nonneg_right (le_max_right _ _) hlog

private theorem logDerivPrimitiveLocal_of_high_critical {q : ℕ} [NeZero q] {T : ℝ}
    (hT : 0 < T)
    (hline : ∀ (χ : DirichletCharacter ℂ q) ρ, ρ ∈ primitiveZeros χ →
      T ≤ |ρ.im| → ρ.re = 1 / 2) : LogDerivPrimitiveLocal q := by
  classical
  have hχbound (χ : DirichletCharacter ℂ q) :
      ∃ C : ℝ, 0 ≤ C ∧ (χ ≠ 1 →
        ∀ z : ℂ, 0 < z.re → z.re ≤ 2 → max 2 (T + 1) ≤ |z.im| → primitiveL χ z ≠ 0 →
          ‖logDeriv (primitiveL χ) z -
            ∑ᶠ ρ ∈ {ρ ∈ primitiveZeros χ | |ρ.im - z.im| ≤ 1},
              (primitiveMult χ ρ : ℂ) / (z - ρ)‖ ≤ C * Real.log (2 + |z.im|)) := by
    by_cases hχ : χ = 1
    · exact ⟨0, le_rfl, fun h ↦ (h hχ).elim⟩
    · let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
      obtain ⟨C, hC, hbound⟩ := exists_lFunction_local_bound χ.primitiveCharacter
        χ.primitiveCharacter_isPrimitive (primitiveCharacter_ne_one χ hχ) hT
        (fun ρ hρ h ↦ hline χ ρ hρ h)
      exact ⟨C, hC, fun _ ↦ hbound⟩
  choose C hC hbound using hχbound
  refine ⟨∑ χ, C χ, max 2 (T + 1), Finset.sum_nonneg (fun χ _ ↦ hC χ), le_max_left _ _, ?_⟩
  intro χ hχ z hz₀ hz₂ hz hnz
  rw [← logDeriv_apply]
  exact (hbound χ hχ z hz₀ hz₂ hz hnz).trans
    (mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun ξ _ ↦ hC ξ) (Finset.mem_univ χ))
      (Real.log_nonneg (by linarith [le_abs_self z.im, abs_nonneg z.im])))

/-- The primitive local logarithmic derivative expansion at a fixed modulus under GRH. -/
theorem logDerivPrimitiveLocal_of_GRH {q : ℕ} [NeZero q] (hGRH : GRH q) :
    LogDerivPrimitiveLocal q :=
  logDerivPrimitiveLocal_of_high_critical (T := 1) (by norm_num) (fun χ ρ hρ _ ↦ hGRH χ ρ hρ)

/-- A large-height threshold excludes the finitely many off-line zeros from
every radius-one window in the local primitive expansion. -/
theorem logDerivPrimitiveLocal_of_finite_exceptions {q : ℕ} [NeZero q]
    (hE : (OffLineZeros q).Finite) : LogDerivPrimitiveLocal q := by
  obtain ⟨T, hT, hline⟩ := exists_high_critical hE
  exact logDerivPrimitiveLocal_of_high_critical (T := T + 1) (by linarith)
    (fun χ ρ hρ h ↦ hline χ ρ hρ (by linarith))

end GoldbachBoundaries.ResidueClass
