import GoldbachBoundaries.T0HInf.Defs

/-! The filter contributes two powers of height and a vanishing relative phase error. -/
noncomputable section
open Complex Filter Topology Set Metric
namespace GoldbachBoundaries.T0HInf
open GoldbachBoundaries
open _root_.GoldbachBoundaries.Phi2HInf
  (StirlingStrip bKerH bAmp bMain coneRotation coneMargin norm_bKer_asymp bAmp_pos
    norm_bMain bMain_cone norm_coneRotation coneMargin_pos cone_of_relative_error bAmp_ratio_le)

def filterFactor (b c τ u : ℝ) : ℂ :=
  ((b : ℂ) + ((u + τ : ℝ) : ℂ) * I - 1) * ((c : ℂ) - (u : ℂ) * I - 1)

def bKerF (b c τ u : ℝ) : ℂ := bKerH b c τ u * filterFactor b c τ u

def filteredAmp (b c τ u : ℝ) : ℝ := u ^ 2 * bAmp b c τ u

def filteredMain (b c τ u : ℝ) : ℂ := (u : ℂ) ^ 2 * bMain b c τ u

lemma filterFactor_error {b c τ u Y : ℝ} (hb : b ∈ Icc (0 : ℝ) 1)
    (hc : c ∈ Icc (0 : ℝ) 1) (hY : 0 < Y) (hτ : |τ| ≤ Y) (hu : 1 ≤ u) :
    ‖filterFactor b c τ u - (u : ℂ) ^ 2‖ ≤ (2 * (Y + 1)) * u := by
  have hu0 : 0 ≤ u := by linarith
  have hb' : |b - 1| ≤ 1 := abs_le.mpr ⟨by linarith [hb.1], by linarith [hb.2]⟩
  have hc' : |c - 1| ≤ 1 := abs_le.mpr ⟨by linarith [hc.1], by linarith [hc.2]⟩
  have hbc : |c - b| ≤ 1 := abs_le.mpr ⟨by linarith [hb.2, hc.1], by linarith [hb.1, hc.2]⟩
  have hprod : |(b - 1) * (c - 1)| ≤ 1 := by rw [abs_mul]; nlinarith [mul_le_mul hb' hc' (abs_nonneg _) zero_le_one]
  have hre : (filterFactor b c τ u - (u : ℂ) ^ 2).re = τ * u + (b - 1) * (c - 1) := by
    simp [filterFactor, pow_two]; ring
  have him : (filterFactor b c τ u - (u : ℂ) ^ 2).im = u * (c - b) + τ * (c - 1) := by
    simp [filterFactor, pow_two]; ring
  have hr : |τ * u + (b - 1) * (c - 1)| ≤ Y * u + 1 := by
    calc _ ≤ |τ * u| + |(b - 1) * (c - 1)| := abs_add_le _ _
      _ ≤ Y * u + 1 := by rw [abs_mul, abs_of_nonneg hu0]; gcongr
  have hi : |u * (c - b) + τ * (c - 1)| ≤ u + Y := by
    calc _ ≤ |u * (c - b)| + |τ * (c - 1)| := abs_add_le _ _
      _ ≤ u * 1 + Y * 1 := by rw [abs_mul, abs_mul, abs_of_nonneg hu0]; gcongr
      _ = u + Y := by ring
  calc ‖filterFactor b c τ u - (u : ℂ) ^ 2‖
      ≤ |(filterFactor b c τ u - (u : ℂ) ^ 2).re| +
        |(filterFactor b c τ u - (u : ℂ) ^ 2).im| := norm_le_abs_re_add_abs_im _
    _ ≤ Y * u + 1 + (u + Y) := by rw [hre, him]; gcongr
    _ ≤ (2 * (Y + 1)) * u := by nlinarith

lemma norm_filteredMain (b c τ u : ℝ) (hu : 0 < u) :
    ‖filteredMain b c τ u‖ = filteredAmp b c τ u := by
  rw [filteredMain, norm_mul, Complex.norm_pow, Complex.norm_real,
    Real.norm_of_nonneg hu.le, norm_bMain b c τ u hu]
  rfl

lemma filteredAmp_pos {b c τ u : ℝ} (hu : 0 < u) : 0 < filteredAmp b c τ u :=
  mul_pos (sq_pos_of_pos hu) (bAmp_pos hu)

lemma norm_bKerF_asymp (hStir : StirlingStrip) {B Y : ℝ}
    (hB : 1 / 2 ≤ B) (hB1 : B < 1) (hY : 0 < Y) :
    ∃ K U : ℝ, 0 ≤ K ∧ Y + 1 ≤ U ∧
      ∀ b ∈ Icc (1 - B) B, ∀ c ∈ Icc (1 - B) B, ∀ τ : ℝ, |τ| ≤ Y →
        ∀ u : ℝ, U ≤ u →
          ‖bKerF b c τ u - filteredMain b c τ u‖ ≤ K / u * filteredAmp b c τ u := by
  obtain ⟨K, U, hK, hU, happrox⟩ := norm_bKer_asymp hStir hB hB1 hY
  let D : ℝ := 2 * (Y + 1)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨K * (1 + D) + D, U, by positivity, hU, ?_⟩
  intro b hb c hc τ hτ u hu
  have hu1 : 1 ≤ u := by linarith [hU.trans hu]
  have hu0 : 0 < u := by linarith
  have hfactor := filterFactor_error (b := b) (c := c)
    ⟨by linarith [hb.1], by linarith [hb.2]⟩
    ⟨by linarith [hc.1], by linarith [hc.2]⟩ hY hτ hu1
  change ‖filterFactor b c τ u - (u : ℂ) ^ 2‖ ≤ D * u at hfactor
  have hnorm : ‖filterFactor b c τ u‖ ≤ (1 + D) * u ^ 2 := by
    have h := norm_le_norm_sub_add (filterFactor b c τ u) ((u : ℂ) ^ 2)
    rw [Complex.norm_pow, Complex.norm_real, Real.norm_of_nonneg hu0.le] at h
    nlinarith [mul_nonneg hD (show 0 ≤ u ^ 2 - u by nlinarith)]
  have hid : bKerF b c τ u - filteredMain b c τ u =
      (bKerH b c τ u - bMain b c τ u) * filterFactor b c τ u +
        bMain b c τ u * (filterFactor b c τ u - (u : ℂ) ^ 2) := by
    unfold bKerF filteredMain
    ring
  rw [hid]
  calc _ ≤ ‖(bKerH b c τ u - bMain b c τ u) * filterFactor b c τ u‖ +
          ‖bMain b c τ u * (filterFactor b c τ u - (u : ℂ) ^ 2)‖ := norm_add_le _ _
    _ ≤ (K / u * bAmp b c τ u) * ((1 + D) * u ^ 2) + bAmp b c τ u * (D * u) := by
      rw [norm_mul, norm_mul, norm_bMain b c τ u hu0]
      exact add_le_add (mul_le_mul (happrox b hb c hc τ hτ u hu) hnorm
        (norm_nonneg _) (mul_nonneg (div_nonneg hK hu0.le) (bAmp_pos hu0).le))
        (mul_le_mul_of_nonneg_left hfactor (bAmp_pos hu0).le)
    _ = (K * (1 + D) + D) / u * filteredAmp b c τ u := by
      unfold filteredAmp
      field_simp <;> ring

lemma filteredMain_cone {B Y : ℝ} (hB : 1 / 2 ≤ B) (hB1 : B < 1) (hY : 0 < Y) :
    ∃ U : ℝ, Y + 1 ≤ U ∧
      ∀ b ∈ Icc (1 - B) B, ∀ c ∈ Icc (1 - B) B, ∀ τ : ℝ, |τ| ≤ Y →
        ∀ u₀ u : ℝ, U ≤ u₀ → u₀ ≤ u → u ≤ u₀ + Real.sqrt u₀ →
          Real.sin (3 * (Real.pi * (1 - B)) / 4) * filteredAmp b c τ u ≤
            (coneRotation τ u₀ * filteredMain b c τ u).re := by
  obtain ⟨U, hU, hcone⟩ := bMain_cone hB hB1 hY
  refine ⟨U, hU, ?_⟩
  intro b hb c hc τ hτ u₀ u hU₀ hu hw
  have h := mul_le_mul_of_nonneg_left (hcone b hb c hc τ hτ u₀ u hU₀ hu hw) (sq_nonneg u)
  have heq : (coneRotation τ u₀ * filteredMain b c τ u).re =
      u ^ 2 * (coneRotation τ u₀ * bMain b c τ u).re := by
    rw [filteredMain, mul_left_comm]
    simp [pow_two]
  rw [heq, filteredAmp]
  nlinarith

lemma bKerF_ne_zero {b c τ u : ℝ} (hb : 0 < b) (hc : 0 < c) (hu : 0 < u)
    (hut : 0 < u + τ) : bKerF b c τ u ≠ 0 := by
  unfold bKerF bKerH filterFactor
  apply mul_ne_zero
  · exact mul_ne_zero (Gamma_ne_zero_of_re_pos (by simpa using hb))
      (Gamma_ne_zero_of_re_pos (by simpa using hc))
  · apply mul_ne_zero
    · intro h
      have := congrArg Complex.im h
      simp at this
      linarith
    · intro h
      have := congrArg Complex.im h
      simp at this
      linarith

lemma filteredAmp_ratio_le {b c b₀ c₀ τ u₀ u : ℝ} (hα : b + c = b₀ + c₀)
    (hα1 : b + c - 1 ≤ 1) (hu₀ : 1 ≤ u₀) (hu : u₀ ≤ u) :
    filteredAmp b c τ u ≤ (1 + u - u₀) ^ 3 * Real.exp (-Real.pi * (u - u₀)) *
      filteredAmp b₀ c₀ τ u₀ := by
  have hu₀0 : 0 < u₀ := by linarith
  have hu0 : 0 < u := hu₀0.trans_le hu
  have hd : 0 ≤ 1 + u - u₀ := by linarith
  have hmul : u ≤ (1 + u - u₀) * u₀ := by nlinarith [mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hu₀)]
  have hs : u ^ 2 ≤ ((1 + u - u₀) * u₀) ^ 2 := pow_le_pow_left₀ hu0.le hmul 2
  have ha := bAmp_ratio_le (τ := τ) hα hα1 hu₀ hu
  unfold filteredAmp
  calc u ^ 2 * bAmp b c τ u
      ≤ ((1 + u - u₀) * u₀) ^ 2 *
        ((1 + u - u₀) * Real.exp (-Real.pi * (u - u₀)) * bAmp b₀ c₀ τ u₀) := by
        exact mul_le_mul hs ha (bAmp_pos hu0).le (sq_nonneg _)
    _ = _ := by ring

end GoldbachBoundaries.T0HInf
