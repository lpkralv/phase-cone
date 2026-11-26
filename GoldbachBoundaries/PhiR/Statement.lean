import GoldbachBoundaries.PhiR.Defs
import GoldbachBoundaries.PhiR.Proof.M3Boundary
import GoldbachBoundaries.PhiR.Proof.M4Reduction
import GoldbachBoundaries.PhiR.Proof.M5Radial
import GoldbachBoundaries.Phi2.Statement

/-!
`phiR_natural_boundary` has the shape of `phi2_natural_boundary` with `ℍ = {σ > 1}`, `σ > 2`, `σ = 1`, `phi2Poles`,
`HasPhi2Residues` replaced by `{σ > r - 1}`, `σ > r`, `σ = r - 1`, `phiRPoles r`, `HasPhiRResidues r`, and the same four
hypotheses: RH and the classical premises (Z2), (Z3), `ZLittlewood` (`Paper2/Defs.lean`), which enter only through
`Phi2Proof.phi2_boundary`. For `r = 2` it is `phi2_natural_boundary` (`phiR_natural_boundary_two`, a real proof from
`phi2_natural_boundary` alone).
-/

noncomputable section

open Complex Filter Topology Set Metric

namespace GoldbachBoundaries

open GoldbachBoundaries.Paper2

/-! ## Sanity lemmas (real proofs) -/

/-- A tuple with some `k_i = 0` contributes `0` to `Φ_r` (`Λ(0) = 0`), so `PhiR r` is the sum over `k_i ≥ 1`. -/
theorem PhiR_term_eq_zero {r : ℕ} (k : Fin r → ℕ) (i : Fin r) (hi : k i = 0) (s : ℂ) :
    (∏ j, ((ArithmeticFunction.vonMangoldt (k j) : ℝ) : ℂ)) * (((∑ j, k j : ℕ) : ℂ)) ^ (-s) = 0 := by
  rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi]), zero_mul]

/-- **`Φ_2 = Φ₂`** at every `s` (including the junk region): reindex `Fin 2 → ℕ ≃ ℕ × ℕ`. -/
theorem PhiR_two : PhiR 2 = Phi2 := by
  funext s
  rw [PhiR, Phi2, ← (finTwoArrowEquiv ℕ).symm.tsum_eq]
  refine tsum_congr fun mn => ?_
  simp [Fin.prod_univ_two, Fin.sum_univ_two]

/-- `lineAt 1` is paper 1's `lineOne`. -/
theorem lineAt_one : lineAt 1 = lineOne := rfl

/-- `phiRPoles 2 = phi2Poles`. -/
theorem phiRPoles_two : phiRPoles 2 = phi2Poles := by
  ext s
  simp only [phiRPoles, phi2Poles, mem_union, mem_singleton_iff, Set.mem_ofPred_eq, Nat.cast_ofNat]
  norm_num

/-- `HasPhiRResidues 2 = HasPhi2Residues`: `1/1! = 1` and `-2m(ρ)Γ(ρ)/Γ(ρ+1) = -2m(ρ)/ρ`. -/
theorem hasPhiRResidues_two_iff (v : ℂ → ℂ) : HasPhiRResidues 2 v ↔ HasPhi2Residues v := by
  have key : ∀ ρ ∈ NontrivialZeros,
      -(2 * (zetaMult ρ : ℂ) * Gamma ρ) / Gamma (ρ + 1) = -(2 * (zetaMult ρ : ℂ)) / ρ := by
    intro ρ hρ
    have hρ0 : ρ ≠ 0 := by rintro rfl; simp [NontrivialZeros] at hρ
    have hΓ : Gamma ρ ≠ 0 := Gamma_ne_zero_of_re_pos hρ.2.1
    rw [Complex.Gamma_add_one ρ hρ0]
    field_simp
  simp only [HasPhiRResidues, HasPhi2Residues, Nat.cast_ofNat]
  norm_num
  intro _
  exact forall₂_congr fun ρ hρ => by rw [key ρ hρ]

/-- The pole set lies in `σ > r - 1`, unconditionally. -/
theorem phiRPoles_subset (r : ℕ) : phiRPoles r ⊆ halfPlane ((r : ℝ) - 1) :=
  PhiRProof.phiRPoles_subset_halfPlane r



theorem polyP_ne_zero {j : ℕ} {s : ℂ} (hs : (j : ℝ) < s.re) : polyP j s ≠ 0 := by
  rw [polyP, Finset.prod_ne_zero_iff]
  intro l hl h
  have := congrArg Complex.re h
  simp only [sub_re, natCast_re, zero_re] at this
  have : (l : ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.mp hl).2
  linarith

/-! ## The theorems -/

/--
Assume RH. Then `Φ_r` continues from `σ > r` to a meromorphic function on `σ > r - 1` whose poles are exactly `r` and
`r - 1 + ρ` (`ρ` a non-trivial zero), all simple, with residue `1/(r-1)!` at `r` and `-r m(ρ)Γ(ρ)/Γ(ρ + r - 1)` at
`r - 1 + ρ`; and `σ = r - 1` is a natural boundary of every meromorphic continuation of `Φ_r` to `σ > r - 1`.
-/
theorem phiR_natural_boundary (hRH : RiemannHypothesis) (hZ2 : Z2) (hZ3 : Z3) (hL : ZLittlewood) {r : ℕ}
    (hr : 2 ≤ r) :
    (∃ F : ℂ → ℂ, MeromorphicOn F (halfPlane ((r : ℝ) - 1)) ∧ EqOn F (PhiR r) (halfPlane r) ∧
      AnalyticOnNhd ℂ F (halfPlane ((r : ℝ) - 1) \ phiRPoles r) ∧
      (∀ α ∈ phiRPoles r, meromorphicOrderAt F α = -1) ∧
      ∃ res : ℂ → ℂ, (∀ α ∈ phiRPoles r, HasResidue F α (res α)) ∧ HasPhiRResidues r res ∧
        ∀ α ∈ phiRPoles r, res α ≠ 0) ∧
    (∀ F : ℂ → ℂ, MeromorphicOn F (halfPlane ((r : ℝ) - 1)) → F =ᶠ[codiscreteWithin (halfPlane r)] PhiR r →
      IsNaturalBoundary F (halfPlane ((r : ℝ) - 1)) (lineAt ((r : ℝ) - 1))) :=
  ⟨⟨PhiRProof.PhiRc r, PhiRProof.phiR_continuation hRH hr⟩,
    fun F hF hFΦ => PhiRProof.phiR_boundary hRH hZ2 hZ3 hL hr F hF hFΦ⟩

/-- **The case `r = 2` is `phi2_natural_boundary`** (real proof from `phi2_natural_boundary` alone, through
`PhiR_two`, `phiRPoles_two`, `hasPhiRResidues_two_iff`, `lineAt_one`): a check that the general statement specializes
to the signed-off `Φ₂` statement. -/
theorem phiR_natural_boundary_two (hRH : RiemannHypothesis) (hZ2 : Z2) (hZ3 : Z3) (hL : ZLittlewood) :
    (∃ F : ℂ → ℂ, MeromorphicOn F (halfPlane (((2 : ℕ) : ℝ) - 1)) ∧ EqOn F (PhiR 2) (halfPlane ((2 : ℕ) : ℝ)) ∧
      AnalyticOnNhd ℂ F (halfPlane (((2 : ℕ) : ℝ) - 1) \ phiRPoles 2) ∧
      (∀ α ∈ phiRPoles 2, meromorphicOrderAt F α = -1) ∧
      ∃ res : ℂ → ℂ, (∀ α ∈ phiRPoles 2, HasResidue F α (res α)) ∧ HasPhiRResidues 2 res ∧
        ∀ α ∈ phiRPoles 2, res α ≠ 0) ∧
    (∀ F : ℂ → ℂ, MeromorphicOn F (halfPlane (((2 : ℕ) : ℝ) - 1)) →
      F =ᶠ[codiscreteWithin (halfPlane ((2 : ℕ) : ℝ))] PhiR 2 →
      IsNaturalBoundary F (halfPlane (((2 : ℕ) : ℝ) - 1)) (lineAt (((2 : ℕ) : ℝ) - 1))) := by
  have h1 : ((2 : ℕ) : ℝ) - 1 = 1 := by norm_num
  have h2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
  rw [h1, h2, PhiR_two, phiRPoles_two, lineAt_one]
  simp only [hasPhiRResidues_two_iff]
  exact phi2_natural_boundary hRH hZ2 hZ3 hL

/-- **Corollary (classical form)**: let `F` be a meromorphic
continuation of `Φ_r` to `σ > r - 1` (meromorphic there and equal to `Φ_r` on `σ > r`). Then for every point
`r - 1 + iτ` of the line and every `ε > 0`, no function meromorphic on the disc `|s - (r - 1 + iτ)| < ε` coincides
with `F` at every point of the disc with `σ > r - 1`. -/
theorem phiR_natural_boundary_classical (hRH : RiemannHypothesis) (hZ2 : Z2) (hZ3 : Z3) (hL : ZLittlewood)
    {r : ℕ} (hr : 2 ≤ r) (F : ℂ → ℂ) (hF : MeromorphicOn F (halfPlane ((r : ℝ) - 1)))
    (hFΦ : EqOn F (PhiR r) (halfPlane r)) (τ ε : ℝ) (hε : 0 < ε) :
    ¬ ∃ g : ℂ → ℂ, MeromorphicOn g (ball ((r : ℂ) - 1 + τ * I) ε) ∧
      EqOn g F (ball ((r : ℂ) - 1 + τ * I) ε ∩ halfPlane ((r : ℝ) - 1)) := by
  rintro ⟨g, hg, hgF⟩
  have hcod : F =ᶠ[codiscreteWithin (halfPlane r)] PhiR r := by
    filter_upwards [self_mem_codiscreteWithin (halfPlane r)] with s hs using hFΦ hs
  have hline : ((r : ℂ) - 1 + τ * I) ∈ lineAt ((r : ℝ) - 1) := by
    show ((r : ℂ) - 1 + τ * I).re = (r : ℝ) - 1
    simp
  refine (phiR_natural_boundary hRH hZ2 hZ3 hL hr).2 F hF hcod _ hline ε hε ⟨g, hg, ?_⟩
  filter_upwards [self_mem_codiscreteWithin (ball ((r : ℂ) - 1 + τ * I) ε ∩ halfPlane ((r : ℝ) - 1))]
    with s hs using hgF hs



theorem phiR_singular_iff (hRH : RiemannHypothesis) {r : ℕ} (hr : 2 ≤ r) (F : ℂ → ℂ)
    (hF : MeromorphicOn F (halfPlane ((r : ℝ) - 1))) (hFΦ : F =ᶠ[codiscreteWithin (halfPlane r)] PhiR r)
    (τ : ℝ) :
    NoMeromorphicExtensionAt F (halfPlane ((r : ℝ) - 1)) ((r : ℂ) - 1 + τ * I) ↔
      NoMeromorphicExtensionAt Phi2Proof.Phi2c HH (1 + τ * I) := by
  rw [PhiRProof.noMeromorphicExtensionAt_PhiR_iff hRH hr F hF hFΦ (by simp),
    show (r : ℂ) - 1 + τ * I - (((r : ℝ) - 2 : ℝ) : ℂ) = 1 + τ * I by push_cast; ring]



theorem phiR_reduction (hRH : RiemannHypothesis) {r : ℕ} (hr : 3 ≤ r) :
    ∃ R : ℂ → ℂ, DifferentiableOn ℂ R (halfPlane ((r : ℝ) - 3 / 2)) ∧
      (∀ a : ℝ, (r : ℝ) - 3 / 2 < a → ∀ T : ℝ, ∃ M : ℝ,
        ∀ s : ℂ, a ≤ s.re → T ≤ s.im → s.im ≤ T + 1 → ‖R s‖ ≤ M) ∧
      ∀ s : ℂ, (r : ℝ) < s.re →
        PhiR r s = ((r : ℂ) - 1) * ((r : ℂ) - 2) / 2 / ((r - 1).factorial : ℂ) * riemannZeta (s - r + 1) +
          (r : ℂ) * ((r : ℂ) - 2) / polyP (r - 1) s *
            (deriv riemannZeta (s - r + 1) / riemannZeta (s - r + 1)) +
          ((r.choose 2 : ℕ) : ℂ) / polyP (r - 2) s * Phi2 (s - r + 2) + R s := by
  have hr2 : 2 ≤ r := by omega
  obtain ⟨R, hR, hRR⟩ := PhiRProof.exists_RR hRH hr2
  refine ⟨R, hR, fun a ha T => PhiRProof.RR_bounded_halfStrip hr2 hR hRR ha T, fun s hs => ?_⟩
  have hsH : s ∈ halfPlane ((r : ℝ) - 3 / 2) := by show _ < s.re; linarith
  have hsr : s ≠ (r : ℂ) := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  rw [hRR s hsH hsr]
  exact PhiRProof.PhiR_eq_explicit hr2 hs



theorem phiR_radial_limit (hRH : RiemannHypothesis) (hZ2 : Z2) (hZ3 : Z3) {r : ℕ} (hr : 2 ≤ r) {τ : ℝ}
    (hτ : τ ≠ 0) :
    Tendsto (fun η : ℝ => (η : ℂ) * PhiRProof.PhiRc r ((r : ℂ) - 1 + τ * I + η)) (𝓝[>] 0)
      (𝓝 (((r.choose 2 : ℕ) : ℂ) * Phi2Proof.pairAtom τ / Gamma ((r : ℂ) - 1 + τ * I))) := by
  have h := PhiRProof.tendsto_eta_PhiRc hRH hZ2 hZ3 hr hτ
  have hc : ((PhiRProof.cC r : ℝ) : ℂ) = ((r.choose 2 : ℕ) : ℂ) := by
    rw [Nat.cast_choose_two, PhiRProof.cC]
    push_cast
    ring
  rwa [hc] at h

end GoldbachBoundaries
