import GoldbachBoundaries.Paper2.M6.Sheet
import GoldbachBoundaries.Paper2.M6.Fill.Jseg_idL_kerG_eq_J
import GoldbachBoundaries.Paper2.M6.Fill.J_swap_one
import GoldbachBoundaries.Paper2.M6.Fill.Xcoef_idL_kerG_eq_X
import GoldbachBoundaries.Paper2.M6.Fill.hasCatalogueValues_congr
import GoldbachBoundaries.Paper2.M6.Fill.isAdmissibleGermOn_eventually
import GoldbachBoundaries.Paper2.M6.Fill.local_form_slitDiscL_of_slitDisc

/-!
# M6: Theorem D for the Goldbach series (`cl:ex:G`, conclusions)

Paper 2's Theorem D for `G` is paper 1's Theorem A, so `ex_G` is proved from paper 1's `ThmA` library, not through
`thm_class_i`/`thm_class_ii` (M7). Three translations:

1. **Regions and germs.** Under RH, `catalogueL idL = catalogue` (M4a's `prop_catalogue_i_proof`, paper 1's
   `catalogue_subset_HH`), `idL.HL = ℍ`, `idL.RL = {σ > 2}` (M4b), so `IsAdmissibleGermOn G (ℍ_L ∖ 𝒞_L) R_L` is paper 1's
   `IsAdmissibleGerm` (`admG_iff`, definitional after the rewrites).
2. **The coefficient.** Paper 2's `Xcoef idL kerG α = c₁c_b(J_{1b} + J_{b1})` (`b = α - 1 ≠ 1`) equals paper 1's
   `ThmA.X α = 2 Res_b(Qcont) J_{1b}`: `J_{b1} = J_{1b}` by `t ↦ 1 - t` and `K_s(s - w) = K_s(w)` (M1's `KerS_sub_symm`),
   `c₁ = -1`, `c_b = -R_b`, and `R_b = Res_b(Qcont)` (M1's `hasResidue_Qcont_Rcoef`); at `α = 2` both are `J_{11}`. This
   holds as an identity of functions (`Xcoef_idL_kerG_eq_X`), so the catalogue values of `X'_α(α)` are paper 1's
   `ThmA.X_deriv_spec`.
3. **The slit.** Paper 1's local model lives on the disc minus the *slanted* cut `α - [0, Re α - 1)(1 + iκ)` with the
   branch `Log((s - α)/(1 + iκ))`; paper 2's on the disc minus the *leftward* radius with the principal `Log(s - α)`.
   On the part of the disc off both cuts the two logarithms differ by a locally constant function, which moves into the
   holomorphic part as a constant multiple of `X_α`; at a point of the slanted cut the germ is first continued to a
   nearby point off it (inside a small disc where it is analytic and every germ is admissible), and the identity
   theorem carries the formula back (`local_form_slitDiscL_of_slitDisc`, a general lemma).

The natural boundary is paper 1's `ThmA.thm_G_boundary_proof` after translation 1. Only RH is used; (Z1), (Z2), (Z3),
(Z6) (which the statement carries because the paper's route goes through `cl:thm:class`) are not.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M6

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-! ## Real proofs: regions and germs -/

/-- Under RH the catalogue of `L(s) = s` is paper 1's catalogue. -/
theorem catalogueL_idL (hRH : RiemannHypothesis) : catalogueL Aff.idL = catalogue := by
  rw [(M4a.prop_catalogue_i_proof hRH Aff.idL).1]
  ext s
  simp only [Set.mem_ofPred_eq, M4a.app_idL, M4b.idL_HL_eq]
  exact ⟨fun h => h.2, fun h => ⟨catalogue_subset_HH h, h⟩⟩

/-- Under RH, admissible germs of `G` in paper 2's sense (for `L(s) = s`) are paper 1's admissible germs. -/
theorem admG_iff (hRH : RiemannHypothesis) {g : ℂ → ℂ} {s : ℂ} :
    IsAdmissibleGermOn G (Aff.idL.HL \ catalogueL Aff.idL) Aff.idL.RL g s ↔ IsAdmissibleGerm g s := by
  rw [M4b.idL_HL_eq, catalogueL_idL hRH, M4b.idL_RL_eq]
  rfl

/-- Paper 1's local model with its concrete coefficient `ThmA.X α` (the body of paper 1's `ThmA.thm_A_local_proof`,
which states the model with an existential `X`), keeping `r ≤ Re α - 1`. -/
theorem thmA_local_concrete (hRH : RiemannHypothesis) {κ : ℝ} (hκ : ThmA.IsGoodSlant κ) {α : ℂ}
    (hα : α ∈ catalogue) :
    ∃ r : ℝ, 0 < r ∧ r ≤ α.re - 1 ∧ ∀ s₁ ∈ slitDisc (slantDir κ) α r, ∀ g : ℂ → ℂ, IsAdmissibleGerm g s₁ →
      ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (ball α r) ∧
        g =ᶠ[𝓝 s₁] fun s => ThmA.X α s * logAt (slantDir κ) α s + h s := by
  have hP := ThmA.isPrincipalSheet_Gnat hRH hκ
  obtain ⟨r, hr, hrα, hsub, H, hH, hEq⟩ := hP.local_form α hα
  refine ⟨r, hr, hrα, fun s₁ hs₁ g hg => ?_⟩
  obtain ⟨-, hev⟩ := ThmA.isBranch_of_admissible hκ hP hg
  obtain ⟨m, hm, hgm⟩ := hev.self_of_nhds (hsub hs₁)
  have hmA := ThmA.MSpan_analyticOn hm
  refine ⟨fun s => H s + m s, fun z hz =>
    ((hH z hz).add (hmA z (ThmA.ball_subset_HH hrα hz))).differentiableAt.differentiableWithinAt, ?_⟩
  have hopen := (ThmA.slitDisc_facts κ hr hrα).1
  filter_upwards [hgm, hopen.mem_nhds hs₁] with s hs1 hs2
  rw [hs1, hEq hs2]; ring

/-! ## Lemmas

Proved in `Fill/`, one file per lemma (same name, same statement): `Jseg_idL_kerG_eq_J`, `J_swap_one`, `Xcoef_idL_kerG_eq_X`, `hasCatalogueValues_congr`, `isAdmissibleGermOn_eventually`, `local_form_slitDiscL_of_slitDisc`. -/

/-! ## Target -/

/-- `ex_G` of `Paper2/Statements.lean`, statement verbatim. -/
theorem ex_G_proof (hRH : RiemannHypothesis) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6) :
    (∀ α ∈ catalogueL Aff.idL, ∃ r : ℝ, 0 < r ∧ ∀ s₁ ∈ slitDiscL α r, ∀ g : ℂ → ℂ,
      IsAdmissibleGermOn G (Aff.idL.HL \ catalogueL Aff.idL) Aff.idL.RL g s₁ →
      ∃ H : ℂ → ℂ, DifferentiableOn ℂ H (ball α r) ∧
        g =ᶠ[𝓝 s₁] fun s => Xcoef Aff.idL kerG α s * Complex.log (s - α) + H s) ∧
    HasCatalogueValues (fun α => deriv (Xcoef Aff.idL kerG α) α) ∧
    ∀ (g : ℂ → ℂ) (s₁ : ℂ), IsAdmissibleGermOn G (Aff.idL.HL \ catalogueL Aff.idL) Aff.idL.RL g s₁ →
      ∀ y r : ℝ, 0 < r → s₁ ∈ ball (1 + (y : ℂ) * I) r →
        ¬ GermExtendsMeromorphically g s₁ (ball (1 + (y : ℂ) * I) r) := by
  have _ := hZ1  -- (Z1), (Z2), (Z3), (Z6) are not used: paper 1's Theorem A needs RH only
  have _ := hZ2
  have _ := hZ3
  have _ := hZ6
  have hcat := catalogueL_idL hRH
  have hΩ : IsOpen (Aff.idL.HL \ catalogueL Aff.idL) := by
    rw [M4b.idL_HL_eq, hcat]; exact ThmA.catalogue_locallyFinite.2.2
  obtain ⟨κ, hκ⟩ := ThmA.lem_slant_proof hRH
  refine ⟨fun α hα => ?_, ?_, fun g s₁ hg y r hr hs₁ => ?_⟩
  · rw [hcat] at hα
    obtain ⟨r, hr, hrα, hloc⟩ := thmA_local_concrete hRH hκ hα
    refine ⟨r, hr, ?_⟩
    rw [Xcoef_idL_kerG_eq_X hα]
    exact local_form_slitDiscL_of_slitDisc (κ := κ) hr hrα
      ((ThmA.X_differentiableOn hα).mono (ThmA.ball_subset_HH hrα))
      (Adm := fun s g => IsAdmissibleGermOn G (Aff.idL.HL \ catalogueL Aff.idL) Aff.idL.RL g s)
      (fun _ _ h => analyticAt_of_isAdmissibleGermOn h) (fun _ _ h => isAdmissibleGermOn_eventually hΩ h)
      (fun s₁ hs₁ g hg => hloc s₁ hs₁ g ((admG_iff hRH).1 hg))
  · exact hasCatalogueValues_congr (fun α hα => by simp only [Xcoef_idL_kerG_eq_X hα])
      (ThmA.X_deriv_spec hRH).1
  · exact ThmA.thm_G_boundary_proof hRH ((admG_iff hRH).1 hg) y r hr hs₁

end GoldbachBoundaries.Paper2.M6
