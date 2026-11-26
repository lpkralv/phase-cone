import GoldbachBoundaries.Paper2.M3.Classical

/-!
# M3 skeleton: the targets of Milestone M3 (paper 2's Theorem C and its inputs)

Each `*_proof` theorem has the statement of the theorem of the same name (without `_proof`) in
`Paper2/Statements.lean`, copied verbatim, and a real proof from the M3 lemmas (and M1, M2, paper 1); the target files
have no `sorry` in any target. A target that a later file uses is proved in its own file, so that fillers can import
it without a cycle:

| Target | File |
|---|---|
| `lem_A_proof` | `AConst.lean` |
| `cor_one_add_RH_proof`, `thm_real_a_proof`, `thm_real_b_proof`, `rem_dichotomy_ii_proof` | `Real.lean` |
| `lem_hsq_proof` | `Hsq.lean` |
| `lem_Landau_proof` | `Landau.lean` |
| `thm_test_proof`, `cor_test_proof` | `Test.lean` |
| `rem_classical_ii_proof` | `Classical.lean` |
| `rem_classical_iii_proof` | this file |

The type match is checked by `example : type_of% @GoldbachBoundaries.Paper2.X := @GoldbachBoundaries.Paper2.M3.X_proof`
from a scratch file that imports both (this file does not import `Paper2/Statements.lean`). Once every M3 lemma is
filled, each of the 11 statements closes by `exact M3.X_proof ...`, and `intro_thm_C` (already proved from
`thm_real_a`, `thm_real_b`, `thm_test` in `Paper2/Statements.lean`) becomes sorry-free.

**Changes of proof (statements unchanged).**
1. `cor_one_add_RH` and `thm_real_a` (and so the necessity half of `thm_test`) come from paper 1's `cor_T_poles`, not
   from M1's continuation: under RH paper 1 already has `T` on `ℍ` with its catalogue residues. Their premises (Z1),
   (Z2), (Z3), (Z6) are not used.
2. Steps 3-4 of `nr:thm:test` are proved once, for an arbitrary point `x` of convergence of `𝓜`
   (`re_le_of_mem_mellinConvSet`), and used both for `thm_test` (`x > 1`) and for `nr:rem:classical`(ii) (`x ≥ 2B`).
3. Step 2 of `nr:thm:test` (Landau at the abscissa) is proved once, for discs centred on a real segment `(a, 2]`
   (`mem_mellinConvSet_of_differentiableOn_balls`), and used for `thm_test` (`a = 1`) and `nr:rem:classical`(iii)
   (`a = 2B`).
4. The upper bound `|Γ(x + it)|² ≤ 4π/(1 + t²)²` of `nr:lem:A`(b) is planned through `Γ(s + 2) = s(s + 1)Γ(s)` and
   `|Γ(s + 2)| ≤ Γ(Re s + 2)` instead of the Weierstrass product (same bound).
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M3

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1 GoldbachBoundaries.Paper2.M2

/-- `rem_classical_iii` of `Paper2/Statements.lean`, statement verbatim. -/
theorem rem_classical_iii_proof (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6) (hZ7 : Z7) (h : Binf < Bsup) :
    (∀ x : ℝ, 2 * Bsup < x → x ∈ mellinConvSet) ∧ (∀ x ∈ mellinConvSet, 2 * Bsup ≤ x) ∧
    sigmaC = 2 * Bsup ∧
    (∃ Mc : ℂ → ℂ, MeromorphicOn Mc (halfPlane (2 * Binf)) ∧ EqOn Mc Mcal (halfPlane 2)) ∧
    0 < Real.Gamma (2 * Bsup) * Aconst ∧
    ∀ Mc : ℂ → ℂ, MeromorphicOn Mc (halfPlane (2 * Binf)) →
      Mc =ᶠ[codiscreteWithin (halfPlane 2)] Mcal →
      meromorphicOrderAt Mc ((2 * Bsup : ℝ) : ℂ) = -1 ∧
        HasResidue Mc ((2 * Bsup : ℝ) : ℂ) ((Real.Gamma (2 * Bsup) * Aconst : ℝ) : ℂ) := by
  have _ := hZ6  -- (Z6) is not needed on the M1 route (polynomial Gamma decay)
  obtain ⟨hB1, hB2, -, ⟨ρ, hρ, hre⟩⟩ := lem_B_iv_proof hZ1 h
  obtain ⟨hA0, -, -, -⟩ := lem_A_proof hZ7 hB1 hB2 ⟨ρ, hρ, hre⟩
  have hBinf := half_le_Binf hZ1
  have hsub : halfPlane (2 * Binf) ⊆ HH := fun s hs => by
    show (1 : ℝ) < s.re
    have : 2 * Binf < s.re := hs
    linarith
  obtain ⟨hTm, -, -⟩ := Tcont_props hZ1 hZ2 hZ3
  have hMm : MeromorphicOn (Mform Tcont) (halfPlane (2 * Binf)) := meromorphicOn_Mform hTm hsub
  have hMeq : EqOn (Mform Tcont) Mcal (halfPlane 2) := fun s hs =>
    Mform_eq_Mcal hs (Tcont_eqOn_T hZ1 hZ2 hZ3 hs)
  have hI : ∀ x ∈ Ioc (2 * Bsup) 2, (x : ℂ) ∈ halfPlane (2 * Binf) := fun x hx => by
    show 2 * Binf < (x : ℂ).re
    rw [ofReal_re]
    linarith [hx.1]
  obtain ⟨r, hr, -, Mt, hMt, hMtF⟩ :=
    exists_differentiableOn_balls (isOpen_halfPlane _) hMm hI (order_Mform_Tcont_nonneg hZ1 hZ2 hZ3 h)
  have hEq : EqOn Mt Mcal (ballsU (2 * Bsup) 2 r ∩ halfPlane 2) := fun s hs => by
    have hs2 : 2 < s.re := hs.2
    have hev : Tcont =ᶠ[𝓝 s] T :=
      Filter.eventuallyEq_of_mem ((isOpen_halfPlane 2).mem_nhds hs.2) (Tcont_eqOn_T hZ1 hZ2 hZ3)
    rw [hMtF s hs.1 (analyticAt_Mform_of_eq_T hs2 hev)]
    exact hMeq hs.2
  have h1 : ∀ x : ℝ, 2 * Bsup < x → x ∈ mellinConvSet :=
    mem_mellinConvSet_of_differentiableOn_balls (by linarith) hr hMt hEq
  have h2 : ∀ x ∈ mellinConvSet, 2 * Bsup ≤ x := (rem_classical_ii_proof hZ1).2.1
  have hsig : sigmaC = 2 * Bsup := by
    apply le_antisymm
    · refine le_of_forall_pos_lt_add fun ε hε => ?_
      have hmem := h1 (2 * Bsup + ε / 2) (by linarith)
      have := csInf_le ⟨2 * Bsup, h2⟩ hmem
      unfold sigmaC
      linarith
    · exact le_csInf ⟨3, h1 3 (by linarith)⟩ h2
  have hGA : 0 < Real.Gamma (2 * Bsup) * Aconst := mul_pos (Real.Gamma_pos_of_pos (by linarith)) hA0
  refine ⟨h1, h2, hsig, ⟨Mform Tcont, hMm, hMeq⟩, hGA, fun Mc hMc hMcE => ?_⟩
  have hmem : ((2 * Bsup : ℝ) : ℂ) ∈ halfPlane (2 * Binf) := by
    show 2 * Binf < ((2 * Bsup : ℝ) : ℂ).re
    rw [ofReal_re]
    linarith
  have hev := eventuallyEq_nhdsNE_of_codiscrete_halfPlane (by linarith) hMc hMm hMeq hMcE hmem
  have hres := (hasResidue_Mform_Tcont_two_Bsup hZ1 hZ2 hZ3 h).congr hev.symm
  exact ⟨hres.meromorphicOrderAt_eq_neg_one (hMc _ hmem) (ofReal_ne_zero.mpr hGA.ne'), hres⟩

end GoldbachBoundaries.Paper2.M3
