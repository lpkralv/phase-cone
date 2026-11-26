import GoldbachBoundaries.Paper2.M3.Mellin
import GoldbachBoundaries.Paper2.M3.Fill.order_Mform_nonneg_of_test

/-!
# M3: the RH test (`nr:thm:test` = Theorem C (c), `nr:cor:test`)

**Necessity** (RH `→`): paper 1's `cor_T_poles` gives `F₀` meromorphic on `ℍ`, equal to the series on `σ > 2`, with a
simple pole at every catalogue point; take `U = ℍ`, `T̃ = F₀`, and read the real poles off `thm_real_a_proof`.

**Sufficiency** (`←`), the paper's Steps 1-4:

1. `𝓜̃ = Mform T̃` is meromorphic on `U ∩ ℍ` with order `≥ 0` at every point of `(1, 2]`
   (`order_Mform_nonneg_of_test`: at `1 + 1/k` the principal parts `2μ(k)Γ(1 + 1/k)` and `2Γ(1/k)μ(k)/k` cancel; at `2`
   the residue `1` of `T̃` is forced by `lem_hsq_proof` and the three principal parts cancel). Removing the
   singularities on discs about the points of `(1, 2]` (`exists_differentiableOn_balls`) gives a holomorphic `Mt` on
   `U₀ = ballsU 1 2 r`, equal to `𝓜` on `U₀ ∩ {σ > 2}` (`Mform_eq_Mcal`, `analyticAt_Mform_of_eq_T`).
2. Landau: every `x > 1` is in `mellinConvSet` (`mem_mellinConvSet_of_differentiableOn_balls`).
3. and 4. A zero with `β ≥ 1/2` has `β ≤ x/2` for every `x > 1` (`re_le_of_mem_mellinConvSet`), so `β = 1/2`; with
   (Z1) every zero has `β = 1/2`, which is Mathlib's RH (`riemannHypothesis_iff`).

`cor_test`: under `(H_∞)`, `B_∞ = 1/2`, so M1's `Tcont` is meromorphic on `ℍ`, equal to the series on `σ > 2`, and any
`F` of the statement equals `Tcont` near every point of `ℍ`; `→` is `thm_real_a_proof` (with the order `-1` from the
non-zero residue), `←` is the sufficiency of `thm_test_proof` with `U = ℍ`, `T̃ = Tcont`.

The targets are at the end of the file.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M3

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1 GoldbachBoundaries.Paper2.M2

/-! ## Real lemmas -/

/-- Steps 1-2 of `nr:thm:test`: the test data make `𝓜(x)` converge for every `x > 1`. -/
theorem mem_mellinConvSet_of_test {U : Set ℂ} {Tt : ℂ → ℂ} (h : IsTestPair U Tt) :
    ∀ x : ℝ, 1 < x → x ∈ mellinConvSet := by
  obtain ⟨hU, hUx, hTt, hEq, -, -⟩ := id h
  have hW : IsOpen (U ∩ HH) := hU.inter (isOpen_halfPlane 1)
  have hMm : MeromorphicOn (Mform Tt) (U ∩ HH) :=
    meromorphicOn_Mform (hTt.mono_set inter_subset_left) inter_subset_right
  have hI : ∀ x ∈ Ioc (1 : ℝ) 2, (x : ℂ) ∈ U ∩ HH := fun x hx =>
    ⟨hUx x hx, by
      show (1 : ℝ) < (x : ℂ).re
      simpa using hx.1⟩
  obtain ⟨r, hr, hsub, Mt, hMt, hMtF⟩ := exists_differentiableOn_balls hW hMm hI (order_Mform_nonneg_of_test h)
  refine mem_mellinConvSet_of_differentiableOn_balls (by norm_num) hr hMt fun s hs => ?_
  have hsU : s ∈ U := (hsub hs.1).1
  have hs2 : 2 < s.re := hs.2
  have hnhds : U ∩ halfPlane 2 ∈ 𝓝 s := (hU.inter (isOpen_halfPlane 2)).mem_nhds ⟨hsU, hs.2⟩
  have hev : Tt =ᶠ[𝓝 s] T := Filter.eventuallyEq_of_mem hnhds hEq
  rw [hMtF s hs.1 (analyticAt_Mform_of_eq_T hs2 hev)]
  exact Mform_eq_Mcal hs2 (hEq ⟨hsU, hs.2⟩)

/-- Steps 3-4 of `nr:thm:test` ((Z1)): if `𝓜(x)` converges for every `x > 1`, RH holds. -/
theorem RH_of_forall_mem_mellinConvSet (hZ1 : Z1) (h : ∀ x : ℝ, 1 < x → x ∈ mellinConvSet) :
    RiemannHypothesis := by
  have hhalf : ∀ ρ ∈ NontrivialZeros, 1 / 2 ≤ ρ.re → ρ.re ≤ 1 / 2 := by
    intro ρ hρ hre
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    have := re_le_of_mem_mellinConvSet (h (1 + ε) (by linarith)) hρ hre
    linarith
  rw [riemannHypothesis_iff]
  intro ρ hρ
  by_cases hre : 1 / 2 ≤ ρ.re
  · exact le_antisymm (hhalf ρ hρ hre) hre
  · push Not at hre
    have h' := hhalf _ ((hZ1 ρ hρ).2.1) (by simp; linarith)
    simp at h'
    linarith

/-! ## Target: `thm_test` -/

/-- `thm_test` of `Paper2/Statements.lean`, statement verbatim. -/
theorem thm_test_proof (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6) :
    RiemannHypothesis ↔
      ∃ U : Set ℂ, IsOpen U ∧ (∀ x : ℝ, x ∈ Ioc (1 : ℝ) 2 → (x : ℂ) ∈ U) ∧
        ∃ Tt : ℂ → ℂ, MeromorphicOn Tt U ∧ EqOn Tt T (U ∩ halfPlane 2) ∧
          (∀ x : ℝ, x ∈ Ioo (1 : ℝ) 2 →
            (meromorphicOrderAt Tt x < 0 ↔ ∃ k : ℕ, 2 ≤ k ∧ Squarefree k ∧ (x : ℂ) = 1 + 1 / (k : ℂ))) ∧
          ∀ k : ℕ, 2 ≤ k → Squarefree k →
            meromorphicOrderAt Tt (1 + 1 / (k : ℂ)) = -1 ∧ HasResidue Tt (1 + 1 / (k : ℂ)) (2 * mu k) := by
  constructor
  · intro hRH
    obtain ⟨F₀, hF₀m, hF₀T, -, hF₀o, -⟩ := cor_T_poles hRH
    obtain ⟨-, hall⟩ := thm_real_a_proof hRH hZ1 hZ2 hZ3 hZ6
    obtain ⟨hord, hres⟩ := hall F₀ hF₀m (eventuallyEq_codiscreteWithin_of_eqOn hF₀T)
    refine ⟨HH, isOpen_halfPlane 1, fun x hx => ?_, F₀, hF₀m, fun s hs => hF₀T hs.2, hord,
      fun k hk hsq => ⟨hF₀o _ (Or.inl (Or.inr ⟨k, hk, hsq, rfl⟩)), hres k hk hsq⟩⟩
    show (1 : ℝ) < (x : ℂ).re
    simpa using hx.1
  · rintro ⟨U, hU, hUx, Tt, hTt, hEq, hord, hres⟩
    exact RH_of_forall_mem_mellinConvSet hZ1 (mem_mellinConvSet_of_test ⟨hU, hUx, hTt, hEq, hord, hres⟩)

/-! ## Target: `cor_test` -/

/-- `cor_test` of `Paper2/Statements.lean`, statement verbatim. -/
theorem cor_test_proof (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6)
    (F : ℂ → ℂ) (hF : MeromorphicOn F HH) (hFT : F =ᶠ[codiscreteWithin (halfPlane 2)] T) :
    RiemannHypothesis ↔
      (∀ x : ℝ, x ∈ Ioo (1 : ℝ) 2 →
        (meromorphicOrderAt F x < 0 ↔ ∃ k : ℕ, 2 ≤ k ∧ Squarefree k ∧ (x : ℂ) = 1 + 1 / (k : ℂ))) ∧
      ∀ k : ℕ, 2 ≤ k → Squarefree k →
        meromorphicOrderAt F (1 + 1 / (k : ℂ)) = -1 ∧ HasResidue F (1 + 1 / (k : ℂ)) (2 * mu k) := by
  have hmuk : ∀ k : ℕ, Squarefree k → (2 * mu k : ℂ) ≠ 0 := fun k hsq =>
    mul_ne_zero two_ne_zero (Int.cast_ne_zero.mpr (ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hsq))
  have hkH : ∀ k : ℕ, 2 ≤ k → Squarefree k → (1 + 1 / (k : ℂ)) ∈ HH := fun k hk hsq =>
    catalogue_subset_HH (Or.inl (Or.inr ⟨k, hk, hsq, rfl⟩))
  constructor
  · intro hRH
    obtain ⟨-, hall⟩ := thm_real_a_proof hRH hZ1 hZ2 hZ3 hZ6
    obtain ⟨hord, hres⟩ := hall F hF hFT
    exact ⟨hord, fun k hk hsq =>
      ⟨(hres k hk hsq).meromorphicOrderAt_eq_neg_one (hF _ (hkH k hk hsq)) (hmuk k hsq), hres k hk hsq⟩⟩
  · rintro ⟨hord, hres⟩
    have hBinf : Binf = 1 / 2 := Binf_eq_half_of_Hinf hZ1 hH
    have hHH : halfPlane (2 * Binf) = HH := by
      rw [hBinf]
      norm_num
    obtain ⟨hmero, -, -⟩ := Tcont_props hZ1 hZ2 hZ3
    rw [hHH] at hmero
    have hF' : MeromorphicOn F (halfPlane (2 * Binf)) := by
      rw [hHH]
      exact hF
    have hev : ∀ s ∈ HH, F =ᶠ[𝓝[≠] s] Tcont := fun s hs =>
      eventuallyEq_Tcont_of_codiscrete hZ1 hZ2 hZ3 hF' hFT (by rw [hHH]; exact hs)
    have hxH : ∀ x : ℝ, 1 < x → (x : ℂ) ∈ HH := fun x hx => by
      show (1 : ℝ) < (x : ℂ).re
      simpa using hx
    refine (thm_test_proof hZ1 hZ2 hZ3 hZ6).2 ⟨HH, isOpen_halfPlane 1, fun x hx => hxH x hx.1, Tcont, hmero,
      fun s hs => Tcont_eqOn_T hZ1 hZ2 hZ3 hs.2, fun x hx => ?_, fun k hk hsq => ?_⟩
    · rw [← meromorphicOrderAt_congr (hev _ (hxH x hx.1))]
      exact hord x hx
    · obtain ⟨h1, h2⟩ := hres k hk hsq
      exact ⟨by rw [← meromorphicOrderAt_congr (hev _ (hkH k hk hsq))]; exact h1,
        h2.congr (hev _ (hkH k hk hsq))⟩

end GoldbachBoundaries.Paper2.M3
