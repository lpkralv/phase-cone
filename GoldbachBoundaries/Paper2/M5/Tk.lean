import GoldbachBoundaries.Paper2.M5.TkStep
import GoldbachBoundaries.Paper2.M5.Fill.Tk_strip_facts
import GoldbachBoundaries.Paper2.M5.Fill.exists_pole_near_line_Tk

/-!
# M5: Theorem G (`cl:thm:Tk`), the targets `thm_Tk` and `thm_Tk_poles`

`thm_Tk_proof` reads (i), (iii), (iv) off a package (`exists_tkPack`) and transfers (ii) to every meromorphic
continuation (`eventuallyEq_of_tkPack`). For the poles in the strip (`thm_Tk_poles_proof`), (iii) writes the package's
`F` near each point of `k - 1 < σ < k` as `H_k(s) + g(s)Q(L(s) - 1)` with `L(s) = s - k + 2` and `g(s) = kΓ(s-k+1)/Γ(s)`
holomorphic and zero-free, so M4b's `mero_mul_Qcont_app` gives the orders and residues (`Tk_strip_facts`), with
`R_b ≠ 0` under RH (M4a's `cP_ne_zero_of_RH`). The residue values at `k - 1 + 1/j` and `k - 1 + ρ/n` are M1's `Rcoef_inv`
and M4a's `lem_P_iv_values_proof`. The natural boundary: the points `k - 1 + ρ/n` are the scaled-zero pinches of
`L(s) = s - k + 2` and accumulate at every point of `σ = k - 1` (M4a's `prop_catalogue_ii_proof`), so paper 1's
`noMeromorphicExtensionAt_of_poles_in_every_ball` applies.

(Z1)-(Z3) of the signed-off statements are not used: under RH the growth of `Q` is paper 1's (review choice 2). (Z6) is
used, through `cl:lem:kernelt` in the growth bound (iv).
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-! ## Lemmas

Proved in `Fill/`, one file per lemma (same name, same statement): `Tk_strip_facts`, `exists_pole_near_line_Tk`. -/

/-! ## Real lemmas -/

/-- `ρ/n ∈ Σ_Q ∖ {1}` for a zero `ρ` and squarefree `n ≥ 1` (`ρ/n = 1` would make `ρ = n` real). -/
lemma div_mem_poleSetQ_diff_one {n : ℕ} (hn : 1 ≤ n) (hns : Squarefree n) {ρ : ℂ} (hρ : ρ ∈ NontrivialZeros) :
    ρ / (n : ℂ) ∈ PoleSetQ \ {1} := by
  refine ⟨Or.inr ⟨n, hn, hns, ρ, hρ, rfl⟩, fun h => ?_⟩
  have h' : ρ / (n : ℂ) = 1 := h
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hρn : ρ = n := by rwa [div_eq_one_iff_eq hn0] at h'
  apply im_ne_zero_of_mem_nontrivialZeros hρ
  rw [hρn]
  simp

/-- `1/j ∈ Σ_Q ∖ {1}` for squarefree `j ≥ 2`. -/
lemma inv_mem_poleSetQ_diff_one {j : ℕ} (hj : 2 ≤ j) (hjs : Squarefree j) :
    1 / (j : ℂ) ∈ PoleSetQ \ {1} := by
  refine ⟨Or.inl (Or.inr ⟨j, hj, hjs, rfl⟩), fun h => ?_⟩
  have h' : 1 / (j : ℂ) = 1 := h
  have hj0 : (j : ℂ) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
  rw [div_eq_one_iff_eq hj0] at h'
  have : (j : ℝ) = 1 := by exact_mod_cast h'.symm
  have : (2 : ℝ) ≤ j := by exact_mod_cast hj
  linarith

/-! ## Targets -/

/-- `thm_Tk` of `Paper2/Statements.lean`, statement verbatim. -/
theorem thm_Tk_proof (hRH : RiemannHypothesis) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6) (k : ℕ)
    (hk : 1 ≤ k) :
    (∃ F : ℂ → ℂ, MeromorphicOn F (halfPlane ((k : ℝ) - 1)) ∧ EqOn F (Tk k) (halfPlane k) ∧
      (∃ Hk : ℂ → ℂ, DifferentiableOn ℂ Hk {s | (k : ℝ) - 1 < s.re ∧ s.re < k} ∧
        ∀ Qc : ℂ → ℂ, IsQCont Qc → ∀ s : ℂ, (k : ℝ) - 1 < s.re → s.re < k →
          s - k + 1 ∉ PoleSetQ →
            F s = Hk s + k * (Gamma (s - k + 1) / Gamma s) * Qc (s - k + 1)) ∧
      ∀ x₁ x₂ : ℝ, (k : ℝ) - 1 / 2 < x₁ → x₁ ≤ x₂ → ∃ N C y₀ : ℝ, ∀ x ∈ Icc x₁ x₂, ∀ y : ℝ,
        y₀ ≤ |y| → ‖F (x + y * I)‖ ≤ C * |y| ^ N) ∧
    ∀ F : ℂ → ℂ, MeromorphicOn F (halfPlane ((k : ℝ) - 1)) →
      F =ᶠ[codiscreteWithin (halfPlane k)] Tk k →
      (∀ s ∈ halfPlane ((k : ℝ) - 1 / 2), s ≠ k → 0 ≤ meromorphicOrderAt F s) ∧
      meromorphicOrderAt F k = -1 ∧ HasResidue F k (1 / (k - 1).factorial) := by
  have _ := hZ1  -- (Z1)-(Z3) are not used: under RH the growth of `Q` is paper 1's `norm_Qcont_le_log`
  have _ := hZ2
  have _ := hZ3
  obtain ⟨F₀, H₀, hP⟩ := exists_tkPack hRH hZ6 k hk
  refine ⟨⟨F₀, hP.1, hP.2.1, ⟨H₀, hP.2.2.1, fun Qc hQc s hs1 hs2 hsQ => ?_⟩, hP.2.2.2.2.2.2.2⟩,
    fun F hF hFT => ?_⟩
  · have hpos : s - k + 1 ∈ halfPlane 0 := by
      show 0 < (s - k + 1).re
      simp only [add_re, sub_re, natCast_re, one_re]
      linarith
    rw [hP.2.2.2.1 s hs1 hs2 hsQ, (isQCont_eventuallyEq hQc).1 _ ⟨hpos, hsQ⟩]
  · have hev := eventuallyEq_of_tkPack hP hF hFT
    have hkmem : (k : ℂ) ∈ halfPlane ((k : ℝ) - 1) := by
      show (k : ℝ) - 1 < (k : ℂ).re
      simp
    refine ⟨fun s hs hsk => ?_, ?_, ?_⟩
    · have hs' : (k : ℝ) - 1 / 2 < s.re := hs
      have hsmem : s ∈ halfPlane ((k : ℝ) - 1) := by
        show (k : ℝ) - 1 < s.re
        linarith
      rw [meromorphicOrderAt_congr (hev s hsmem)]
      exact (hP.2.2.2.2.1 s hs' hsk).meromorphicOrderAt_nonneg
    · rw [meromorphicOrderAt_congr (hev k hkmem)]
      exact hP.2.2.2.2.2.1
    · exact M4b.hasResidue_congr_nhdsNE hP.2.2.2.2.2.2.1 (hev k hkmem).symm

/-- `thm_Tk_poles` of `Paper2/Statements.lean`, statement verbatim. -/
theorem thm_Tk_poles_proof (hRH : RiemannHypothesis) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6) (k : ℕ)
    (hk : 2 ≤ k) (F : ℂ → ℂ) (hF : MeromorphicOn F (halfPlane ((k : ℝ) - 1)))
    (hFT : F =ᶠ[codiscreteWithin (halfPlane k)] Tk k) :
    (∀ s : ℂ, (k : ℝ) - 1 < s.re → s.re < k →
      (meromorphicOrderAt F s < 0 ↔ s - (k - 1) ∈ PoleSetQ \ {1})) ∧
    (∀ b ∈ PoleSetQ \ {1}, meromorphicOrderAt F (k - 1 + b) = -1 ∧
      HasResidue F (k - 1 + b) (k * Rcoef b * Gamma b / Gamma (k - 1 + b)) ∧
      (k : ℂ) * Rcoef b * Gamma b / Gamma (k - 1 + b) ≠ 0) ∧
    (∀ j : ℕ, 2 ≤ j → Squarefree j →
      HasResidue F (k - 1 + 1 / (j : ℂ))
        (k * mu j * Gamma (1 / (j : ℂ)) / (j * Gamma (k - 1 + 1 / (j : ℂ))))) ∧
    (∀ n : ℕ, 1 ≤ n → Squarefree n → ∀ ρ ∈ NontrivialZeros,
      HasResidue F (k - 1 + ρ / (n : ℂ))
        (-(k * mu n * (zetaMult ρ : ℂ) * Gamma (ρ / (n : ℂ))) / (n * Gamma (k - 1 + ρ / (n : ℂ))))) ∧
    IsNaturalBoundary F (halfPlane ((k : ℝ) - 1)) {s | s.re = (k : ℝ) - 1} := by
  have _ := hZ2  -- (Z2), (Z3) are not used, as in `thm_Tk_proof`
  have _ := hZ3
  obtain ⟨F₀, H₀, hP⟩ := exists_tkPack hRH hZ6 k (by omega)
  have hev := eventuallyEq_of_tkPack hP hF hFT
  obtain ⟨hord, hres⟩ := Tk_strip_facts hRH hk hP
  have hbmem : ∀ b ∈ PoleSetQ \ {1}, (k : ℂ) - 1 + b ∈ halfPlane ((k : ℝ) - 1) := by
    intro b hb
    have hb0 := (poleSetQ_re_bounds hb.1).1
    show (k : ℝ) - 1 < ((k : ℂ) - 1 + b).re
    simp only [add_re, sub_re, natCast_re, one_re]
    linarith
  have hresF : ∀ b ∈ PoleSetQ \ {1},
      HasResidue F (k - 1 + b) (k * Rcoef b * Gamma b / Gamma (k - 1 + b)) := fun b hb =>
    M4b.hasResidue_congr_nhdsNE (hres b hb).2.1 (hev _ (hbmem b hb)).symm
  refine ⟨fun s hs1 hs2 => ?_, fun b hb => ⟨?_, hresF b hb, (hres b hb).2.2⟩, fun j hj hjs => ?_,
    fun n hn hns ρ hρ => ?_, fun s₀ hs₀ => ?_⟩
  · rw [meromorphicOrderAt_congr (hev s hs1)]
    exact hord s hs1 hs2
  · rw [meromorphicOrderAt_congr (hev _ (hbmem b hb))]
    exact (hres b hb).1
  · have h := hresF _ (inv_mem_poleSetQ_diff_one hj hjs)
    rw [Rcoef_inv hj hjs] at h
    have hval : (k : ℂ) * (mu j / (j : ℂ)) * Gamma (1 / (j : ℂ)) / Gamma (k - 1 + 1 / (j : ℂ)) =
        k * mu j * Gamma (1 / (j : ℂ)) / (j * Gamma (k - 1 + 1 / (j : ℂ))) := by ring
    rwa [hval] at h
  · have h := hresF _ (div_mem_poleSetQ_diff_one hn hns hρ)
    have hR : Rcoef (ρ / (n : ℂ)) = -(mu n * (zetaMult ρ : ℂ) / n) := by
      have := ((M4a.lem_P_iv_values_proof hRH hZ1).2.2.2 n hn hns ρ hρ)
      rw [cP] at this
      rw [← this, neg_neg]
    rw [hR] at h
    have hval : (k : ℂ) * -(mu n * (zetaMult ρ : ℂ) / n) * Gamma (ρ / (n : ℂ)) / Gamma (k - 1 + ρ / (n : ℂ)) =
        -(k * mu n * (zetaMult ρ : ℂ) * Gamma (ρ / (n : ℂ))) / (n * Gamma (k - 1 + ρ / (n : ℂ))) := by ring
    rwa [hval] at h
  · refine noMeromorphicExtensionAt_of_poles_in_every_ball (isOpen_halfPlane _) fun ε hε => ?_
    obtain ⟨a, ha, hne, hball, hneg⟩ := exists_pole_near_line_Tk hRH hk hP s₀ hs₀ ε hε
    exact ⟨a, ha, hne, hball, by rwa [meromorphicOrderAt_congr (hev a ha)]⟩

end GoldbachBoundaries.Paper2.M5
