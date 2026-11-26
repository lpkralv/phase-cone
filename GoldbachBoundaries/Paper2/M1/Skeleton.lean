import GoldbachBoundaries.Paper2.M1.Assembly

/-!
# M1 skeleton: the targets of Milestone M1 (paper 2's Theorem A and its inputs)

Each `*_proof` theorem has the statement of the theorem of the same name (without `_proof`) in
`Paper2/Statements.lean`, copied verbatim, and a real proof from the M1 lemmas; this file has no `sorry` of its own.
The type match is checked by `example : type_of% @GoldbachBoundaries.Paper2.X := @GoldbachBoundaries.Paper2.M1.X_proof`
from a scratch file that imports both (this file does not import `Paper2/Statements.lean`). Once every M1 lemma is
filled, each sorried statement `X` of `Paper2/Statements.lean` in the list below closes by `exact X_proof ...`:

`lem_Q_i`, `lem_Q_ii`, `lem_B_i`, `lem_B_ii`, `lem_B_iii`, `lem_B_iv`, `lem_MB`, `lem_growthQ`, `thm_cont`,
`thm_residue`, `cor_one_add`, `cor_one_add_pairs` (12 of the 76). With them `intro_thm_A` and `cor_one_add_values`
(already proved from these in `Paper2/Statements.lean`) become sorry-free.

`lem_MB`, `thm_cont`, `thm_residue` carry (Z6) in their signed-off statements; the M1 route uses paper 1's polynomial
Gamma decay instead of Stirling, so their proofs do not use it.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M1

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- `lem_Q_i` of `Paper2/Statements.lean`, statement verbatim. -/
theorem lem_Q_i_proof (hZ1 : Z1) :
    (∀ Qc : ℂ → ℂ, IsQCont Qc →
      (∀ z ∈ halfPlane 0 \ PoleSetQ, Qc (conj z) = conj (Qc z)) ∧
      ∀ a ∈ PoleSetQ, -1 ≤ meromorphicOrderAt Qc a ∧ HasResidue Qc a (Rcoef a) ∧
        (meromorphicOrderAt Qc a < 0 ↔ Rcoef a ≠ 0)) ∧
    (∀ a ∈ PoleSetQ, (Rcoef a).im = 0 ∧ Rcoef (conj a) = Rcoef a) ∧
    Rcoef 1 = 1 ∧
    (∀ k : ℕ, 2 ≤ k → Squarefree k → Rcoef (1 / (k : ℂ)) = mu k / k) ∧
    ∀ a ∈ PoleSetQ, a.im ≠ 0 →
      Rcoef a = -∑ᶠ k ∈ {k : ℕ | 1 ≤ k ∧ Squarefree k ∧ (k : ℝ) < 1 / a.re ∧
          (k : ℂ) * a ∈ NontrivialZeros}, mu k / k * (zetaMult ((k : ℂ) * a) : ℂ) := by
  refine ⟨fun Qc hQc => ⟨fun z hz => ?_, fun a ha => ?_⟩, fun a ha => Rcoef_real_conj hZ1 ha, Rcoef_one',
    fun k hk hsq => Rcoef_inv hk hsq, fun a ha him => Rcoef_eq_finsum ha him⟩
  · have h1 := (isQCont_eventuallyEq hQc).1
    have hz' : conj z ∈ halfPlane 0 \ PoleSetQ := by
      refine ⟨?_, fun h => hz.2 ?_⟩
      · have : 0 < z.re := hz.1
        show 0 < (conj z).re
        simpa using this
      · simpa using conj_mem_poleSetQ h
    rw [h1 _ hz', h1 _ hz, Qcont_conj hz]
  · have hpos : 0 < a.re := re_pos_of_mem_poleSetQ ha
    have hev := (isQCont_eventuallyEq hQc).2 a hpos
    refine ⟨?_, ?_, ?_⟩
    · rw [meromorphicOrderAt_congr hev]
      exact meromorphicOrderAt_Qcont_ge hpos
    · exact (hasResidue_Qcont_Rcoef ha).congr hev.symm
    · rw [meromorphicOrderAt_congr hev]
      exact meromorphicOrderAt_Qcont_neg_iff ha

/-- `lem_Q_ii` of `Paper2/Statements.lean`, statement verbatim. -/
theorem lem_Q_ii_proof (hZ1 : Z1) :
    (∀ z ∈ halfPlane 0, ∃ U ∈ 𝓝 z, (U ∩ PoleSetQ).Finite) ∧
    (∀ a ∈ PoleSetQ, a ≠ 1 → a.re ≤ Bsup) ∧
    ∀ a ∈ PoleSetQ, a ≠ 1 → a ∉ NontrivialZeros → a.re ≤ 1 / 2 := by
  exact ⟨poleSetQ_locallyFinite, fun a ha ha1 => poleSetQ_re_le_Bsup hZ1 ha ha1,
    fun a ha ha1 haZ => (poleSetQ_re_bounds ha).2.2 ha1 haZ⟩

/-- `lem_B_i` of `Paper2/Statements.lean`, statement verbatim. -/
theorem lem_B_i_proof (hZ1 : Z1) :
    1 / 2 ≤ Binf ∧ Binf ≤ Bsup ∧ Bsup ≤ 1 ∧
      ∀ δ : ℝ, 0 < δ → {ρ | ρ ∈ NontrivialZeros ∧ Binf + δ < ρ.re}.Finite := by
  exact ⟨half_le_Binf hZ1, Binf_le_Bsup_le_one.1, Binf_le_Bsup_le_one.2,
    fun δ hδ => finite_zeros_re_gt δ hδ⟩

/-- `lem_B_ii` of `Paper2/Statements.lean`, statement verbatim. -/
theorem lem_B_ii_proof (hZ1 : Z1) :
    ∀ δ : ℝ, 0 < δ → (Fdelta δ).Finite ∧ (∀ a ∈ PoleSetQ \ Fdelta δ, a.re ≤ Binf + δ) ∧
      (δ < 1 - Binf → Fdelta δ = {1} ∪ {ρ | ρ ∈ NontrivialZeros ∧ Binf + δ < ρ.re}) := by
  intro δ hδ
  obtain ⟨hfin, heq⟩ := Fdelta_spec hZ1 δ hδ
  refine ⟨hfin, fun a ha => ?_, heq⟩
  by_contra hlt
  exact ha.2 ⟨ha.1, lt_of_not_ge hlt⟩

/-- `lem_B_iii` of `Paper2/Statements.lean`, statement verbatim. -/
theorem lem_B_iii_proof (hH : Hinf) : Bsup < 1 := by
  exact Bsup_lt_one_of_Hinf hH

/-- `lem_B_iv` of `Paper2/Statements.lean`, statement verbatim. -/
theorem lem_B_iv_proof (hZ1 : Z1) (h : Binf < Bsup) :
    1 / 2 < Bsup ∧ Bsup < 1 ∧ {ρ | ρ ∈ NontrivialZeros ∧ ρ.re = Bsup}.Finite ∧
      {ρ | ρ ∈ NontrivialZeros ∧ ρ.re = Bsup}.Nonempty := by
  obtain ⟨h1, h2, h3⟩ := Bsup_attained h
  exact ⟨by linarith [half_le_Binf hZ1], h1, h2, h3⟩

/-- `lem_MB` of `Paper2/Statements.lean`, statement verbatim. -/
theorem lem_MB_proof (hZ6 : Z6) {s : ℂ} (hs : 2 < s.re) {c : ℝ} (hc1 : 1 < c) (hc2 : c < s.re - 1) :
    Integrable (fun t : ℝ => KerS s (c + t * I) * Q (c + t * I) * Q (s - (c + t * I))) ∧
      T s = VerticalIntegral' (fun w => KerS s w * Q w * Q (s - w)) c := by
  have _ := hZ6  -- (Z6) is not needed on the M1 route (polynomial Gamma decay)
  exact ⟨integrable_KerS_Q_line hs hc1 hc2, T_eq_verticalIntegral'_KerS hs hc1 hc2⟩

/-- `lem_growthQ` of `Paper2/Statements.lean`, statement verbatim. -/
theorem lem_growthQ_proof (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) :
    ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ H : ℝ, 2 ≤ H →
      (∀ ρ ∈ NontrivialZeros, H - 1 ≤ |ρ.im| → ρ.re ≤ Binf + δ) →
      ∀ Qc : ℂ → ℂ, IsQCont Qc → ∀ w : ℂ, Binf + 2 * δ ≤ w.re → H ≤ |w.im| →
        w ∉ PoleSetQ ∧ ‖Qc w‖ ≤ C * Real.log |w.im| := by
  intro δ hδ
  obtain ⟨C, hC⟩ := norm_Qcont_le_growth hZ1 hZ2 hZ3 δ hδ
  refine ⟨C, fun H hH2 hH Qc hQc w hw hwH => ?_⟩
  obtain ⟨hnot, hb⟩ := hC H ⟨hH2, hH⟩ w hw hwH
  refine ⟨hnot, ?_⟩
  have hpos : 0 < w.re := by
    have := half_le_Binf hZ1
    linarith
  rw [(isQCont_eventuallyEq hQc).1 w ⟨hpos, hnot⟩]
  exact hb

/-- `thm_cont` of `Paper2/Statements.lean`, statement verbatim. -/
theorem thm_cont_proof (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6) :
    ∃ F : ℂ → ℂ, MeromorphicOn F (halfPlane (2 * Binf)) ∧ EqOn F T (halfPlane 2) ∧
      AnalyticOnNhd ℂ F (halfPlane (2 * Binf) \ Pinch) ∧
      (∀ s ∈ halfPlane (2 * Binf), -1 ≤ meromorphicOrderAt F s) ∧
      (∀ s ∈ halfPlane (2 * Binf) \ Pinch, F (conj s) = conj (F s)) ∧
      ∀ δ : ℝ, 0 < δ → δ < (1 - Binf) / 2 → ∀ c : ℝ, Binf + 2 * δ < c → c < 1 →
        (∀ a ∈ Fdelta δ, c ≠ a.re) → ∀ Qc : ℂ → ℂ, IsQCont Qc →
        DifferentiableOn ℂ (fun s => VerticalIntegral' (fun w => KerS s w * Qc w * Qc (s - w)) c)
            {s | c + Binf + 2 * δ < s.re ∧ ∀ a ∈ Fdelta δ, s.re ≠ c + a.re} ∧
        (∀ a ∈ Fdelta δ, MeromorphicOn (fun s => Rcoef a * KerS s a * Qc (s - a)) (halfPlane a.re) ∧
          halfPlane (2 * Binf) ⊆ halfPlane a.re) ∧
        ∀ s : ℂ, c + Binf + 2 * δ < s.re → (∀ a ∈ Fdelta δ, s.re ≠ c + a.re) → s ∉ Pinch →
          F s = VerticalIntegral' (fun w => KerS s w * Qc w * Qc (s - w)) c +
            ∑ᶠ a ∈ Fdelta δ, (iverson (c < a.re) + iverson (s.re - a.re < c)) *
              Rcoef a * KerS s a * Qc (s - a) := by
  have _ := hZ6  -- (Z6) is not needed on the M1 route (polynomial Gamma decay)
  obtain ⟨hmero, hana, hord⟩ := Tcont_props hZ1 hZ2 hZ3
  refine ⟨Tcont, hmero, Tcont_eqOn_T hZ1 hZ2 hZ3, hana, hord, fun s hs => Tcont_conj hZ1 hZ2 hZ3 hs, ?_⟩
  intro δ hδ hδ1 c hc1 hc2 hcF Qc hQc
  have hadm : AdmC δ c := ⟨hδ, hδ1, hc1, hc2, hcF⟩
  refine ⟨?_, fun a ha => ⟨meromorphicOn_term hQc ha.1, halfPlane_two_Binf_subset hZ1 ha.1⟩, ?_⟩
  · refine (Ic_differentiableOn hZ1 hZ2 hZ3 hadm).congr ?_
    intro s hs
    exact IcQ_congr hZ1 hQc hadm hs
  · intro s hs1 hs2 hsP
    have hs : s ∈ RegC δ c := ⟨hs1, hs2⟩
    rw [Tcont_eq_Tc hZ1 hZ2 hZ3 hadm hs hsP]
    exact (TcQ_congr hZ1 hQc hadm hs hsP).symm

/-- `thm_residue` of `Paper2/Statements.lean`, statement verbatim. -/
theorem thm_residue_proof (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6) {s₀ : ℂ} (hs₀ : 2 * Binf < s₀.re) :
    (pinchPairs s₀).Finite ∧
      ∀ F : ℂ → ℂ, MeromorphicOn F (halfPlane (2 * Binf)) →
        F =ᶠ[codiscreteWithin (halfPlane 2)] T →
        HasResidue F s₀ (pairSum s₀) ∧ (s₀ ∉ Pinch → 0 ≤ meromorphicOrderAt F s₀) := by
  have _ := hZ6  -- (Z6) is not needed on the M1 route (polynomial Gamma decay)
  refine ⟨pinchPairs_finite hZ1 hs₀, fun F hF hFT => ?_⟩
  have hev := eventuallyEq_Tcont_of_codiscrete hZ1 hZ2 hZ3 hF hFT hs₀
  refine ⟨(hasResidue_Tcont hZ1 hZ2 hZ3 hs₀).congr hev.symm, fun hP => ?_⟩
  rw [meromorphicOrderAt_congr hev]
  exact ((Tcont_props hZ1 hZ2 hZ3).2.1 s₀ ⟨hs₀, hP⟩).meromorphicOrderAt_nonneg

/-- `cor_one_add` of `Paper2/Statements.lean`, statement verbatim. -/
theorem cor_one_add_proof (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6) {u : ℂ} (hu : u ∈ PoleSetQ)
    (hu2 : 2 * Binf < 1 + u.re) (hpairs : pinchPairs (1 + u) ⊆ {(1, u), (u, 1)})
    (F : ℂ → ℂ) (hF : MeromorphicOn F (halfPlane (2 * Binf)))
    (hFT : F =ᶠ[codiscreteWithin (halfPlane 2)] T) :
    (u ≠ 1 → HasResidue F (1 + u) (2 * Rcoef u / u)) ∧ (u = 1 → HasResidue F 2 1) := by
  have hre : 2 * Binf < (1 + u).re := by simpa using hu2
  have hres := ((thm_residue_proof hZ1 hZ2 hZ3 hZ6 hre).2 F hF hFT).1
  rw [pairSum_one_add hu hpairs] at hres
  refine ⟨fun h1 => by rwa [ite_eq_right h1] at hres, fun h1 => ?_⟩
  subst h1
  rw [ite_eq_left rfl] at hres
  have h2 : (1 : ℂ) + 1 = 2 := by norm_num
  rwa [h2] at hres

/-- `cor_one_add_pairs` of `Paper2/Statements.lean`, statement verbatim. -/
theorem cor_one_add_pairs_proof (hZ1 : Z1) {u : ℂ} (hu : u ∈ PoleSetQ) (h : 2 * Bsup < 1 + u.re) :
    pinchPairs (1 + u) ⊆ {(1, u), (u, 1)} := by
  exact pinchPairs_one_add_subset hZ1 hu h

end GoldbachBoundaries.Paper2.M1
