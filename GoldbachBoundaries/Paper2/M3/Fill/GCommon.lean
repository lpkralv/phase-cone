import GoldbachBoundaries.Paper2.M3.Defs

/-!
# M3 fill, group G (residue cancellations): shared helpers

* `gc_meromorphicAt_Mform`: `Mform F` is meromorphic at `x` (`Re x > 1`) when `F` is.
* `gc_hasResidue_Mform`: the residue of `Mform F` at `x` (`Re x > 1`) from the residues of `F` at `x` and of `Qcont` at
  `x - 1`: `Γ(x)c_F - 2Γ(x - 1)c_Q + [x = 2]`.
* `gc_order_nonneg_of_hasResidue_zero`: a meromorphic function with residue `0` (in the `HasResidue` sense) has
  order `≥ 0`.
* `gc_hasResidue_zero_of_order_nonneg`: conversely, order `≥ 0` gives residue `0`.
* `gc_hasResidue_Qcont_real`: at a real `y ∈ (0, 1)` that is no `1/k` (`k ≥ 2` squarefree), `Qcont` is analytic, so
  its residue is `0`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M3

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1 GoldbachBoundaries.Paper2.M2

/-- `Γ` is analytic on `Re s > 0`. -/
lemma gc_analyticAt_Gamma {s : ℂ} (hs : 0 < s.re) : AnalyticAt ℂ Gamma s := by
  have hd : ∀ᶠ z in 𝓝 s, DifferentiableAt ℂ Gamma z := by
    filter_upwards [(isOpen_halfPlane 0).mem_nhds (show s ∈ halfPlane 0 from hs)] with z hz
    refine Complex.differentiableAt_Gamma z fun m hm => ?_
    have : (0 : ℝ) < z.re := hz
    rw [hm] at this
    simp at this
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  exact Complex.analyticAt_iff_eventually_differentiableAt.2 hd

lemma gc_analyticAt_sub_one (x : ℂ) : AnalyticAt ℂ (fun z : ℂ => z - 1) x :=
  analyticAt_id.sub analyticAt_const

lemma gc_analyticAt_Gamma_sub_one {x : ℂ} (hx : 1 < x.re) : AnalyticAt ℂ (fun z => Gamma (z - 1)) x := by
  have h : AnalyticAt ℂ Gamma ((fun z : ℂ => z - 1) x) := gc_analyticAt_Gamma (s := x - 1) (by simp; linarith)
  exact AnalyticAt.comp (f := fun z : ℂ => z - 1) (x := x) h (gc_analyticAt_sub_one x)

lemma gc_analyticAt_ecal_sub_one (x : ℂ) : AnalyticAt ℂ (fun z => ecal (z - 1)) x := by
  have h : AnalyticAt ℂ ecal ((fun z : ℂ => z - 1) x) := by
    rw [ecal_eq_e1]
    exact TIdentity.differentiable_e1.analyticAt _
  exact AnalyticAt.comp (f := fun z : ℂ => z - 1) (x := x) h (gc_analyticAt_sub_one x)

/-- `Mform F` is meromorphic at `x` (`Re x > 1`) when `F` is. -/
lemma gc_meromorphicAt_Mform {F : ℂ → ℂ} {x : ℂ} (hx : 1 < x.re) (hF : MeromorphicAt F x) :
    MeromorphicAt (Mform F) x := by
  have hG : AnalyticAt ℂ Gamma x := gc_analyticAt_Gamma (by linarith)
  have hG1 : AnalyticAt ℂ (fun z => Gamma (z - 1)) x := gc_analyticAt_Gamma_sub_one hx
  have hQ : MeromorphicAt (fun z => Qcont (z - 1)) x := by
    have h : MeromorphicAt Qcont ((fun z : ℂ => z - 1) x) := meromorphicAt_Qcont (a := x - 1) (by simp; linarith)
    exact MeromorphicAt.comp_analyticAt (g := fun z : ℂ => z - 1) (x := x) h (gc_analyticAt_sub_one x)
  have hE : AnalyticAt ℂ Ecal x := by
    rw [Ecal_eq_E2]
    exact TIdentity.differentiable_E2.analyticAt x
  have he : AnalyticAt ℂ (fun z => ecal (z - 1)) x := gc_analyticAt_ecal_sub_one x
  have hinv : MeromorphicAt (fun z : ℂ => 1 / (z - 2)) x :=
    (MeromorphicAt.const 1 x).div ((analyticAt_id.sub analyticAt_const).meromorphicAt)
  have h := ((((hG.meromorphicAt.mul hF).sub
    (((MeromorphicAt.const 2 x).mul hG1.meromorphicAt).mul hQ)).add hinv).sub hE.meromorphicAt).add
      ((MeromorphicAt.const 2 x).mul he.meromorphicAt)
  convert h using 1
  funext z
  simp only [Mform, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]

/-- The residue of `Mform F` at `x` (`Re x > 1`): `Γ(x)c_F - 2Γ(x - 1)c_Q + [x = 2]`. -/
lemma gc_hasResidue_Mform {F : ℂ → ℂ} {x cF cQ : ℂ} (hx : 1 < x.re) (hF : HasResidue F x cF)
    (hQ : HasResidue Qcont (x - 1) cQ) :
    HasResidue (Mform F) x (Gamma x * cF - 2 * Gamma (x - 1) * cQ + if x = 2 then 1 else 0) := by
  have hG : AnalyticAt ℂ Gamma x := gc_analyticAt_Gamma (by linarith)
  have hG1 : AnalyticAt ℂ (fun z => 2 * Gamma (z - 1)) x :=
    analyticAt_const.mul (gc_analyticAt_Gamma_sub_one hx)
  have h1 : HasResidue (fun z => F z * Gamma z) x (cF * Gamma x) :=
    hF.mul_continuousAt' hG.continuousAt
  have hQ' : HasResidue (fun z => Qcont (z - 1)) x cQ := by
    simpa using hQ.comp_sub_const 1
  have h2 : HasResidue (fun z => Qcont (z - 1) * (2 * Gamma (z - 1))) x (cQ * (2 * Gamma (x - 1))) :=
    hQ'.mul_continuousAt' hG1.continuousAt
  have h3 : HasResidue (fun z : ℂ => 1 / (z - 2)) x (if x = 2 then 1 else 0) := by
    split_ifs with hx2
    · subst hx2
      exact hasResidue_div_sub 2 1
    · refine hasResidue_zero_of_analyticAt ?_
      exact analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.2 hx2)
  have hE0 : AnalyticAt ℂ Ecal x := by
    rw [Ecal_eq_E2]
    exact TIdentity.differentiable_E2.analyticAt x
  have hE : AnalyticAt ℂ (fun z => -Ecal z + 2 * ecal (z - 1)) x :=
    hE0.neg.add (analyticAt_const.mul (gc_analyticAt_ecal_sub_one x))
  have h := ((h1.sub h2).add h3).add_analyticAt hE
  convert h using 1
  · funext z
    simp only [Mform, Pi.add_apply]
    ring
  · ring

/-- A meromorphic function with residue `0` has order `≥ 0`. -/
lemma gc_order_nonneg_of_hasResidue_zero {f : ℂ → ℂ} {a : ℂ} (hm : MeromorphicAt f a)
    (hf : HasResidue f a 0) : 0 ≤ meromorphicOrderAt f a := by
  have hsub : MeromorphicAt (fun s : ℂ => s - a) a := (analyticAt_id.sub analyticAt_const).meromorphicAt
  have hprod : MeromorphicAt ((fun s : ℂ => s - a) * f) a := hsub.mul hm
  have h0 : 0 ≤ meromorphicOrderAt ((fun s : ℂ => s - a) * f) a :=
    (tendsto_nhds_iff_meromorphicOrderAt_nonneg hprod).1 ⟨0, hf⟩
  have hne : meromorphicOrderAt ((fun s : ℂ => s - a) * f) a ≠ 0 := by
    intro h
    obtain ⟨c, hc, hlim⟩ := (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero hprod).2 h
    exact hc (tendsto_nhds_unique hlim hf)
  rw [meromorphicOrderAt_mul hsub hm, meromorphicOrderAt_id_sub_const] at h0 hne
  cases ho : meromorphicOrderAt f a with
  | top => exact le_top
  | coe n =>
    rw [ho] at h0 hne
    have h1 : (0 : ℤ) ≤ 1 + n := by exact_mod_cast h0
    have h2 : (1 : ℤ) + n ≠ 0 := by
      intro h
      apply hne
      exact_mod_cast h
    exact_mod_cast (by omega : (0 : ℤ) ≤ n)

/-- Order `≥ 0` gives residue `0`. -/
lemma gc_hasResidue_zero_of_order_nonneg {f : ℂ → ℂ} {a : ℂ} (hm : MeromorphicAt f a)
    (h : 0 ≤ meromorphicOrderAt f a) : HasResidue f a 0 := by
  obtain ⟨L, hL⟩ := (tendsto_nhds_iff_meromorphicOrderAt_nonneg hm).2 h
  exact hasResidue_zero_of_tendsto hL

/-- The real points of `Σ_Q` in `(0, 1)` are the `1/k`, `k ≥ 2` squarefree. -/
lemma gc_real_mem_poleSetQ {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) (hmem : (y : ℂ) ∈ PoleSetQ) :
    ∃ k : ℕ, 2 ≤ k ∧ Squarefree k ∧ (y : ℂ) = 1 / (k : ℂ) := by
  rcases hmem with (h1 | ⟨k, hk, hsq, hyk⟩) | ⟨n, hn, -, ρ, hρ, hyρ⟩
  · have : (y : ℂ) = 1 := h1
    have := congrArg Complex.re this
    simp at this
    linarith [hy.2]
  · exact ⟨k, hk, hsq, hyk⟩
  · exfalso
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    have hρeq : ρ = ((n * y : ℝ) : ℂ) := by
      rw [eq_div_iff hn0] at hyρ
      push_cast
      rw [← hyρ]
      ring
    have hz := hρ.1
    have hre1 := hρ.2.1
    have hre2 := hρ.2.2
    rw [hρeq] at hz hre1 hre2
    simp only [ofReal_re] at hre1 hre2
    exact riemannZeta_ne_zero_of_mem_Ioo ⟨hre1, hre2⟩ hz

/-- At a real `y ∈ (0, 1)` that is no `1/k` (`k ≥ 2` squarefree), `Qcont` is analytic, so has residue `0`. -/
lemma gc_hasResidue_Qcont_real {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1)
    (hk : ∀ k : ℕ, 2 ≤ k → Squarefree k → (y : ℂ) ≠ 1 / (k : ℂ)) : HasResidue Qcont y 0 := by
  have hnot : (y : ℂ) ∉ PoleSetQ := by
    intro hmem
    obtain ⟨k, hk2, hsq, hyk⟩ := gc_real_mem_poleSetQ hy hmem
    exact hk k hk2 hsq hyk
  refine hasResidue_zero_of_analyticAt (isQCont_Qcont.2.2 _ ⟨?_, hnot⟩)
  show (0 : ℝ) < (y : ℂ).re
  simpa using hy.1

/-- `Γ(1 + u) · (2R/u) - 2Γ(u)R = 0` for `u ≠ 0`: the cancellation at `1 + u`. -/
lemma gc_cancel {u R : ℂ} (hu : u ≠ 0) : Gamma (1 + u) * (2 * R / u) - 2 * Gamma u * R = 0 := by
  rw [add_comm, Complex.Gamma_add_one u hu]
  field_simp
  ring
