import GoldbachBoundaries.BoundaryLemma
import GoldbachBoundaries.TIdentity.Assembly

/-!
Paper 1, `thm:T-boundary`: under RH, the line `σ = 1` is a natural boundary of `T`. The proof
here takes the density statement (for every `y` and `ε > 0` there are infinitely many pairs
`(p, ρ)`, `p` prime, `ρ` a non-trivial zero, with `|ρ/p - iy| < ε`) as the hypothesis `hdens`.

Route:
1. `cor_T_poles_proof` gives a continuation `F₀` of `T`, meromorphic on `ℍ`, with a simple pole
   (order `-1`) at every catalogue point. Any `F` meromorphic on `ℍ` and equal to `T` off a
   discrete subset of `σ > 2` agrees with `F₀` on a punctured neighbourhood of every point of `ℍ`
   (`F - F₀` has order `⊤` at `3`, hence at every point of the connected set `ℍ`), so it has the
   same orders there (`meromorphicOrderAt_eq_of_eqOn_halfPlane_two`).
2. For `z₀ = 1 + iy` and `ε > 0`, `hdens` gives a prime `p` and a non-trivial zero `ρ` with
   `|ρ/p - iy| < ε`; then `a = 1 + ρ/p` is a catalogue point (primes are squarefree), lies in `ℍ`
   (`Re ρ > 0`), differs from `z₀` (`Re a > 1`), and lies in `Δ(z₀, ε)`.
3. `noMeromorphicExtensionAt_of_poles_in_every_ball` with `U = ℍ`.

RH enters only through `cor_T_poles_proof`.
-/

noncomputable section

open Complex Filter Topology Set Metric

namespace GoldbachBoundaries

/-- The half-plane `{Re s > a}` is preconnected (it is convex). -/
lemma isPreconnected_halfPlane (a : ℝ) : IsPreconnected (halfPlane a) :=
  (convex_halfSpace_re_gt a).isPreconnected

/-- Identity theorem for meromorphic functions on `ℍ`: if `F` and `F₀` are meromorphic on `ℍ`,
`F₀ = T` on `σ > 2`, and `F = T` off a discrete subset of `σ > 2`, then `F = F₀` on a punctured
neighbourhood of every point of `ℍ`. -/
lemma eventuallyEq_nhdsNE_of_agree_halfPlane_two {F F₀ : ℂ → ℂ} (hF : MeromorphicOn F HH)
    (hF₀ : MeromorphicOn F₀ HH) (hF₀T : EqOn F₀ T (halfPlane 2))
    (hFT : F =ᶠ[codiscreteWithin (halfPlane 2)] T) {a : ℂ} (ha : a ∈ HH) :
    F =ᶠ[𝓝[≠] a] F₀ := by
  have h3 : (3 : ℂ) ∈ halfPlane 2 := by norm_num [halfPlane]
  have h3H : (3 : ℂ) ∈ HH := by norm_num [halfPlane]
  have hn3 : halfPlane 2 ∈ 𝓝 (3 : ℂ) := (isOpen_halfPlane 2).mem_nhds h3
  have hFT3 : F =ᶠ[𝓝[≠] (3 : ℂ)] T :=
    eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin hFT hn3
  have hF₀T3 : F₀ =ᶠ[𝓝[≠] (3 : ℂ)] T :=
    Filter.mem_of_superset (nhdsWithin_le_nhds hn3) fun s hs => hF₀T hs
  have htop3 : meromorphicOrderAt (F - F₀) 3 = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    filter_upwards [hFT3, hF₀T3] with s h1 h2
    simp [h1, h2]
  have htop : meromorphicOrderAt (F - F₀) a = ⊤ :=
    (hF.sub hF₀).meromorphicOrderAt_eq_top_of_isPreconnected (isPreconnected_halfPlane 1) h3H ha
      htop3
  rw [meromorphicOrderAt_eq_top_iff] at htop
  filter_upwards [htop] with s hs
  exact sub_eq_zero.mp hs

/-- **`thm:T-boundary`, density lemma as hypothesis.** Under RH, and given the density of the
points `ρ/p` (`p` prime, `ρ` a non-trivial zero) in the imaginary axis in the form `hdens`, the
line `σ = 1` is a natural boundary of every meromorphic continuation `F` of `T` to `ℍ`. -/
theorem thm_T_boundary_of_density (hRH : RiemannHypothesis)
    (hdens : ∀ (y : ℝ) {ε : ℝ}, 0 < ε →
      {np : ℕ × ℂ | np.1.Prime ∧ np.2 ∈ NontrivialZeros ∧
        ‖np.2 / (np.1 : ℂ) - (y : ℂ) * I‖ < ε}.Infinite)
    (F : ℂ → ℂ) (hF : MeromorphicOn F HH)
    (hFT : F =ᶠ[codiscreteWithin (halfPlane 2)] T) :
    IsNaturalBoundary F HH lineOne := by
  obtain ⟨F₀, hF₀, hF₀T, -, hord, -⟩ := cor_T_poles_proof hRH
  intro z₀ hz₀
  have hz₀re : z₀.re = 1 := hz₀
  refine noMeromorphicExtensionAt_of_poles_in_every_ball (isOpen_halfPlane 1) ?_
  intro ε hε
  obtain ⟨⟨n, ρ⟩, hn, hρ, hdist⟩ := (hdens z₀.im hε).nonempty
  simp only at hn hρ hdist
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn.pos
  set a : ℂ := 1 + ρ / (n : ℂ) with ha_def
  have hare : a.re = 1 + ρ.re / n := by
    simp [ha_def, Complex.div_re, Complex.natCast_re, Complex.natCast_im, Complex.normSq_natCast]
    field_simp
  have hgt : 1 < a.re := by
    rw [hare]; have := div_pos hρ.2.1 hnpos; linarith
  have haC : a ∈ catalogue :=
    Or.inr ⟨n, hn.one_lt.le, hn.squarefree, ρ, hρ, rfl⟩
  have haH : a ∈ HH := hgt
  refine ⟨a, haH, ?_, ?_, ?_⟩
  · intro h; rw [h, hz₀re] at hgt; exact lt_irrefl _ hgt
  · rw [mem_ball, dist_eq_norm]
    have : a - z₀ = ρ / (n : ℂ) - (z₀.im : ℂ) * I := by
      have hz := (Complex.re_add_im z₀).symm
      rw [hz₀re] at hz
      rw [ha_def]; conv_lhs => rw [hz]
      push_cast; ring
    rw [this]; exact hdist
  · rw [meromorphicOrderAt_congr (eventuallyEq_nhdsNE_of_agree_halfPlane_two hF hF₀ hF₀T hFT haH),
      hord a haC]
    decide

end GoldbachBoundaries
