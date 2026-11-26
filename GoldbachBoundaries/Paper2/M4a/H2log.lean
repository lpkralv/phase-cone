import GoldbachBoundaries.Paper2.M4a.Jseg
import GoldbachBoundaries.Paper2.M4a.Fill.hasDerivAt_Jseg_of_H2b
import GoldbachBoundaries.Paper2.M4a.Fill.meromorphicOn_H2b_rhs

/-!
# M4a: the two sufficient conditions for (H2-log)

**(H2a).** (H2a) contains (K1) (`D_L ⊆ ℍ_L`), so `lem_J_i` makes `J_{ab}` holomorphic on the open `ℍ_L`; its
derivative is holomorphic there (`DifferentiableOn.deriv`), hence meromorphic, and it is `J'_{ab}` on `D_L` by
definition. Real proof, no sorry lemma.

**(H2b).** `k(z, s) = g(z - θs)`. (K1) makes `g` holomorphic at `z - θs` for `(z, s)` in the (K1) domain, in
particular along the segment `[a, L(s) - b]` for `s ∈ D_L`. Differentiating `J_{ab}(s) = Δ(s) ∫_0^1 g(φ(t, s)) dt`
(`Δ(s) = L(s) - a - b`, `φ(t, s) = a + tΔ(s) - θs`) under the integral and integrating by parts in `t`:
`J'(s) = ℓ∫_0^1 [g(φ) + tΔ g'(φ)] dt - θΔ∫_0^1 g'(φ) dt = ℓ[t g(φ)]_0^1 - θ[g(φ)]_0^1
= (ℓ - θ) g(L(s) - b - θs) + θ g(a - θs)`.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M4a

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-! ## Lemmas

Proved in `Fill/`, one file per lemma (same name, same statement): `hasDerivAt_Jseg_of_H2b`, `meromorphicOn_H2b_rhs`. -/

/-! ## Targets -/

/-- `H2log_of_H2a` of `Paper2/Statements.lean`, statement verbatim. -/
theorem H2log_of_H2a_proof (A : Aff) (k : ℂ → ℂ → ℂ) (hH2a : H2a A k) : H2log A k := by
  have hK1 : K1 A k := hH2a.mono fun p hp => ⟨hp.1.1, hp.2⟩
  intro a ha b hb
  have hd := ((lem_J_i_proof A k hK1 ha hb).2.2.1 hH2a).2
  exact ⟨deriv (Jseg A k a b), ((hd.deriv (isOpen_HL A)).analyticOnNhd (isOpen_HL A)).meromorphicOn,
    fun _ _ => rfl⟩

/-- `H2log_of_H2b` of `Paper2/Statements.lean`, statement verbatim. -/
theorem H2log_of_H2b_proof (A : Aff) (k : ℂ → ℂ → ℂ) (hK1 : K1 A k) {g : ℂ → ℂ} {θ : ℝ}
    (hg : MeromorphicOn g univ) (hk : ∀ z s, k z s = g (z - θ * s)) :
    (∀ a ∈ PoleSetQ, ∀ b ∈ PoleSetQ, ∀ s ∈ A.DL,
      HasDerivAt (Jseg A k a b) (((A.ell : ℂ) - θ) * g (A.app s - b - θ * s) + θ * g (a - θ * s)) s) ∧
    (∀ a b : ℂ, MeromorphicOn (fun s => ((A.ell : ℂ) - θ) * g (A.app s - b - θ * s) + θ * g (a - θ * s)) univ) ∧
    H2log A k := by
  refine ⟨fun a ha b hb s hs => hasDerivAt_Jseg_of_H2b A k hK1 hk ha hb hs,
    fun a b => meromorphicOn_H2b_rhs A hg a b, fun a ha b hb => ?_⟩
  exact ⟨_, (meromorphicOn_H2b_rhs A hg a b).mono_set (subset_univ _),
    fun s hs => (hasDerivAt_Jseg_of_H2b A k hK1 hk ha hb hs).deriv.symm⟩

end GoldbachBoundaries.Paper2.M4a
