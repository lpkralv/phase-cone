import GoldbachBoundaries.Paper2.M4a.Defs
import GoldbachBoundaries.Paper2.M4a.Fill.sub_one_mem_poleSetQ_of_mem_pinch
import GoldbachBoundaries.Paper2.M4a.Fill.pinchPairs_one_add
import GoldbachBoundaries.Paper2.M4a.Fill.catalogueL_locallyFinite
import GoldbachBoundaries.Paper2.M4a.Fill.infinite_scaledZeros_near
import GoldbachBoundaries.Paper2.M4a.Fill.infinite_pinches_of_infinite

/-!
# M4a: the catalogue `𝒞_L` (`cl:prop:catalogue`)

**(i)** Under RH every point of `Σ ∖ {1}` has real part at most `1/2` (paper 1's `lem_Sigma_iv`), so a sum `a' + b'`
of two points of `Σ` with real part above `1` has `a' = 1` or `b' = 1`. Hence `L(s) ∈ Σ + Σ` with `Re L(s) > 1` iff
`L(s) - 1 ∈ Σ` iff `L(s) ∈ 𝒞` (paper 1's `catalogue_eq_image`), and the pairs at `1 + b` are `(1, b)`, `(b, 1)`.
Local finiteness is that of `Σ` in `Re z > 0` (`lem_Sigma_iv`), pulled back through `s ↦ L(s) - 1`.

**(ii)** Paper 1's `lem_density` (no (Z2), review choice 9) gives the pairs (prime `n`, zero `ρ`) with
`|ρ/n - iy| < ε`; under RH distinct pairs give distinct points `ρ/n` (paper 1's `catalogue_zero_inj`), and the affine
bijection `L` carries them into the disc.

The targets `prop_catalogue_i_proof`, `prop_catalogue_ii_proof` are at the end of the file (`Jseg.lean` and
`H3.lean` use them).
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M4a

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-! ## Lemmas

Proved in `Fill/`, one file per lemma (same name, same statement): `sub_one_mem_poleSetQ_of_mem_pinch`, `pinchPairs_one_add`, `catalogueL_locallyFinite`, `infinite_scaledZeros_near`, `infinite_pinches_of_infinite`. -/

/-! ## Targets -/

/-- `prop_catalogue_i` of `Paper2/Statements.lean`, statement verbatim. -/
theorem prop_catalogue_i_proof (hRH : RiemannHypothesis) (A : Aff) :
    catalogueL A = {s | s ∈ A.HL ∧ A.app s ∈ catalogue} ∧
    (∀ α ∈ catalogueL A, ∀ b ∈ PoleSetQ, A.app α = 1 + b → pinchPairs (A.app α) = {(1, b), (b, 1)}) ∧
    (∀ α ∈ catalogueL A, ∀ α' ∈ catalogueL A, A.app α - 1 = A.app α' - 1 → α = α') ∧
    ∀ z ∈ A.HL, ∃ U ∈ 𝓝 z, (U ∩ catalogueL A).Finite := by
  refine ⟨?_, fun α _ b hb h => h ▸ pinchPairs_one_add hRH hb, fun α _ α' _ h =>
    app_injective A (sub_left_inj.mp h), catalogueL_locallyFinite hRH A⟩
  ext s
  simp only [catalogueL, mem_ofPred_eq, catalogue_eq_image, mem_image]
  constructor
  · rintro ⟨hH, hP⟩
    exact ⟨hH, A.app s - 1, sub_one_mem_poleSetQ_of_mem_pinch hRH hP hH, by ring⟩
  · rintro ⟨hH, b, hb, hbs⟩
    exact ⟨hH, 1, one_mem_poleSetQ, b, hb, hbs.symm⟩

/-- `prop_catalogue_ii` of `Paper2/Statements.lean`, statement verbatim. -/
theorem prop_catalogue_ii_proof (hRH : RiemannHypothesis) (A : Aff) :
    ∀ s₀ ∈ A.lineL, ∀ r : ℝ, 0 < r →
      {α | ∃ ρ ∈ NontrivialZeros, ∃ n : ℕ, n.Prime ∧ A.app α = 1 + ρ / (n : ℂ) ∧ α ∈ ball s₀ r}.Infinite ∧
      (0 ≤ s₀.im → {α | ∃ ρ ∈ NontrivialZeros, 0 < ρ.im ∧ ∃ n : ℕ, n.Prime ∧
        A.app α = 1 + ρ / (n : ℂ) ∧ α ∈ ball s₀ r}.Infinite) := by
  intro s₀ hs₀ r hr
  have hεr : 0 < A.ell * r := mul_pos A.ell_pos hr
  obtain ⟨h1, h2⟩ := infinite_scaledZeros_near hRH (A.app s₀).im hεr
  refine ⟨(infinite_pinches_of_infinite A hs₀ hr h1).mono ?_, fun him => ?_⟩
  · rintro α ⟨⟨ρ, hρ, n, hn, h⟩, hb⟩
    exact ⟨ρ, hρ, n, hn, by rw [← h]; ring, hb⟩
  · have hy : 0 ≤ (A.app s₀).im := by rw [app_im]; exact mul_nonneg A.ell_pos.le him
    refine (infinite_pinches_of_infinite A hs₀ hr (h2 hy)).mono ?_
    rintro α ⟨⟨ρ, hρ, hγ, n, hn, h⟩, hb⟩
    exact ⟨ρ, hρ, hγ, n, hn, by rw [← h]; ring, hb⟩

end GoldbachBoundaries.Paper2.M4a
