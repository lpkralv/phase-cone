import GoldbachBoundaries.Paper2.M1.Skeleton

/-!
# Paper 2, Milestone M4a (the kernel class, Section 4): definitions and small facts

Everything in this file has a real proof. The one new definition is `lineCoeff`, the Taylor coefficients of a
function of two variables in the first variable along a complex line `z = c₀ + c₁ s` (used for (K4), `Restrict.lean`).
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M4a

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- `lineCoeff u c₀ c₁ j s = ∂ᶻʲ u(z, s)` at `z = c₀ + c₁ s`: the `j`-th derivative in the first variable of a
function on `ℂ × ℂ`, along the complex line `{(c₀ + c₁ s, s)}`. (Up to `j!`, the Taylor coefficients of
`z ↦ u(z, s)` at the point of the line.) -/
def lineCoeff (u : ℂ × ℂ → ℂ) (c₀ c₁ : ℂ) (j : ℕ) (s : ℂ) : ℂ :=
  iteratedDeriv j (fun z => u (z, s)) (c₀ + c₁ * s)

/-! ## The affine map and its regions -/

lemma continuous_app_re (A : Aff) : Continuous fun s => (A.app s).re := by
  unfold Aff.app; fun_prop

lemma isOpen_HL (A : Aff) : IsOpen A.HL :=
  isOpen_lt continuous_const (continuous_app_re A)

lemma isOpen_DL (A : Aff) : IsOpen A.DL :=
  (isOpen_lt continuous_const (continuous_app_re A)).inter (isOpen_lt (continuous_app_re A) continuous_const)

lemma DL_subset_HL (A : Aff) : A.DL ⊆ A.HL := fun _ hs => hs.1

lemma app_re (A : Aff) (s : ℂ) : (A.app s).re = A.ell * s.re + A.ell0 := by
  simp [Aff.app]

lemma app_im (A : Aff) (s : ℂ) : (A.app s).im = A.ell * s.im := by
  simp [Aff.app]

lemma app_injective (A : Aff) : Function.Injective A.app := by
  intro s s' h
  have hl : (A.ell : ℂ) ≠ 0 := by exact_mod_cast A.ell_pos.ne'
  simp only [Aff.app, add_left_inj] at h
  exact mul_left_cancel₀ hl h

lemma app_idL (s : ℂ) : Aff.idL.app s = s := by simp [Aff.app, Aff.idL]

lemma one_mem_poleSetQ : (1 : ℂ) ∈ PoleSetQ := Or.inl (Or.inl rfl)

lemma kr_one' : kr 1 = k0 := by
  funext z s; simp [kr, k0]; ring

/-- `X_α` at a pinch `α` with `L(α) - 1 = b ≠ 1`, unfolded. -/
lemma Xcoef_of_ne (A : Aff) (k : ℂ → ℂ → ℂ) {α : ℂ} (h : A.app α - 1 ≠ 1) :
    Xcoef A k α = fun s =>
      cP 1 * cP (A.app α - 1) * (Jseg A k 1 (A.app α - 1) s + Jseg A k (A.app α - 1) 1 s) := by
  funext s; simp [Xcoef, h]

/-- `X_α` at a pinch `α` with `L(α) - 1 = 1`, unfolded. -/
lemma Xcoef_of_eq (A : Aff) (k : ℂ → ℂ → ℂ) {α : ℂ} (h : A.app α - 1 = 1) :
    Xcoef A k α = Jseg A k 1 1 := by
  funext s; simp [Xcoef, h]

/-- A function with a non-zero derivative at `x` is not identically zero near `x`. -/
lemma exists_ne_zero_of_hasDerivAt {f : ℂ → ℂ} {f' x : ℂ} (hf : HasDerivAt f f' x) (hf' : f' ≠ 0)
    {U : Set ℂ} (hU : U ∈ 𝓝 x) : ∃ s ∈ U, f s ≠ 0 := by
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  have h0 : f =ᶠ[𝓝 x] fun _ => (0 : ℂ) := Filter.mem_of_superset hU h
  exact hf' (hf.unique ((hasDerivAt_const x (0 : ℂ)).congr_of_eventuallyEq h0))

end GoldbachBoundaries.Paper2.M4a
