import GoldbachBoundaries.Paper2.M5.FilterIV

/-!
# M5 skeleton: the targets of Milestone M5 (`cl:lem:Qleft`, Theorem G, Theorem F)

Each `*_proof` theorem has the statement of the theorem of the same name (without `_proof`) in
`Paper2/Statements.lean`, copied verbatim, and a real proof from the M5 lemmas (and M1-M4b, paper 1); no target has a
`sorry` of its own. A target that a later file uses is proved at the end of its own file, in the dependency order
`Defs → General → Qleft → TkLine → TkStep → Tk → FilterI → FilterII → FilterIII → FilterIV → Skeleton`:

| Target | File |
|---|---|
| `lem_Qleft_proof` | `Qleft.lean` |
| `thm_Tk_proof`, `thm_Tk_poles_proof` | `Tk.lean` |
| `thm_filter_i_proof` | `FilterI.lean` |
| `thm_filter_ii_proof` | `FilterII.lean` |
| `thm_filter_iii_proof` | `FilterIII.lean` |
| `thm_filter_iv_proof` | `FilterIV.lean` |
| `intro_thm_F_proof` | here |

The type match is checked by `example : type_of% @GoldbachBoundaries.Paper2.X := @GoldbachBoundaries.Paper2.M5.X_proof`
from a scratch file that imports both (this file does not import `Paper2/Statements.lean`). Once every M5 lemma is
filled, each of the 7 statements closes by `exact M5.X_proof ...`, and `intro_thm_F` (already proved from
`thm_filter_i` to `thm_filter_iv` in `Paper2/Statements.lean`) becomes sorry-free with them; `intro_thm_F_proof` below is
the same assembly, checked against the statement.

**Changes of proof (statements unchanged).**
1. **Theorem G by an explicit induction package** (`TkPack`, `Defs.lean`): a concrete continuation `F` of `T_k` and a
   concrete `H_k`, with (i)-(iv) in pointwise form, and an explicit step (`TkStep`, `HkStep`) glued from the three
   regions of the paper's proof. (ii) for every meromorphic continuation follows by the identity theorem
   (`eventuallyEq_of_tkPack`).
2. **The absolute convergence of `T_k` on `σ > k`** is proved along the induction, from the Fubini step of the iterated
   Mellin–Barnes identity (`Tk_succ_eq_verticalIntegral'`); the paper asserts it ("converge for `k - 1 < c < σ - 1`").
3. **Theorem F(i) without removable singularities**: the integrand is written as `K_s(z)G(z, s-z)A(z)A(s-z)` with
   `A = (z - 1)Q` given its value at `1` (`gA`), so the lines `Re z = σ/2` work for every `σ > 1` and no line has to avoid
   `z = 1` or `z = s - 1`.
4. **Theorem F(ii)'s residue theorem with infinitely many poles** is done on rectangles of the good heights of
   `cl:lem:Qleft`(ii), with a rectangle residue theorem that asks holomorphy on the rectangle only
   (`rectangleIntegral'_eq_sum_of_simplePoles_rect`; M1's version asks it on the whole strip, which fails here).
5. **No (Z6) in Theorem F**: Step 2's Stirling bounds are replaced by M1's polynomial decay of `K_s(ρ)` (the majorant only
   has to beat polynomial factors). (Z6) is used in Theorem G, through `cl:lem:kernelt`, for the growth in `Im s`.
6. **Under RH, paper 1's bounds on `Q`** (`norm_Qcont_le_log`, `analyticAt_Qcont_of_RH`) wherever the paper cites
   `nr:lem:growthQ`: Theorem G uses none of (Z1)-(Z3), and Theorem F(i) none either. (Z1)-(Z3) enter Theorem F through
   `cl:lem:Qleft` and the zero counts of Step 2.
7. **Littlewood's theorem** is the premise `ZLittlewood` of `thm_filter_iii` (and of the (iii) part of `intro_thm_F`),
   used only in `exists_ordinate_in_interval`.

Unused premises are consumed by `have _ := ...` with a comment, as in M1–M4b.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- `intro_thm_F` of `Paper2/Statements.lean`, statement verbatim (the assembly of `Statements.lean`, with the M5
targets). -/
theorem intro_thm_F_proof (hRH : RiemannHypothesis) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3) (hZ6 : Z6)
    (H : MvPolynomial (Fin 2) ℂ) (hH0 : H ≠ 0) (hHs : ∀ z w, evalH H z w = evalH H w z)
    (hH1 : ∀ w, evalH H 1 w = 0) :
    (∃ F : ℂ → ℂ, DifferentiableOn ℂ F HH ∧ EqOn F (DH H) (halfPlane 2)) ∧
    (∀ τ₀ : ℝ, τ₀ ≠ 0 → (∀ ρ ∈ NontrivialZeros, ρ.im ≠ τ₀) →
      ∀ F : ℂ → ℂ, DifferentiableOn ℂ F HH → EqOn F (DH H) (halfPlane 2) →
        Summable (CHterm H τ₀) ∧
          Tendsto (fun η : ℝ => (η : ℂ) * F (1 + τ₀ * I + η)) (𝓝[>] 0) (𝓝 (CH H τ₀))) ∧
    (ZLittlewood → HypF →
      (∀ F : ℂ → ℂ, DifferentiableOn ℂ F HH → EqOn F (DH H) (halfPlane 2) →
        IsNaturalBoundary F HH lineOne) ∧
      ∀ F : ℂ → ℂ, DifferentiableOn ℂ F HH → EqOn F T0 (halfPlane 2) →
        IsNaturalBoundary F HH lineOne) ∧
    (Summable lambda0Term ∧
      ∀ F : ℂ → ℂ, DifferentiableOn ℂ F HH → EqOn F T0 (halfPlane 2) →
        Tendsto (fun η : ℝ => (η : ℂ) * F (1 + η)) (𝓝[>] 0) (𝓝 (Lambda0 : ℂ)) ∧
        (∀ r : ℝ, 0 < r → ¬ ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball 1 r) ∧ EqOn g F (ball 1 r ∩ HH)) ∧
        ∀ r : ℝ, 0 < r → ∀ f : ℂ → ℂ, MeromorphicOn f (ball 1 r) →
          f =ᶠ[codiscreteWithin (ball 1 r ∩ HH)] F →
          meromorphicOrderAt f 1 = -1 ∧ HasResidue f 1 (Lambda0 : ℂ)) :=
  ⟨thm_filter_i_proof hRH hZ1 hZ2 hZ3 hZ6 H hH0 hHs hH1,
    fun _ hτ0 hτ F hF hFD => thm_filter_ii_proof hRH hZ1 hZ2 hZ3 hZ6 H hH0 hHs hH1 hτ0 hτ F hF hFD,
    fun hL hF => thm_filter_iii_proof hRH hZ1 hZ2 hZ3 hZ6 hL hF H hH0 hHs hH1,
    thm_filter_iv_proof hRH hZ1 hZ2 hZ3 hZ6⟩

end GoldbachBoundaries.Paper2.M5
