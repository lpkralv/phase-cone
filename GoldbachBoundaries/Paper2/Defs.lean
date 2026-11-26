import GoldbachBoundaries.Defs

/-!
# Definitions for paper 2 (T without RH, and natural boundaries of a class of double prime series)

Paper 1's definitions are reused, not redefined: `P`, `Q`, `G`, `T`, `NontrivialZeros`, `zetaMult`, `mu`,
`PoleSetQ` (the paper's `Σ_Q`, which is the same set as paper 1's `Σ`), `catalogue`, `HasCatalogueValues`,
`HasResidue`, `halfPlane`, `HH`, `lineOne`, `IsContinuationAlong`, `ContinuesAlong`, `IsTerminalGerm`,
`NoMeromorphicExtensionAt`, `IsNaturalBoundary`, `GermExtendsMeromorphically`. No paper 1 definition is changed.
Paper 1's `IsAdmissibleGerm` is specific to `G`, `ℍ ∖ 𝒞` and `σ > 2`; paper 2 needs the same notion for other
series, regions and start sets, so `IsAdmissibleGermOn` below generalises it (paper 1's is the instance
`IsAdmissibleGermOn G (HH \ catalogue) (halfPlane 2)`).

## Junk-value discipline (as in paper 1)

`tsum`, `∑ᶠ`, `Set.ncard`, Bochner integrals and `sSup`/`iInf` all return junk (`0`) when the sum, set or
integral is not summable, finite, integrable or bounded. Every definition below is used only where the object is
genuine, and every statement that relies on a count or a sum being finite says so (`Set.Finite`, `Summable`,
`Integrable`), so that a junk `0` can never make a statement true. Continuations are quantified functions that
agree with the series on a half-plane of convergence; residues are `HasResidue` (punctured neighbourhood);
boundaries compare functions off a discrete set. A pointwise formula is asserted only at points where every
function in it is analytic.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2

open GoldbachBoundaries

/-! ## 1. Zeros, the residues `R_a` of `Q`, the pinch set (Section 2 of the paper) -/

/-- `ord_w ζ` of eq. `(nr:eq:Ra)`: `m(w)` if `w` is a non-trivial zero, `-1` at `w = 1`, `0` otherwise. -/
def ordZeta (w : ℂ) : ℤ := by
  classical exact if w = 1 then -1 else if w ∈ NontrivialZeros then (zetaMult w : ℤ) else 0

/-- `R_a = -∑_{k ≥ 1} μ(k)/k · ord_{ka} ζ` (eq. `(nr:eq:Ra)`). The index is `k + 1`, `k : ℕ`. For
`Re a > 0` only finitely many terms are non-zero (the paper's remark after the display), so the `tsum` is a
finite sum there. Used only for `a ∈ Σ_Q`. -/
def Rcoef (a : ℂ) : ℂ :=
  -∑' k : ℕ, mu (k + 1) / ((k + 1 : ℕ) : ℂ) * (ordZeta (((k + 1 : ℕ) : ℂ) * a) : ℂ)

/-- `c_a = -R_a`, the coefficient of `log(z - a)` in `P` near `a` (Section 4). -/
def cP (a : ℂ) : ℂ := -Rcoef a

/-- `Σ_Q^* = {a ∈ Σ_Q : R_a ≠ 0}`, the poles of `Q` (Lemma `nr:lem:Q`). -/
def SigmaQStar : Set ℂ := {a | a ∈ PoleSetQ ∧ Rcoef a ≠ 0}

/-- The pinch set `Π = Σ_Q + Σ_Q`. -/
def Pinch : Set ℂ := {s | ∃ a ∈ PoleSetQ, ∃ b ∈ PoleSetQ, s = a + b}

/-- The ordered pairs `(a, b) ∈ Σ_Q²` with `a + b = s₀`. As a set of ordered pairs, `(a, a)` occurs once,
which is the paper's "the pair `(a,a)`, if present, counted once". -/
def pinchPairs (s₀ : ℂ) : Set (ℂ × ℂ) := {p | p.1 ∈ PoleSetQ ∧ p.2 ∈ PoleSetQ ∧ p.1 + p.2 = s₀}

/-- `B(a, b) = Γ(a)Γ(b)/Γ(a + b)`. -/
def betaB (a b : ℂ) : ℂ := Gamma a * Gamma b / Gamma (a + b)

/-- The pair sum `𝓡(s₀) = ∑_{(a,b) ∈ Σ_Q², a+b = s₀} R_a R_b B(a,b)` (eq. `(nr:eq:residue)`,
`(nr:eq:Lambda)`). A `tsum` over the subtype of pairs: when the set of pairs is finite it is the finite sum;
`𝓡(s₀) ≠ 0` implies summability (a non-summable `tsum` is `0`). -/
def pairSum (s₀ : ℂ) : ℂ :=
  ∑' p : pinchPairs s₀, Rcoef p.1.1 * Rcoef p.1.2 * betaB p.1.1 p.1.2

/-- The Mellin–Barnes kernel `K_s(w) = Γ(w)Γ(s - w)/Γ(s)`. -/
def KerS (s w : ℂ) : ℂ := Gamma w * Gamma (s - w) / Gamma s

/-- The Iverson bracket `[A]` as a complex number. -/
def iverson (A : Prop) : ℂ := by classical exact if A then 1 else 0

/-! ## 2. The numbers `B`, `B_∞`, the hypothesis `(H_∞)`, the sets `F_δ` (Section 3) -/

/-- `B = sup_ρ β`. (`NontrivialZeros` is infinite and its real parts lie in `(0,1)`, so this is a genuine
supremum.) -/
def Bsup : ℝ := sSup (re '' NontrivialZeros)

/-- `B_∞ = lim_{t→∞} sup{β : |γ| ≥ t}`. The sup is non-increasing in `t`, so the limit is the infimum over
`t`; each sup is in `[0, 1]` (junk `sSup ∅ = 0` cannot occur, since there are zeros of every height), so the
infimum is over a set bounded below by `0`. -/
def Binf : ℝ := ⨅ t : ℝ, sSup (re '' {ρ | ρ ∈ NontrivialZeros ∧ t ≤ |ρ.im|})



def Hinf : Prop := ∀ δ : ℝ, 0 < δ → {ρ | ρ ∈ NontrivialZeros ∧ 1 / 2 + δ < ρ.re}.Finite

/-- The property of `T` in `nr:prop:dichotomy`(i): "`T` is meromorphic on `ℍ` with `σ = 1` as a natural boundary in
the sense of Theorem `nr:thm:boundary`". Some meromorphic `F` on `ℍ` equals the series on `σ > 2`, and every such `F`
(agreeing with the series off a discrete subset of `σ > 2`) has `σ = 1` as a natural boundary, in the form of
`thm_boundary`. -/
def TBoundaryOnHH : Prop :=
  (∃ F : ℂ → ℂ, MeromorphicOn F HH ∧ EqOn F T (halfPlane 2)) ∧
    ∀ F : ℂ → ℂ, MeromorphicOn F HH → F =ᶠ[codiscreteWithin (halfPlane 2)] T →
      IsNaturalBoundary F HH lineOne

/-- `F_δ = {a ∈ Σ_Q : Re a > B_∞ + δ}`. -/
def Fdelta (δ : ℝ) : Set ℂ := {a | a ∈ PoleSetQ ∧ Binf + δ < a.re}

/-! ## 3. The continuation of `Q` -/

/-- `Qc` is *the* continuation of `Q` to `Re z > 0` as a function: meromorphic there, equal to the series
on `Re z > 1`, and analytic off `Σ_Q`. The last clause pins `Qc` down pointwise off `Σ_Q` (identity
theorem on the connected set `{Re z > 0} ∖ Σ_Q`), so a formula that evaluates `Qc` off `Σ_Q` does not
depend on the choice. Non-vacuous: `exists_isQCont` in `Statements.lean`. -/
def IsQCont (Qc : ℂ → ℂ) : Prop :=
  MeromorphicOn Qc (halfPlane 0) ∧ EqOn Qc Q (halfPlane 1) ∧
    AnalyticOnNhd ℂ Qc (halfPlane 0 \ PoleSetQ)

/-! ## 4. The classical inputs (Z1)–(Z7), and two inputs the list does not name

Each is a `Prop`, true by the cited classical theorem and not proved here, and appears as an explicit
hypothesis exactly on the statements whose proofs (in the paper) use it. None is an `axiom`. -/

/-- (Z1), the part not already proved. The paper's (Z1) has four clauses: `0 < β < 1` (here true by the
definition of `NontrivialZeros`), `ζ(1 + it) ≠ 0` (Mathlib, `riemannZeta_ne_zero_of_one_le_re`),
`ζ(x) ≠ 0` for `0 < x < 1` (paper 1's library, `riemannZeta_ne_zero_of_mem_Ioo`), and the symmetry:
`ρ̄` and `1 - ρ̄` are zeros of the same multiplicity as `ρ`. Only the symmetry is left as a hypothesis
(`conj_mem_nontrivialZeros` in paper 1's library proves that `ρ̄` is a zero, not the multiplicity). -/
def Z1 : Prop :=
  ∀ ρ ∈ NontrivialZeros,
    (conj ρ ∈ NontrivialZeros ∧ zetaMult (conj ρ) = zetaMult ρ) ∧
      (1 - conj ρ ∈ NontrivialZeros ∧ zetaMult (1 - conj ρ) = zetaMult ρ)

/-- `N(t)`: the number of zeros with `0 < γ ≤ t`, counted with multiplicity. The set is finite (zeros are
discrete and avoid a neighbourhood of `1`), so `∑ᶠ` is the finite sum. -/
def Nzero (t : ℝ) : ℝ :=
  ∑ᶠ ρ ∈ {ρ : ℂ | ρ ∈ NontrivialZeros ∧ 0 < ρ.im ∧ ρ.im ≤ t}, (zetaMult ρ : ℝ)

/-- (Z2), Riemann–von Mangoldt: `N(t) = (t/2π) log(t/2π) - t/2π + O(log t)` as `t → ∞`, and
`N(t+1) - N(t) ≤ C₁ log(t+3)` for all `t ≥ 0`. (The paper's further consequences, "hence ...", are derived
from these two.) -/
def Z2 : Prop :=
  (∃ C : ℝ, ∀ᶠ t in atTop,
      |Nzero t - (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi))| ≤
        C * Real.log t) ∧
    ∃ C₁ : ℝ, ∀ t : ℝ, 0 ≤ t → Nzero (t + 1) - Nzero t ≤ C₁ * Real.log (t + 3)

/-- (Z3), the local expansion of `ζ'/ζ`: for `-1 ≤ Re z ≤ 2`, `|Im z| ≥ 2`,
`ζ'/ζ(z) = ∑_{|γ - Im z| ≤ 1} m(ρ)/(z - ρ) + O(log |Im z|)` uniformly. Asserted at points with `ζ(z) ≠ 0`
(at a zero both sides have a pole; the identity is one of meromorphic functions). -/
def Z3 : Prop :=
  ∃ C : ℝ, ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 → 2 ≤ |z.im| → riemannZeta z ≠ 0 →
    ‖deriv riemannZeta z / riemannZeta z -
        ∑ᶠ ρ ∈ {ρ : ℂ | ρ ∈ NontrivialZeros ∧ |ρ.im - z.im| ≤ 1}, (zetaMult ρ : ℂ) / (z - ρ)‖ ≤
      C * Real.log |z.im|

/-- `N₀(t)`: the number of distinct zeros `1/2 + iγ` with `0 < γ ≤ t`. -/
def N0 (t : ℝ) : ℕ :=
  Set.ncard {ρ : ℂ | ρ ∈ NontrivialZeros ∧ ρ.re = 1 / 2 ∧ 0 < ρ.im ∧ ρ.im ≤ t}

/-- (Z4), Hardy–Littlewood: `N₀(t) ≥ A₀ t` for `t ≥ t₀`, some `A₀ > 0`. (A junk `ncard` would be `0`, which
makes this false, not vacuous.) -/
def Z4 : Prop := ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ t₀ : ℝ, ∀ t ≥ t₀, A₀ * t ≤ (N0 t : ℝ)

/-- (Z5), the prime number theorem in the paper's form: for fixed `θ > 0` there is `x₀(θ)` such that for
`x ≥ x₀(θ)` the interval `(x, (1+θ)x)` contains at least `θx/(2 log x)` primes. (It follows from PNT+'s
sorry-free `pi_alt`, but that derivation is not in any library; see the review notes.) -/
def Z5 : Prop :=
  ∀ θ : ℝ, 0 < θ → ∃ x₀ : ℝ, ∀ x ≥ x₀,
    θ * x / (2 * Real.log x) ≤ ({p : ℕ | p.Prime ∧ x < p ∧ (p : ℝ) < (1 + θ) * x}.ncard : ℝ)

/-- (Z6), Stirling: for `0 < x₁ ≤ x₂` there is `C` with `|Γ(x+iy)| ≤ C(1+|y|)^{x₂} e^{-π|y|/2}` on
`x₁ ≤ x ≤ x₂`. (The paper's second sentence, `1/Γ` entire, is Mathlib's `differentiable_one_div_Gamma`.) -/
def Z6 : Prop :=
  ∀ x₁ x₂ : ℝ, 0 < x₁ → x₁ ≤ x₂ → ∃ C : ℝ, ∀ x ∈ Icc x₁ x₂, ∀ y : ℝ,
    ‖Gamma (x + y * I)‖ ≤ C * (1 + |y|) ^ x₂ * Real.exp (-(Real.pi * |y| / 2))

/-- `C₀ = 1 + γ_E/2 - log(4π)/2 = 0.0230957…`. -/
def C0 : ℝ := 1 + Real.eulerMascheroniConstant / 2 - Real.log (4 * Real.pi) / 2

/-- (Z7), from the Hadamard product: `∑_ρ m(ρ) Re(1/ρ) = C₀`, the sum over the distinct zeros. `HasSum`
over the subtype is unconditional convergence, which for these positive terms is plain convergence. -/
def Z7 : Prop :=
  HasSum (fun ρ : NontrivialZeros => (zetaMult (ρ : ℂ) : ℝ) * (1 / (ρ : ℂ)).re) C0

/-- Littlewood's theorem on gaps between ordinates (Titchmarsh, Ch. IX), used in the proof of
`cl:thm:filter`(iii) and **not** among (Z1)–(Z7): for large `t` there is an ordinate `γ` with
`|γ - t| < a / log log log t`. -/
def ZLittlewood : Prop :=
  ∃ a : ℝ, ∀ᶠ t in atTop, ∃ ρ ∈ NontrivialZeros,
    |ρ.im - t| < a / Real.log (Real.log (Real.log t))

/-- Hypothesis (F) of Section 4.9 (Conjecture 1 of Bhowmik and Schlage-Puchta): if `γ₁ + γ₂ = γ₃ + γ₄ ≠ 0` for
ordinates of non-trivial zeros, then `{γ₁, γ₂} = {γ₃, γ₄}`. -/
def HypF : Prop :=
  ∀ ρ₁ ∈ NontrivialZeros, ∀ ρ₂ ∈ NontrivialZeros, ∀ ρ₃ ∈ NontrivialZeros, ∀ ρ₄ ∈ NontrivialZeros,
    ρ₁.im + ρ₂.im = ρ₃.im + ρ₄.im → ρ₁.im + ρ₂.im ≠ 0 →
      ({ρ₁.im, ρ₂.im} : Set ℝ) = {ρ₃.im, ρ₄.im}

/-! ## 5. Representations and single-representation points (Section 3.4) -/

/-- `(ρ, k)` is a *representation* of `u`: `ρ` a zero, `k ≥ 1` squarefree, `ρ/k = u`. -/
def IsRep (u ρ : ℂ) (k : ℕ) : Prop :=
  ρ ∈ NontrivialZeros ∧ 1 ≤ k ∧ Squarefree k ∧ ρ / (k : ℂ) = u

/-- `(ρ, q)` is the only representation of `ρ/q` (the paper's *good* pair). -/
def IsSingleRep (ρ : ℂ) (q : ℕ) : Prop :=
  ∀ ρ' : ℂ, ∀ k : ℕ, IsRep (ρ / (q : ℂ)) ρ' k → ρ' = ρ ∧ k = q

/-- The zero `ζ*` of Lemma `nr:lem:rigidity` attached to a representation `(ρ', k)` of `ρ/q`: `ρ'` if `k > q`,
`1 - ρ̄'` if `k < q`. (The lemma shows `k ≠ q` for every representation other than `(ρ, q)`, so the `else` branch
is used only for `k < q`.) -/
def zetaStar (ρ' : ℂ) (k q : ℕ) : ℂ := if q < k then ρ' else 1 - conj ρ'

/-- `M(X) = ⌈2 log X / A₀⌉`. -/
def Mfun (A₀ X : ℝ) : ℕ := ⌈2 * Real.log X / A₀⌉₊

/-- `𝓟(X)` of Theorem `nr:thm:single`: pairs `(ρ, q)` with `ρ = 1/2 + iγ` a zero, `X/M < γ ≤ X`,
`q` prime and `γ/q ∈ J = (y - ε/2, y + ε/2)`. -/
def singlePairs (A₀ y ε X : ℝ) : Set (ℂ × ℕ) :=
  {p | p.1 ∈ NontrivialZeros ∧ p.1.re = 1 / 2 ∧ X / (Mfun A₀ X : ℝ) < p.1.im ∧ p.1.im ≤ X ∧
    p.2.Prime ∧ p.1.im / (p.2 : ℝ) ∈ Ioo (y - ε / 2) (y + ε / 2)}

/-! ## 6. Branches -/

/-- `g` is an *admissible germ* at `s₁` of `F` for the region `Ω` and the start set `S`: the terminal germ at
`s₁` of a continuation of `F` along a path in `Ω` that starts in `S` (the continuation is part of
`IsTerminalGerm`, which matches the paper's "along which the continuation exists"). Paper 1's
`IsAdmissibleGerm g s₁` is `IsAdmissibleGermOn G (HH \ catalogue) (halfPlane 2) g s₁`. -/
def IsAdmissibleGermOn (F : ℂ → ℂ) (Ω S : Set ℂ) (g : ℂ → ℂ) (s₁ : ℂ) : Prop :=
  ∃ γ : C(unitInterval, ℂ), (∀ t, γ t ∈ Ω) ∧ γ 0 ∈ S ∧ γ 1 = s₁ ∧ IsTerminalGerm F γ g

/-- A branch of `P` at `z₁`: a germ reached from the series `P` (on `Re z > 1`) by continuation along a path in
`{Re z > 0} ∖ Σ_Q`. The paper does not define "branch of `P`" outside Section 4 (where `Σ = Σ_Q` under
RH); this is the reading used for Corollary `nr:cor:LW` and Lemma `cl:lem:P`. -/
def IsPBranch (g : ℂ → ℂ) (z₁ : ℂ) : Prop :=
  IsAdmissibleGermOn P (halfPlane 0 \ PoleSetQ) (halfPlane 1) g z₁

/-! ## 7. The prime-sum error and its Mellin transform (Section 3.7) -/

/-- `Θ(t) = ∑_p log p · e^{-pt}` (`t > 0`). (Same as paper 1's `TIdentity.Fw`.) -/
def Theta (t : ℝ) : ℝ := ∑' p : Nat.Primes, Real.log (p : ℕ) * Real.exp (-((p : ℕ) * t))

/-- `h(t) = Θ(t) - 1/t`. -/
def hErr (t : ℝ) : ℝ := Theta t - 1 / t

/-- `𝓜(s) = ∫_0^1 h(t)² t^{s-1} dt`. -/
def Mcal (s : ℂ) : ℂ := ∫ t in Ioc (0 : ℝ) 1, ((hErr t ^ 2 : ℝ) : ℂ) * (t : ℂ) ^ (s - 1)

/-- The real `x` at which `𝓜(x) = ∫_0^1 h(t)² t^{x-1} dt` converges (Lebesgue integrability of the non-negative
integrand; `t^{x-1}` is the real power, `t > 0`). With `u = -log t` this is the convergence set of the Laplace
transform `∫_0^∞ h(e^{-u})² e^{-xu} du` of Step 2 of `nr:thm:test`, so its infimum is the abscissa of that step and of
`nr:rem:classical`. The set is an up-set (`t^{x'-1} ≤ t^{x-1}` on `(0,1]` for `x' ≥ x`). -/
def mellinConvSet : Set ℝ :=
  {x | IntegrableOn (fun t : ℝ => hErr t ^ 2 * t ^ (x - 1)) (Ioc (0 : ℝ) 1)}

/-- The abscissa of convergence `σ_c = inf mellinConvSet` of `𝓜`. `sInf` is genuine only for a non-empty set that
is bounded below (otherwise it is the junk `0`): every statement that uses `sigmaC` also asserts both
(`rem_classical_ii`, `rem_classical_iii`), and states the bound in the junk-free form "every `x` in the set is
`≥ 2B`" as well. -/
def sigmaC : ℝ := sInf mellinConvSet

/-- `E(s) = ∫_1^∞ Θ(t)² t^{s-1} dt`. -/
def Ecal (s : ℂ) : ℂ := ∫ t in Ioi (1 : ℝ), ((Theta t ^ 2 : ℝ) : ℂ) * (t : ℂ) ^ (s - 1)

/-- `e(z) = ∫_1^∞ Θ(t) t^{z-1} dt`. -/
def ecal (z : ℂ) : ℂ := ∫ t in Ioi (1 : ℝ), (Theta t : ℂ) * (t : ℂ) ^ (z - 1)

/-- The Laplace transform `𝓛(s) = ∫_0^∞ φ(u) e^{-su} du` of Lemma `nr:lem:Landau`. -/
def laplace (φ : ℝ → ℝ) (s : ℂ) : ℂ := ∫ u in Ioi (0 : ℝ), (φ u : ℂ) * exp (-(s * u))

/-- The real `x` at which `∫_0^∞ φ(u) e^{-xu} du < ∞` (Lebesgue integrability of the non-negative
integrand). -/
def laplaceConvSet (φ : ℝ → ℝ) : Set ℝ :=
  {x | IntegrableOn (fun u => φ u * Real.exp (-(x * u))) (Ioi (0 : ℝ))}

/-- The constant `A = Γ(2B)⁻¹ ∑_{β = B} m(ρ)² |Γ(ρ)|²` of Lemma `nr:lem:A`, the sum over the distinct
zeros with `β = B` in both half-planes. (A `tsum` of non-negative terms; `0 < A` implies summability.) -/
def Aconst : ℝ :=
  (∑' ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ ρ.re = Bsup},
      (zetaMult (ρ : ℂ) : ℝ) ^ 2 * ‖Gamma (ρ : ℂ)‖ ^ 2) / Real.Gamma (2 * Bsup)

/-- `Ω = {Re z > 0} ∖ ⋃_{a ∈ Σ} (a - [0, ∞))`, the right half-plane with a horizontal cut running west from every
point of `Σ` (Section 4.4). -/
def OmegaP : Set ℂ := halfPlane 0 \ ⋃ a ∈ PoleSetQ, {z | ∃ t : ℝ, 0 ≤ t ∧ z = a - t}

/-! ## 8. The class of Section 4: affine map, regions, kernel hypotheses -/

/-- The affine map `L(s) = ℓ s + ℓ₀`, `ℓ > 0`, `ℓ₀ ∈ ℝ`. -/
structure Aff where
  ell : ℝ
  ell0 : ℝ
  ell_pos : 0 < ell

namespace Aff

/-- `L(s) = ℓ s + ℓ₀`. -/
def app (A : Aff) (s : ℂ) : ℂ := (A.ell : ℂ) * s + A.ell0

/-- `ℍ_L = {Re L(s) > 1}`. -/
def HL (A : Aff) : Set ℂ := {s | 1 < (A.app s).re}

/-- `D_L = {1 < Re L(s) < 3}`. -/
def DL (A : Aff) : Set ℂ := {s | 1 < (A.app s).re ∧ (A.app s).re < 3}

/-- `R_L = {Re L(s) > 2}`. -/
def RL (A : Aff) : Set ℂ := {s | 2 < (A.app s).re}

/-- The boundary line `Re L(s) = 1`. -/
def lineL (A : Aff) : Set ℂ := {s | (A.app s).re = 1}

/-- `Str(s) = {0 < Re z < Re L(s)}`. -/
def Str (A : Aff) (s : ℂ) : Set ℂ := {z | 0 < z.re ∧ z.re < (A.app s).re}

/-- The open set `{(z, s) : s ∈ D_L, z ∈ Str(s)} ⊆ ℂ²` of (K1). -/
def domK1 (A : Aff) : Set (ℂ × ℂ) := {p | p.2 ∈ A.DL ∧ p.1 ∈ A.Str p.2}

/-- The open set `{(z, s) : s ∈ ℍ_L, z ∈ Str(s)}` of (H2a). -/
def domH2a (A : Aff) : Set (ℂ × ℂ) := {p | p.2 ∈ A.HL ∧ p.1 ∈ A.Str p.2}

/-- `L(s) = s`. -/
def idL : Aff := ⟨1, 0, one_pos⟩

/-- `L(s) = 2s` (sums of two squares). -/
def twoL : Aff := ⟨2, 0, two_pos⟩

/-- `L(s) = 2s + 1` (the series `S`). -/
def twoOneL : Aff := ⟨2, 1, two_pos⟩

end Aff

/-- Meromorphic on `ℂ²`, in the usual local-quotient sense (Mathlib has no meromorphic functions of several
variables): near every point, on a polydisc, `k = u/v` with `u, v` holomorphic and `v` not identically zero;
nothing is asked of `k` where `v = 0`. -/
def IsMeromorphic₂ (k : ℂ → ℂ → ℂ) : Prop :=
  ∀ p : ℂ × ℂ, ∃ r > 0, ∃ u v : ℂ × ℂ → ℂ,
    AnalyticOnNhd ℂ u (ball p r) ∧ AnalyticOnNhd ℂ v (ball p r) ∧ (∃ q ∈ ball p r, v q ≠ 0) ∧
      ∀ q ∈ ball p r, v q ≠ 0 → k q.1 q.2 = u q / v q

/-- (K1) Holomorphy: `k` is holomorphic on `{(z, s) : s ∈ D_L, z ∈ Str(s)} ⊆ ℂ²` (joint, i.e. Fréchet,
complex differentiability). The kernel is written `k z s` for the paper's `k(z, s)`. -/
def K1 (A : Aff) (k : ℂ → ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ (fun p : ℂ × ℂ => k p.1 p.2) A.domK1

/-- (K2) Decay: for compact `C ⊆ D_L` and `[x₁, x₂] ⊆ (0, min_C Re L)` there is `M` with
`|k(x+iy, s)| ≤ M (1+|y|)^{-2}`. -/
def K2 (A : Aff) (k : ℂ → ℂ → ℂ) : Prop :=
  ∀ C : Set ℂ, IsCompact C → C ⊆ A.DL → ∀ x₁ x₂ : ℝ, 0 < x₁ → x₁ ≤ x₂ →
    (∀ s ∈ C, x₂ < (A.app s).re) →
      ∃ M : ℝ, ∀ x ∈ Icc x₁ x₂, ∀ s ∈ C, ∀ y : ℝ, ‖k (x + y * I) s‖ ≤ M / (1 + |y|) ^ 2

/-- (K3) Reality, on the (conjugation-invariant) domain of (K1): `k(z̄, s̄) = conj k(z, s)`. -/
def K3 (A : Aff) (k : ℂ → ℂ → ℂ) : Prop :=
  ∀ s ∈ A.DL, ∀ z ∈ A.Str s, k (conj z) (conj s) = conj (k z s)

/-- (K4) Global form: `k` is meromorphic on `ℂ²`. -/
def K4 (k : ℂ → ℂ → ℂ) : Prop := IsMeromorphic₂ k

/-- The double prime series `∑_{p,q} W_s(p,q)` (the weight is `W s p q`). -/
def Dser (W : ℂ → ℕ → ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑' pq : Nat.Primes × Nat.Primes, W s (pq.1 : ℕ) (pq.2 : ℕ)

/-- (R) The series: `∑_{p,q} W_s(p,q)` converges absolutely on `R_L`, its sum is holomorphic on `R_L` and real
on `R_L ∩ ℝ`, and it equals the integral `(1/2πi) ∫_{(c)} k(z,s) F(z) F(L(s) - z) dz` for every
`s ∈ R_L ∩ D_L` and every `c ∈ (1, Re L(s) - 1)`. `F = P` gives (R) for `D` (eq. `(cl:eq:D)`), `F = Q` for
`D^log` (eq. `(cl:eq:Dw)`). On such a line both factors are the convergent prime sums. -/
def HypR (A : Aff) (k : ℂ → ℂ → ℂ) (W : ℂ → ℕ → ℕ → ℂ) (F : ℂ → ℂ) : Prop :=
  (∀ s ∈ A.RL, Summable fun pq : Nat.Primes × Nat.Primes => ‖W s (pq.1 : ℕ) (pq.2 : ℕ)‖) ∧
    DifferentiableOn ℂ (Dser W) A.RL ∧
    (∀ x : ℝ, (x : ℂ) ∈ A.RL → (Dser W x).im = 0) ∧
    ∀ s ∈ A.RL ∩ A.DL, ∀ c : ℝ, 1 < c → c < (A.app s).re - 1 →
      Dser W s = VerticalIntegral' (fun z => k z s * F z * F (A.app s - z)) c

/-- `J_{ab}(s) = ∫_a^{L(s)-b} k(z,s) dz` over the straight segment, written in its parametrised form
`(L(s) - a - b) ∫_0^1 k(a + t(L(s) - a - b), s) dt` (Lemma `cl:lem:J`; Mathlib has no segment integral). -/
def Jseg (A : Aff) (k : ℂ → ℂ → ℂ) (a b s : ℂ) : ℂ :=
  (A.app s - a - b) * ∫ t in (0 : ℝ)..1, k (a + (t : ℂ) * (A.app s - a - b)) s

/-- (H2-log) Excursions: for `a, b ∈ Σ`, the derivative of `J_{ab}` extends from `D_L` to a single-valued
meromorphic function on `ℍ_L`. -/
def H2log (A : Aff) (k : ℂ → ℂ → ℂ) : Prop :=
  ∀ a ∈ PoleSetQ, ∀ b ∈ PoleSetQ, ∃ g : ℂ → ℂ, MeromorphicOn g A.HL ∧
    EqOn g (deriv (Jseg A k a b)) A.DL

/-- (H2a): `k` is holomorphic on `{(z, s) : s ∈ ℍ_L, z ∈ Str(s)}`. -/
def H2a (A : Aff) (k : ℂ → ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ (fun p : ℂ × ℂ => k p.1 p.2) A.domH2a

/-- (H2b): `k(z, s) = g(z - θ s)` with `g` meromorphic on `ℂ` and `θ ∈ ℝ`. -/
def H2b (k : ℂ → ℂ → ℂ) : Prop :=
  ∃ g : ℂ → ℂ, ∃ θ : ℝ, MeromorphicOn g univ ∧ ∀ z s, k z s = g (z - θ * s)

/-- The bracket `𝔟(s) = k(1, s) + k(L(s) - 1, s)`. -/
def bracket (A : Aff) (k : ℂ → ℂ → ℂ) (s : ℂ) : ℂ := k 1 s + k (A.app s - 1) s

/-- The catalogue `𝒞_L = {s ∈ ℍ_L : L(s) ∈ Σ + Σ}`. -/
def catalogueL (A : Aff) : Set ℂ := {s | s ∈ A.HL ∧ A.app s ∈ Pinch}

/-- The scaled-zero pinches `α_{ρ,n} = L⁻¹(1 + ρ/n)`, `n ≥ 1` squarefree. -/
def scaledZeroPinches (A : Aff) : Set ℂ :=
  {α | ∃ ρ ∈ NontrivialZeros, ∃ n : ℕ, 1 ≤ n ∧ Squarefree n ∧ A.app α = 1 + ρ / (n : ℂ)}

/-- The coefficient `X_α` of Lemma `cl:lem:J`: with `b = L(α) - 1`, `X_α = c₁c_b(J_{1b} + J_{b1})` if `b ≠ 1`
and `X_α = J_{11}` if `b = 1` (the paper writes `c₁²J₁₁ = J₁₁`, as `c₁ = -1`). Under RH, `b` is the unique
`b ∈ Σ` with `L(α) = 1 + b` (Proposition `cl:prop:catalogue`(i)). -/
def Xcoef (A : Aff) (k : ℂ → ℂ → ℂ) (α : ℂ) (s : ℂ) : ℂ :=
  if A.app α - 1 = 1 then Jseg A k 1 1 s
  else cP 1 * cP (A.app α - 1) * (Jseg A k 1 (A.app α - 1) s + Jseg A k (A.app α - 1) 1 s)

/-- (H3): every point of the line `Re L(s) = 1` is a limit of scaled-zero pinches `α` with `X_α ≢ 0`
(`X_α` is holomorphic on the connected strip `D_L`; "`≢ 0`" is "not identically zero there"). -/
def H3 (A : Aff) (k : ℂ → ℂ → ℂ) : Prop :=
  ∀ s₀ ∈ A.lineL, ∀ r : ℝ, 0 < r → ∃ α ∈ scaledZeroPinches A, ‖α - s₀‖ < r ∧
    ∃ s ∈ A.DL, Xcoef A k α s ≠ 0

/-- The slit disc about `α`: the disc with the leftward horizontal radius `α - [0, r)` removed. On it the
principal `Complex.log (s - α)` is holomorphic (its cut is exactly that radius). -/
def slitDiscL (α : ℂ) (r : ℝ) : Set ℂ := ball α r \ {s | ∃ t : ℝ, 0 ≤ t ∧ s = α - t}

/-! ## 9. The series of the examples and of Sections 4.8–4.10 -/

/-- Kernel of the Goldbach series `G`: `k(z, s) = K_s(z)`, `L(s) = s`. -/
def kerG (z s : ℂ) : ℂ := KerS s z

/-- Weight of `G`: `(p+q)^{-s}`. -/
def WG (s : ℂ) (p q : ℕ) : ℂ := (((p + q : ℕ) : ℂ)) ^ (-s)

/-- Kernel of `∑(p²+q²)^{-s}`: `½ Γ(z/2) Γ(s - z/2)/Γ(s)`, `L(s) = 2s`. -/
def kerSq (z s : ℂ) : ℂ := (1 / 2) * Gamma (z / 2) * Gamma (s - z / 2) / Gamma s

/-- Weight `(p² + q²)^{-s}`. -/
def WSq (s : ℂ) (p q : ℕ) : ℂ := (((p ^ 2 + q ^ 2 : ℕ) : ℂ)) ^ (-s)

/-- `K(w) = Γ(w) Γ(2 - w)`. -/
def KS (w : ℂ) : ℂ := Gamma w * Gamma (2 - w)

/-- Kernel of `S`: `½ K((z - s + 1)/2)`, `L(s) = 2s + 1`. -/
def kerS (z s : ℂ) : ℂ := (1 / 2) * KS ((z - s + 1) / 2)

/-- Weight of `S`: `p^{1-s} q^{2-s} (p² + q²)^{-2}`. -/
def WS (s : ℂ) (p q : ℕ) : ℂ :=
  (p : ℂ) ^ (1 - s) * (q : ℂ) ^ (2 - s) * ((((p ^ 2 + q ^ 2 : ℕ) : ℂ)) ^ 2)⁻¹

/-- `W₀(p,q;s) = (p+q)^{-s}[1 - s + s(s+1) pq/(p+q)²]`. -/
def W0 (s : ℂ) (p q : ℕ) : ℂ :=
  (((p + q : ℕ) : ℂ)) ^ (-s) * (1 - s + s * (s + 1) * ((p * q : ℕ) : ℂ) / (((p + q : ℕ) : ℂ)) ^ 2)

/-- The log-weighted `log p log q W₀(p,q;s)`. -/
def W0log (s : ℂ) (p q : ℕ) : ℂ := (Real.log p : ℂ) * (Real.log q : ℂ) * W0 s p q

/-- The log weight `log p log q (p+q)^{-s}` of `T`. -/
def WT (s : ℂ) (p q : ℕ) : ℂ := (Real.log p : ℂ) * (Real.log q : ℂ) * WG s p q

/-- `T₀ = ∑ log p log q W₀`. -/
def T0 (s : ℂ) : ℂ := Dser W0log s

/-- `G₀ = ∑ W₀`. -/
def G0 (s : ℂ) : ℂ := Dser W0 s

/-- The kernel `k₀(z, s) = K_s(z)(z - 1)(s - 1 - z)` of `W₀`. -/
def k0 (z s : ℂ) : ℂ := KerS s z * (z - 1) * (s - 1 - z)

/-- The kernel `k_r(z, s) = K_s(z) ((z - 1)(s - 1 - z))^r` of `cl:rem:order` (the factor of `k₀` raised to the
`r`-th power; `k_1 = k₀`, `kr_one`). -/
def kr (r : ℕ) (z s : ℂ) : ℂ := KerS s z * ((z - 1) * (s - 1 - z)) ^ r

/-- `H(z, w)` for `H ∈ ℂ[z, w]` (variables `X 0 = z`, `X 1 = w`). -/
def evalH (H : MvPolynomial (Fin 2) ℂ) (z w : ℂ) : ℂ := MvPolynomial.eval ![z, w] H

/-- `k_H(z, s) = K_s(z) H(z, s - z)`. -/
def kH (H : MvPolynomial (Fin 2) ℂ) (z s : ℂ) : ℂ := KerS s z * evalH H z (s - z)

/-- `D_H(s) = (1/2πi) ∫_{(c)} k_H(z,s) Q(z) Q(s-z) dz` for `σ > 2` (eq. `(cl:eq:DH)`), with the line
`c = σ/2 ∈ (1, σ - 1)`; the paper allows any `c ∈ (1, σ - 1)`, and the value does not depend on it. -/
def DH (H : MvPolynomial (Fin 2) ℂ) (s : ℂ) : ℂ :=
  VerticalIntegral' (fun z => kH H z s * Q z * Q (s - z)) (s.re / 2)

/-- `H(z, w) = ∑_{i,j < N} h_{ij} z^{(i)} w^{(j)}`: the coefficients `h` (indices `< N`) of `H` in the basis of
rising factorials `z^{(i)} = z(z+1)⋯(z+i-1)` (Mathlib's `ascPochhammer`), as an identity of functions. For a given
`N` large enough the `h_{ij}` exist and are unique. -/
def IsRisingRep (H : MvPolynomial (Fin 2) ℂ) (N : ℕ) (h : ℕ → ℕ → ℂ) : Prop :=
  ∀ z w : ℂ, evalH H z w = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
    h i j * (ascPochhammer ℂ i).eval z * (ascPochhammer ℂ j).eval w

/-- `W_H(p,q;s) = ∑_{i,j} h_{ij} Γ(s+i+j)/Γ(s) p^i q^j (p+q)^{-s-i-j}` (the first remark after `cl:thm:filter`).
Used only for `σ > 2`, where `Γ(s) ≠ 0`. -/
def WH (N : ℕ) (h : ℕ → ℕ → ℂ) (s : ℂ) (p q : ℕ) : ℂ :=
  ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
    h i j * (Gamma (s + i + j) / Gamma s) * (p : ℂ) ^ i * (q : ℂ) ^ j *
      (((p + q : ℕ) : ℂ)) ^ (-(s + i + j))

/-- The log-weighted `log p log q W_H(p,q;s)`, whose double series is `D_H` for `σ > 2`. -/
def WHlog (N : ℕ) (h : ℕ → ℕ → ℂ) (s : ℂ) (p q : ℕ) : ℂ :=
  (Real.log p : ℂ) * (Real.log q : ℂ) * WH N h s p q

/-- The summand `m(ρ)m(ρ') Γ(ρ)Γ(ρ')/Γ(s₀) H(ρ, ρ')` of `C_H(τ₀)`, indexed by the ordered pairs of zeros
`(ρ, ρ')` with `ρ + ρ' = s₀ = 1 + iτ₀`. -/
def CHterm (H : MvPolynomial (Fin 2) ℂ) (τ₀ : ℝ)
    (p : {p : ℂ × ℂ // p.1 ∈ NontrivialZeros ∧ p.2 ∈ NontrivialZeros ∧ p.1 + p.2 = 1 + τ₀ * I}) : ℂ :=
  (zetaMult p.1.1 : ℂ) * (zetaMult p.1.2 : ℂ) * (Gamma p.1.1 * Gamma p.1.2 / Gamma (1 + τ₀ * I)) *
    evalH H p.1.1 p.1.2

/-- `C_H(τ₀) = ∑_{ρ + ρ' = s₀} m(ρ)m(ρ') Γ(ρ)Γ(ρ')/Γ(s₀) H(ρ, ρ')`, `s₀ = 1 + iτ₀` (eq. `(cl:eq:CH)`); `0`
when there is no pair. -/
def CH (H : MvPolynomial (Fin 2) ℂ) (τ₀ : ℝ) : ℂ := ∑' p, CHterm H τ₀ p

/-- The summand of the sum `∑_{γ > 0} m(ρ)² |Γ(ρ)|² |ρ - 1|²` of `cl:thm:filter`(iv). -/
def lambda0Term (ρ : {ρ : ℂ // ρ ∈ NontrivialZeros ∧ 0 < ρ.im}) : ℝ :=
  (zetaMult (ρ : ℂ) : ℝ) ^ 2 * ‖Gamma (ρ : ℂ)‖ ^ 2 * ‖(ρ : ℂ) - 1‖ ^ 2

/-- `Λ₀ = π/16 + 2 ∑_{γ > 0} m(ρ)² |Γ(ρ)|² |ρ - 1|²`. -/
def Lambda0 : ℝ := Real.pi / 16 + 2 * ∑' ρ, lambda0Term ρ

/-- `T_k(s) = ∑_{p₁,…,p_k} log p₁ ⋯ log p_k (p₁ + ⋯ + p_k)^{-s}` (`σ > k`). -/
def Tk (k : ℕ) (s : ℂ) : ℂ :=
  ∑' p : Fin k → Nat.Primes,
    (∏ i, (Real.log (p i : ℕ) : ℂ)) * (((∑ i, (p i : ℕ) : ℕ) : ℂ)) ^ (-s)

end GoldbachBoundaries.Paper2
