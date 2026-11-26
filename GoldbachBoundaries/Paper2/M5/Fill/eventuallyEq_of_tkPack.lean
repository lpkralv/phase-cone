import GoldbachBoundaries.Paper2.M5.TkLine

/-!
# M5 filler T3: `eventuallyEq_of_tkPack`

Identity theorem on the connected `halfPlane (k - 1)`: at `k + 1` both `G` and the package's `F` equal `T_k` near it,
so they agree off a discrete subset, hence on a punctured neighbourhood of every point (as M4b's `eventuallyEq_Fmero`).
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M5

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

theorem eventuallyEq_of_tkPack {k : ℕ} {F H G : ℂ → ℂ} (hP : TkPack k F H)
    (hG : MeromorphicOn G (halfPlane ((k : ℝ) - 1))) (hGT : G =ᶠ[codiscreteWithin (halfPlane k)] Tk k) :
    ∀ s ∈ halfPlane ((k : ℝ) - 1), G =ᶠ[𝓝[≠] s] F := by
  set z₁ : ℂ := (((k : ℝ) + 1 : ℝ) : ℂ) with hz₁
  have hz₁k : z₁ ∈ halfPlane (k : ℝ) := by
    show (k : ℝ) < z₁.re; rw [hz₁, ofReal_re]; linarith
  have hz₁U : z₁ ∈ halfPlane ((k : ℝ) - 1) := by
    show (k : ℝ) - 1 < z₁.re; rw [hz₁, ofReal_re]; linarith
  have hn : halfPlane (k : ℝ) ∈ 𝓝 z₁ := (isOpen_halfPlane _).mem_nhds hz₁k
  have h1 : G =ᶠ[𝓝[≠] z₁] Tk k := eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin hGT hn
  have h2 : Tk k =ᶠ[𝓝[≠] z₁] F := by
    filter_upwards [nhdsWithin_le_nhds hn] with t ht
    exact (hP.2.1 ht).symm
  have hcod : G =ᶠ[codiscreteWithin (halfPlane ((k : ℝ) - 1))] F :=
    M2.eventuallyEq_codiscreteWithin_of_nhdsNE (isPreconnected_halfPlane _) hG hP.1 hz₁U (h1.trans h2)
  intro s hs
  exact eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin hcod ((isOpen_halfPlane _).mem_nhds hs)

end GoldbachBoundaries.Paper2.M5
