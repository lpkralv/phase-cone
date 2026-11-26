import GoldbachBoundaries.Paper2.M6.Defs

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory

namespace GoldbachBoundaries.Paper2.M6

open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **`HasCatalogueValues` depends only on the values on the catalogue.** The three clauses evaluate at `2`,
`1 + 1/k` and `1 + ρ/n`, all catalogue points by definition. -/
theorem hasCatalogueValues_congr {v w : ℂ → ℂ} (h : ∀ α ∈ catalogue, v α = w α)
    (hv : HasCatalogueValues v) : HasCatalogueValues w := by
  obtain ⟨h1, h2, h3⟩ := hv
  refine ⟨?_, fun k hk hsf => ?_, fun n hn hsf ρ hρ => ?_⟩
  · rw [← h 2 (Or.inl (Or.inl rfl))]; exact h1
  · rw [← h _ (Or.inl (Or.inr ⟨k, hk, hsf, rfl⟩))]; exact h2 k hk hsf
  · rw [← h _ (Or.inr ⟨n, hn, hsf, ρ, hρ, rfl⟩)]; exact h3 n hn hsf ρ hρ

end GoldbachBoundaries.Paper2.M6
