import GoldbachBoundaries.Paper2.M4b.ExG
import GoldbachBoundaries.Paper2.M4b.Fill.E1Common

noncomputable section
open Complex Filter Topology Set MeasureTheory
namespace GoldbachBoundaries.Paper2.M4b
open GoldbachBoundaries GoldbachBoundaries.Paper2

/-- **`D_H` as a double prime series, without reality** (no hypothesis on `H` beyond `hrep`). `WHlog N h =
wtd log (Wrise N (cWH h))` (`WHlog_eq_wtd`, `WH_eq_Wrise`, both `rfl`). Summability and holomorphy on `σ > 2`:
`rising_summable_eq`, `rising_differentiableOn` (`differentiableOn_cWH`), `ω = log`. The identity on `R_L ∩ D_L` and
`D_H = Dser` at `σ > 2` (the line `c = σ/2 ∈ (1, σ - 1)` of the definition `DH`): `rising_summable_eq` and
`kH_eq_krise` on the line (`Re z = c > 0`, `Re(s - z) = σ - c > 0`), `primeSum_log`. Size: 80–150 lines. -/
theorem filter_series_aux {H : MvPolynomial (Fin 2) ℂ} {N : ℕ} {h : ℕ → ℕ → ℂ} (hrep : IsRisingRep H N h) :
    (∀ s : ℂ, 2 < s.re →
      Summable fun pq : Nat.Primes × Nat.Primes => ‖WHlog N h s (pq.1 : ℕ) (pq.2 : ℕ)‖) ∧
    (∀ s : ℂ, 2 < s.re → DH H s = Dser (WHlog N h) s) ∧
    DifferentiableOn ℂ (Dser (WHlog N h)) (halfPlane 2) ∧
    ∀ s ∈ Aff.idL.RL ∩ Aff.idL.DL, ∀ c : ℝ, 1 < c → c < (Aff.idL.app s).re - 1 →
      Dser (WHlog N h) s = VerticalIntegral' (fun z => kH H z s * Q z * Q (Aff.idL.app s - z)) c := by
  have heq (s : ℂ) (hs : 2 < s.re) (c : ℝ) (hc1 : 1 < c) (hc2 : c < s.re - 1) :
      Dser (WHlog N h) s = VerticalIntegral' (fun z => kH H z s * Q z * Q (s - z)) c := by
    change Dser (wtd (fun n => Real.log n) (Wrise N (cWH h))) s = _
    rw [(rising_summable_eq primeWeight_log N (cWH h) hs).2 c hc1 hc2 |>.2]
    apply E1_integral_congr
    intro y
    rw [kH_eq_krise hrep (by simp; linarith) (by simp; linarith)]
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hs
    exact (rising_summable_eq primeWeight_log N (cWH h) hs).1
  · intro s hs
    exact (heq s hs (s.re / 2) (by linarith) (by linarith)).symm
  · exact rising_differentiableOn primeWeight_log N (cWH h) (differentiableOn_cWH h)
  · intro s hs c hc1 hc2
    simp only [M4a.app_idL] at hc2 ⊢
    exact heq s (by simpa [Aff.RL, M4a.app_idL] using hs.1) c hc1 hc2

end GoldbachBoundaries.Paper2.M4b
