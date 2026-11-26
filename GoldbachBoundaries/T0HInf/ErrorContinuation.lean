import GoldbachBoundaries.T0HInf.ErrorBounds
import GoldbachBoundaries.T0HInf.RemainderTransform

/-! The finite exceptional-zero shifts preserve meromorphy across the boundary. -/
noncomputable section
open Complex Filter Topology Set Metric MeasureTheory
namespace GoldbachBoundaries.T0HInf
open GoldbachBoundaries Paper2
open _root_.GoldbachBoundaries.Phi2HInf (StirlingStrip)

lemma meromorphicOn_W_aux (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3)
    (hStir : StirlingStrip) {E : Finset NontrivialZeros} (hE : IsCutoff E) :
    MeromorphicOn (W E) (halfPlane crossingAbscissa) := by
  intro s hs
  have hB : Bsup < s.re := (le_max_left _ _).trans_lt hs
  have hHreg : remainderAbscissa + cutoffAbscissa < s.re := (le_max_right _ _).trans_lt hs
  have hE2 := (differentiable_E2.analyticAt s).meromorphicAt
  have hp : MeromorphicAt (fun z : ℂ => primeSquareCoef ^ 2 / (z - 1)) s :=
    (MeromorphicAt.const _ _).div (analyticAt_id.sub analyticAt_const).meromorphicAt
  have hC : MeromorphicAt (fun z : ℂ => 2 * primeSquareCoef * singleC (z - 1 / 2)) s :=
    (MeromorphicAt.const _ _).mul ((meromorphicOn_singleC hZ1 hZ2 _ (mem_univ _)).comp_analyticAt
      (g := fun z : ℂ => z - 1 / 2) (by fun_prop))
  have hsum : MeromorphicAt (fun z : ℂ => ∑ ρ ∈ E, zeroCoef ρ * Rhat (z - ρ)) s := by
    apply MeromorphicAt.fun_sum
    intro ρ hρ
    have hz : s - ρ ∈ halfPlane 0 := by
      change 0 < (s - ρ).re
      rw [sub_re]
      linarith [(M1.Bsup_facts hZ1).1 ρ ρ.2]
    exact (MeromorphicAt.const _ _).mul
      ((meromorphicOn_Rhat hZ1 hZ2 _ hz).comp_analyticAt (g := fun z : ℂ => z - ρ) (by fun_prop))
  have hHolo := ((differentiableOn_H hH hZ1 hZ2 hZ3 hStir hE).analyticOnNhd
    (isOpen_halfPlane _) s hHreg).meromorphicAt
  change MeromorphicAt (fun z => E2 z + primeSquareCoef ^ 2 / (z - 1) +
    2 * primeSquareCoef * singleC (z - 1 / 2) + 2 * (∑ ρ ∈ E, zeroCoef ρ * Rhat (z - ρ)) + H E z) s
  exact (((hE2.add hp).add hC).add ((MeromorphicAt.const _ _).mul hsum)).add hHolo

end GoldbachBoundaries.T0HInf
