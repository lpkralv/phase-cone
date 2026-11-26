import GoldbachBoundaries.Phi2HInf.Proof.M2Catalogue

noncomputable section
open Complex Filter Topology Set Metric
namespace GoldbachBoundaries.Phi2HInf
open GoldbachBoundaries Paper2

theorem phi2_hinf_continuation (hH : Hinf) (hZ1 : Z1) (hZ2 : Z2) (hZ3 : Z3)
    (hStir : StirlingStrip) : MeromorphicOn Phi2cHInf HH ∧ EqOn Phi2cHInf Phi2 (halfPlane 2) := by
  refine ⟨?_, phi2_reg_identity hZ1 hZ2 hZ3 hStir⟩
  intro s hs
  have hsA : s ∈ halfPlane (1 / 2) := by
    change 1 / 2 < s.re
    have : 1 < s.re := hs
    linarith
  have hA := ((differentiableOn_A hZ1 hZ2 hZ3 hStir).analyticOnNhd
    (isOpen_halfPlane (1 / 2)) s hsA).meromorphicAt
  have hΓ := (differentiable_one_div_Gamma.analyticAt s).meromorphicAt
  have hm := (meromorphicOn_M0 hZ1 hZ2 hStir s (mem_univ _)).add
    (((meromorphicOn_C_hinf hH hZ1 hZ2 hStir s hs).add hA).mul hΓ)
  convert hm using 1
  ext z
  simp only [Phi2cHInf, Pi.add_apply, Pi.mul_apply, div_eq_mul_inv]


end GoldbachBoundaries.Phi2HInf
