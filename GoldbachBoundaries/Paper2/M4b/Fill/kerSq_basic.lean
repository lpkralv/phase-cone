import GoldbachBoundaries.Paper2.M4b.Fill.DCommon

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M4b

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/- Filler for `kerSq_basic` (`Kernels.lean`). -/

/-- `kerSq` is jointly holomorphic on `{σ > 1/2, 0 < Re z < 2σ}` (the domain of (H2a) for `L(s) = 2s`). -/
lemma FillD.kerSq_H2a : H2a Aff.twoL kerSq := by
  rintro ⟨z, s⟩ ⟨hs, hz0, hz1⟩
  have hs' : 1 < 2 * s.re := by simpa [Aff.HL, twoL_app] using hs
  have hz1' : z.re < 2 * s.re := by simpa [twoL_app] using hz1
  have hz0' : 0 < z.re := hz0
  have hd1 : DifferentiableAt ℂ (fun q : ℂ × ℂ => Gamma (q.1 / 2)) (z, s) :=
    (FillD.differentiableAt_Gamma_of_re_pos (w := z / 2) (by simp; linarith)).comp (z, s)
      (by fun_prop)
  have hd2 : DifferentiableAt ℂ (fun q : ℂ × ℂ => Gamma (q.2 - q.1 / 2)) (z, s) :=
    (FillD.differentiableAt_Gamma_of_re_pos (w := s - z / 2) (by simp; linarith)).comp (z, s)
      (by fun_prop)
  have hd3 : DifferentiableAt ℂ (fun q : ℂ × ℂ => Gamma q.2) (z, s) :=
    (FillD.differentiableAt_Gamma_of_re_pos (w := s) (by linarith)).comp (z, s) differentiableAt_snd
  have hne : Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
  refine DifferentiableAt.differentiableWithinAt ?_
  show DifferentiableAt ℂ (fun q : ℂ × ℂ => (1 / 2) * Gamma (q.1 / 2) * Gamma (q.2 - q.1 / 2) / Gamma q.2) (z, s)
  simp only [div_eq_mul_inv _ (Gamma _)]
  exact ((hd1.const_mul _).mul hd2).mul (hd3.inv hne)

/-- **(K1), (H2a), (K3) for `∑(p²+q²)^{-s}`**. On `{σ > 1/2, 0 < Re z < 2σ}` (`domH2a`, which contains `domK1`):
`Re(z/2) > 0`, `Re(s - z/2) > 0`, `Re s > 0`, so `Γ(z/2)`, `Γ(s - z/2)`, `1/Γ(s)` are holomorphic there (as
`differentiableOn_kerG'` in Defs). (K3): `Γ(conj w) = conj Γ(w)` (`Complex.Gamma_conj`), `conj(z/2) = conj z/2`. Size:
60–120 lines. -/
theorem kerSq_basic : K1 Aff.twoL kerSq ∧ H2a Aff.twoL kerSq ∧ K3 Aff.twoL kerSq := by
  refine ⟨FillD.kerSq_H2a.mono ?_, FillD.kerSq_H2a, ?_⟩
  · rintro ⟨z, s⟩ ⟨hs, hz⟩
    exact ⟨hs.1, hz⟩
  · intro s _ z _
    simp only [kerSq, map_div₀, map_mul, ← Complex.Gamma_conj, map_sub, map_one, map_ofNat]

end GoldbachBoundaries.Paper2.M4b
