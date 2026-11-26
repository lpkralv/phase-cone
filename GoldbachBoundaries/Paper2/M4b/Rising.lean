import GoldbachBoundaries.Paper2.M4b.MB
import GoldbachBoundaries.Paper2.M4b.Fill.rising_summable_eq
import GoldbachBoundaries.Paper2.M4b.Fill.rising_differentiableOn
import GoldbachBoundaries.Paper2.M4b.Fill.W0_k0_rising
import GoldbachBoundaries.Paper2.M4b.Fill.kH_eq_krise

/-!
# M4b: (R) for the combinations `∑ c_{ij}(s) p^i q^j (p+q)^{-s-i-j}` (`L(s) = s`)

The proof of `cl:prop:T0` and the first remark after `cl:thm:filter` use one computation: the kernel of
`p^i q^j (p+q)^{-s-i-j}` is `Γ(z+i)Γ(s-z+j)/Γ(s+i+j)`. In the form of `MB.lean`: `p^i q^j (p+q)^{-s-i-j} =
q^{-s} f(p/q)` with `f(t) = t^i(1+t)^{-(s+i+j)}`, whose kernel is `kMB 1 i (s+i+j) z = K_{s+i+j}(z+i)`. Summing over
`i, j < N` with coefficients `c_{ij}(s)` gives (R) (all but reality) for `Wrise N cf` and `krise N cf`, with `P`
(`ω = 1`) or `Q` (`ω = log`). The weights `W_G = (p+q)^{-s}` (`N = 1`, `c = 1`), `W₀` (`N = 2`, `cW0`) and `W_H`
(`cWH h`, definitionally) are instances; their kernels `K_s`, `k₀`, `k_H` equal `krise` on the lines used.
-/

noncomputable section

open Complex Filter Topology Set Metric ComplexConjugate MeasureTheory Asymptotics

namespace GoldbachBoundaries.Paper2.M4b

open GoldbachBoundaries GoldbachBoundaries.Paper2 GoldbachBoundaries.Paper2.M1

/-! ## Lemmas

Proved in `Fill/`, one file per lemma (same name, same statement): `rising_summable_eq`, `rising_differentiableOn`, `W0_k0_rising`, `kH_eq_krise`. -/

/-! ## Real lemmas -/

lemma WG_eq_Wrise (s : ℂ) (p q : ℕ) : WG s p q = Wrise 1 (fun _ _ _ => 1) s p q := by
  simp [WG, Wrise]

lemma kerG_eq_krise (z s : ℂ) : kerG z s = krise 1 (fun _ _ _ => 1) z s := by
  simp [kerG, krise, KerS]

lemma differentiableOn_one_cf (i j : ℕ) :
    DifferentiableOn ℂ ((fun _ _ _ => (1 : ℂ)) i j) (halfPlane 2) :=
  differentiableOn_const _

lemma differentiableOn_cW0 (i j : ℕ) : DifferentiableOn ℂ (cW0 i j) (halfPlane 2) := by
  unfold cW0
  split_ifs <;> fun_prop

lemma differentiableOn_cWH (h : ℕ → ℕ → ℂ) (i j : ℕ) : DifferentiableOn ℂ (cWH h i j) (halfPlane 2) := by
  intro s hs
  have hs' : 2 < s.re := hs
  have hG : ∀ w : ℂ, 0 < w.re → DifferentiableAt ℂ Gamma w := fun w hw =>
    differentiableAt_Gamma _ (fun m h => by rw [h] at hw; simp at hw; linarith [(m.cast_nonneg : (0:ℝ) ≤ m)])
  have h1 : DifferentiableAt ℂ (fun s : ℂ => Gamma (s + i + j)) s :=
    (hG _ (by simp; positivity)).comp s (by fun_prop)
  have h2 : DifferentiableAt ℂ Gamma s := hG s (by linarith)
  have h3 : Gamma s ≠ 0 := Gamma_ne_zero_of_re_pos (by linarith)
  exact ((differentiableAt_const _).mul (h1.div h2 h3)).differentiableWithinAt

end GoldbachBoundaries.Paper2.M4b
