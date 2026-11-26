import GoldbachBoundaries.Paper2.M4b.SeriesS

/-!
# M4b skeleton: the targets of Milestone M4b (Theorem E and the hypothesis checks of Section 4)

Each `*_proof` theorem has the statement of the theorem of the same name (without `_proof`) in
`Paper2/Statements.lean`, copied verbatim, and a real proof from the M4b lemmas (and M1, M2, M4a, paper 1); no target
has a `sorry` of its own. A target that a later file uses is proved at the end of its own file, in the dependency order
`Defs → MB → Rising → Mero → Boundary → Kernels → ExG → T0 → Squares → SeriesS → Skeleton`:

| Target | File |
|---|---|
| `thm_mero_i_proof`, `thm_mero_ii_proof` | `Mero.lean` |
| `thm_mero_iii_proof` | `Boundary.lean` |
| `ex_T_hyp_proof`, `ex_G_hyp_proof` | `ExG.lean` |
| `prop_T0_proof`, `filter_series_proof`, `filter_series_real_proof` | `T0.lean` |
| `ex_squares_hyp_proof` | `Squares.lean` |
| `ex_S_hyp_proof` | `SeriesS.lean` |

The type match is checked by `example : type_of% @GoldbachBoundaries.Paper2.X := @GoldbachBoundaries.Paper2.M4b.X_proof`
from a scratch file that imports both (this file does not import `Paper2/Statements.lean`). Once every M4b lemma is
filled, each of the 10 statements closes by `exact M4b.X_proof ...`, and `intro_T_strip` (already proved from
`thm_mero_i`, `ex_T_hyp` and `bracket_kerG` in `Paper2/Statements.lean`) becomes sorry-free.

**Changes of proof (statements unchanged).**
1. **One Mellin–Barnes lemma for every weight** (`MB.lean`): `∑ ω(p)ω(q) q^{-L} f(p/q) = (1/2πi)∫ k · F · F(L - ·)`
   for any Mellin pair `(f, k)` and prime weight `ω` (`P` or `Q`), with the absolute convergence of the series as a
   by-product. The six (R)'s use two families of Mellin pairs: `t^i(1+t)^{-(s+i+j)}` (the rising combinations
   `W_G`, `W₀`, `W_H`, `Rising.lean`) and `t^μ(1+t²)^{-ν}` (`∑(p²+q²)^{-s}`, `S`). The AM-GM step of `cl:ex:S` is not
   needed.
2. **Theorem E through one glued function** (`Fmero`, `Defs.lean`) instead of "continues ... as a single-valued
   meromorphic function": the series on `R_L`, `(cl:eq:Iplus)` on `3/2 < Re L ≤ 2`, `(cl:eq:strip)` on `Re L ≤ 3/2`.
   Every admissible continuation equals it near every point of `ℍ_L` (`eventuallyEq_Fmero`).
3. **Theorem E(ii) by removable singularities** (`exists_differentiableOn_of_order_nonneg`): `Fmero` itself is not
   holomorphic at `s₂` (its value there is `I⁺(s₂) + 0·Q(1)`, Lean's junk), so the holomorphic `F` is its normal form.
4. **Under RH, paper 1's `Q`-bounds** (`norm_Qcont_le_log`, `analyticAt_Qcont_of_RH`): Theorem E's (Z1)-(Z3), and
   the (Z6) of `filter_series(_real)`, are not used.
5. **Reality of `D_H` from the integral** (`im_DH_eq_zero`, symmetric line `c = x/2`), not from the coefficients
   `h_{ij}`.
6. **(H3) for `S` at `s = ½`**: the paper's `𝔟(0) ≠ 0` is at a point of the boundary line, outside `D_L`; M4a's
   `thm_class_H3_of_K4_proof` needs a point of `D_L`, and `𝔟(½) = K(¾) = Γ(¾)Γ(5/4) ≠ 0`.

Unused premises (RH in `ex_T_hyp`, `filter_series(_real)`, review choice 1; (Z1)-(Z3) in Theorem E; (Z6) and the
conditions on `H` in `filter_series(_real)`) are consumed by `have _ := ...` with a comment, as in M1–M4a.
-/
