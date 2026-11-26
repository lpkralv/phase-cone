import GoldbachBoundaries.Paper2.M4a.H3

/-!
# M4a skeleton: the targets of Milestone M4a (the kernel class of Section 4: basics)

Each `*_proof` theorem has the statement of the theorem of the same name (without `_proof`) in
`Paper2/Statements.lean`, copied verbatim, and a real proof from the M4a lemmas (and M1, paper 1); no target has a
`sorry` of its own. A target that a later file uses is proved at the end of its own file, in the dependency order
`Defs → Catalogue → Coeff → Jseg → H2log → Order → Kernel → Restrict → H3 → Skeleton`:

| Target | File |
|---|---|
| `prop_catalogue_i_proof`, `prop_catalogue_ii_proof` | `Catalogue.lean` |
| `lem_P_iv_values_proof` | `Coeff.lean` |
| `lem_J_i_proof`, `lem_J_ii_proof` | `Jseg.lean` |
| `H2log_of_H2a_proof`, `H2log_of_H2b_proof` | `H2log.lean` |
| `rem_order_kr_coeff_proof`, `rem_order_coeff_proof` | `Order.lean` |
| `lem_kernelt_proof`, `rem_order_kr_K2_proof` | `Kernel.lean` |
| `thm_class_H3_of_bracket_proof`, `thm_class_H3_of_K4_proof`, `rem_order_H3_proof` | `H3.lean` |

The type match is checked by `example : type_of% @GoldbachBoundaries.Paper2.X := @GoldbachBoundaries.Paper2.M4a.X_proof`
from a scratch file that imports both (this file does not import `Paper2/Statements.lean`). Once every M4a lemma is
filled, each of the 14 statements closes by `exact M4a.X_proof ...`, and `rem_order_kr_coeff_ne` (already proved from
`lem_P_iv_values` in `Paper2/Statements.lean`) becomes sorry-free.

**Changes of proof (statements unchanged).**
1. **Restriction of (K4) to a line by transverse Taylor coefficients** (`Restrict.lean`), not by "`v` not identically
   zero on the line", which can fail for non-coprime local quotients.
2. **The orders at `1 + b` without the symmetry `J_{b1} = J_{1b}`**: both segment integrals are expanded directly
   (`isBigO_Jseg_kr_one_b`, `isBigO_Jseg_kr_b_one`) through one first-order lemma for parametric integrals
   (`isBigO_integral_param`); `rem_order_coeff` at `1 + b` is `rem_order_kr_coeff` at `r = 1` (`kr_one'`).
3. **One (H3) criterion for three targets** (`H3_of_eventually`): `thm_class_H3_of_bracket`, `thm_class_H3_of_K4` and
   `rem_order_H3` differ only in why `X_α ≢ 0` at the scaled-zero pinches near the line.
4. **No (Z2) in the density step** (review choice 9): paper 1's `lem_density`, through `infinite_scaledZeros_near`.
5. **`1/Γ` on vertical strips by reflection and (Z6)** (`norm_inv_Gamma_le`) instead of the product formula.

Unused premises (RH in `lem_kernelt`, `rem_order_kr_K2`, `rem_order_kr_coeff`, review choice 1; the
`r ≥ 1` of `rem_order_kr_coeff`) are consumed by `have _ := ...` with a comment, as in M1–M3.
-/
