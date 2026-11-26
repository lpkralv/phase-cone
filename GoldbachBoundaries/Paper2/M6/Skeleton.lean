import GoldbachBoundaries.Paper2.M6.ExG

/-!
# M6 skeleton: the targets of Milestone M6 (`cl:lem:P`, `cl:ex:G`)

Each `*_proof` theorem has the statement of the theorem of the same name (without `_proof`) in
`Paper2/Statements.lean`, copied verbatim, and a real proof from the M6 lemmas (and M1-M5, paper 1); no target has a
`sorry` of its own. Dependency order `Defs → Omega → Ptil → Branch → Local → Sheet → ExG → Skeleton`:

| Target | File |
|---|---|
| `lem_P_i_proof` | `Omega.lean` |
| `lem_P_ii_proof` | `Ptil.lean` |
| `lem_P_iii_proof` | `Branch.lean` |
| `lem_P_iv_proof` | `Local.lean` |
| `lem_P_v_proof`, `lem_P_vi_proof` | `Sheet.lean` |
| `ex_G_proof` | `ExG.lean` |

The type match is checked by `example : type_of% @GoldbachBoundaries.Paper2.X := @GoldbachBoundaries.Paper2.M6.X_proof`
from a scratch file that imports both (this file does not import `Paper2/Statements.lean`). Once every M6 lemma is
filled, each of the 7 statements closes by `exact M6.X_proof ...`.

**Changes of proof (statements unchanged).**
1. **`P̃` as an explicit formula** `P̃(z) = P(z + 2) + ∫_0^2 Q(z + t) dt` (`Ptil`), using only that eastward rays stay in
   `Ω`; no path integral over `Ω` and no monodromy theorem for (ii). Simple connectivity is still proved for (i)
   (contractibility by the paper's deformation).
2. **(iii) through paper 1's G13**: the germs with `-f' = Q` form a uniform family (`uniformFamily_PBranchFam`), and
   `ThmA.exists_continuationAlong_of_uniform` continues them; the derivative clause is M2's
   `neg_deriv_eventuallyEq_Qcont_of_isPBranch`.
3. **(v) with paper 1's `E`** (`ThmA.Eaux`) as `E₁`, and **(vi) from (v) and paper 1's `ThmA.norm_Eaux_le`** instead of
   `nr:lem:growthQ`: (Z1)-(Z3) are not used.
4. **`ex_G` from paper 1's Theorem A**, not from `cl:thm:class`: the coefficient is identified as a function
   (`Xcoef_idL_kerG_eq_X`), and the local model is moved from paper 1's slanted slit to the leftward slit
   (`local_form_slitDiscL_of_slitDisc`). Only RH is used.

Unused premises are consumed by `have _ := ...` with a comment, as in M1–M5.
-/
