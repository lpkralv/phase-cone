import GoldbachBoundaries.Paper2.M1.Residue
import GoldbachBoundaries.Paper2.M1.Fill.Binf_le_Bsup_le_one
import GoldbachBoundaries.Paper2.M1.Fill.Bsup_attained
import GoldbachBoundaries.Paper2.M1.Fill.Bsup_facts
import GoldbachBoundaries.Paper2.M1.Fill.Bsup_lt_one_of_Hinf
import GoldbachBoundaries.Paper2.M1.Fill.Fdelta_spec
import GoldbachBoundaries.Paper2.M1.Fill.IcQ_congr
import GoldbachBoundaries.Paper2.M1.Fill.Ic_differentiableOn
import GoldbachBoundaries.Paper2.M1.Fill.Ic_sub_Ic
import GoldbachBoundaries.Paper2.M1.Fill.Qcont_conj
import GoldbachBoundaries.Paper2.M1.Fill.Rcoef_eq_finsum
import GoldbachBoundaries.Paper2.M1.Fill.Rcoef_inv
import GoldbachBoundaries.Paper2.M1.Fill.Rcoef_real_conj
import GoldbachBoundaries.Paper2.M1.Fill.T_differentiableOn
import GoldbachBoundaries.Paper2.M1.Fill.«T_eq_verticalIntegral'_KerS»
import GoldbachBoundaries.Paper2.M1.Fill.TcQ_congr
import GoldbachBoundaries.Paper2.M1.Fill.Tc_analyticAt
import GoldbachBoundaries.Paper2.M1.Fill.Tc_eq_T
import GoldbachBoundaries.Paper2.M1.Fill.Tc_indep
import GoldbachBoundaries.Paper2.M1.Fill.Tc_meromorphicAt
import GoldbachBoundaries.Paper2.M1.Fill.Tc_mono_delta
import GoldbachBoundaries.Paper2.M1.Fill.Tcont_conj
import GoldbachBoundaries.Paper2.M1.Fill.Tcont_props
import GoldbachBoundaries.Paper2.M1.Fill.conj_mem_poleSetQ
import GoldbachBoundaries.Paper2.M1.Fill.«differentiableOn_verticalIntegral'»
import GoldbachBoundaries.Paper2.M1.Fill.eventuallyEq_Tcont_of_codiscrete
import GoldbachBoundaries.Paper2.M1.Fill.exists_adm_reg
import GoldbachBoundaries.Paper2.M1.Fill.exists_goodHeight
import GoldbachBoundaries.Paper2.M1.Fill.finite_zeros_re_gt
import GoldbachBoundaries.Paper2.M1.Fill.finsum_nu_eq_pairSum
import GoldbachBoundaries.Paper2.M1.Fill.half_le_Binf
import GoldbachBoundaries.Paper2.M1.Fill.hasResidue_Qcont_Rcoef
import GoldbachBoundaries.Paper2.M1.Fill.hasResidue_Tc
import GoldbachBoundaries.Paper2.M1.Fill.hasResidue_Tcont
import GoldbachBoundaries.Paper2.M1.Fill.integrable_KerS_Q_line
import GoldbachBoundaries.Paper2.M1.Fill.isOpen_RegC
import GoldbachBoundaries.Paper2.M1.Fill.isQCont_eventuallyEq
import GoldbachBoundaries.Paper2.M1.Fill.mellin_one_add_cpow_neg
import GoldbachBoundaries.Paper2.M1.Fill.meromorphicOn_term
import GoldbachBoundaries.Paper2.M1.Fill.meromorphicOrderAt_Qcont_ge
import GoldbachBoundaries.Paper2.M1.Fill.meromorphicOrderAt_Qcont_neg_iff
import GoldbachBoundaries.Paper2.M1.Fill.norm_KerS_mul_pow_le
import GoldbachBoundaries.Paper2.M1.Fill.norm_Qcont_le_growth
import GoldbachBoundaries.Paper2.M1.Fill.norm_gs_le_far
import GoldbachBoundaries.Paper2.M1.Fill.norm_negLogDerivZeta_le_strip
import GoldbachBoundaries.Paper2.M1.Fill.norm_sigmaTail_two_le
import GoldbachBoundaries.Paper2.M1.Fill.not_mem_poleSetQ_of_goodHeight
import GoldbachBoundaries.Paper2.M1.Fill.«one_add_cpow_neg_eq_verticalIntegral'»
import GoldbachBoundaries.Paper2.M1.Fill.pairSum_one_add
import GoldbachBoundaries.Paper2.M1.Fill.pinchPairs_finite
import GoldbachBoundaries.Paper2.M1.Fill.pinchPairs_one_add_subset
import GoldbachBoundaries.Paper2.M1.Fill.pinch_locallyFinite
import GoldbachBoundaries.Paper2.M1.Fill.poleSetQ_locallyFinite
import GoldbachBoundaries.Paper2.M1.Fill.poleSetQ_re_bounds
import GoldbachBoundaries.Paper2.M1.Fill.poleSetQ_re_le_Bsup
import GoldbachBoundaries.Paper2.M1.Fill.sum_zetaMult_window_le
import GoldbachBoundaries.Paper2.M1.Fill.«verticalIntegral'_eq_add_sum_of_simplePoles»

/-!
# M1: the 56 lemmas, assembled

Imports the proof of each of the 56 lemmas of `QnoRH`, `BNumbers`, `Kernel`, `Growth`, `Shift`, `Cont` and
`Residue` (`Fill/<name>.lean`, one theorem `<name>` per file, statement verbatim from the skeleton, the skeleton's
sketch as its docstring), with the helper files `Fill/ACommon`, `BCommon`, `KernelCommon`, `E1Common`, `E2Common`.
The skeleton files keep only the real lemmas that use none of the 56 (`Rcoef_one'`, `AdmC.Binf_lt_one`,
`KerS_sub_symm`). The real lemmas that use one of the 56 sit at the end of the fill file of the lemma they use:
`isQCont_order_ge` in `Fill/isQCont_eventuallyEq.lean`, `conj_mem_Pinch` in `Fill/conj_mem_poleSetQ.lean`,
`Tcont_eq_Tc` in `Fill/Tc_indep.lean`, `Tcont_eqOn_T` in `Fill/Tc_eq_T.lean`, `halfPlane_two_Binf_subset` in
`Fill/half_le_Binf.lean`. `Skeleton.lean` imports this file.
-/
