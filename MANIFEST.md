# Lean source manifest

The three papers cite declarations in 41 local source modules. Following their imports yields 652 modules, plus the new `GoldbachBoundaries` entry point. The three `Check.lean` files are separate check programs.

The Lake toolchain and dependency lockfile match the source project. The release configuration lists `GoldbachBoundaries` as its only library and default target. The copied Lean modules keep their paths, declarations and proofs. Release edits remove private references from source comments.

| Paper | Modules with cited declarations | Local modules in import closure |
| --- | ---: | ---: |
| [phase-cone](phase-cone/README.md) | 8 | 487 |
| [t0-boundary](t0-boundary/README.md) | 14 | 626 |
| [class-one](class-one/README.md) | 30 | 623 |

| Source group under `GoldbachBoundaries/` | Modules |
| --- | ---: |
| `(top level)` | 11 |
| `Paper2` | 387 |
| `PhaseCone` | 2 |
| `Phi2` | 45 |
| `Phi2HInf` | 45 |
| `PhiR` | 25 |
| `ResidueClass` | 25 |
| `T0HInf` | 31 |
| `TIdentity` | 17 |
| `ThmA` | 64 |

## Module list

● marks a module containing a cited declaration. ✓ marks a module reached through imports. Restated sector results are included for the papers that use them.

| Module | Phase cone | T₀ boundary | Class one |
| --- | :---: | :---: | :---: |
| [`GoldbachBoundaries`](GoldbachBoundaries.lean) | | | |
| [`GoldbachBoundaries.BoundaryLemma`](GoldbachBoundaries/BoundaryLemma.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Defs`](GoldbachBoundaries/Defs.lean) | ● | ● | ● |
| [`GoldbachBoundaries.Density`](GoldbachBoundaries/Density.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.LogDerivZeta`](GoldbachBoundaries/LogDerivZeta.lean) | ✓ | ✓ | ● |
| [`GoldbachBoundaries.Paper2.Defs`](GoldbachBoundaries/Paper2/Defs.lean) | ✓ | ● | ● |
| [`GoldbachBoundaries.Paper2.M1.Assembly`](GoldbachBoundaries/Paper2/M1/Assembly.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.BNumbers`](GoldbachBoundaries/Paper2/M1/BNumbers.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Cont`](GoldbachBoundaries/Paper2/M1/Cont.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Defs`](GoldbachBoundaries/Paper2/M1/Defs.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Fill.ACommon`](GoldbachBoundaries/Paper2/M1/Fill/ACommon.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Fill.BCommon`](GoldbachBoundaries/Paper2/M1/Fill/BCommon.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Fill.Binf_le_Bsup_le_one`](GoldbachBoundaries/Paper2/M1/Fill/Binf_le_Bsup_le_one.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Fill.Bsup_attained`](GoldbachBoundaries/Paper2/M1/Fill/Bsup_attained.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Fill.Bsup_facts`](GoldbachBoundaries/Paper2/M1/Fill/Bsup_facts.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Fill.Bsup_lt_one_of_Hinf`](GoldbachBoundaries/Paper2/M1/Fill/Bsup_lt_one_of_Hinf.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Fill.E1Common`](GoldbachBoundaries/Paper2/M1/Fill/E1Common.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Fill.E2Common`](GoldbachBoundaries/Paper2/M1/Fill/E2Common.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Fill.Fdelta_spec`](GoldbachBoundaries/Paper2/M1/Fill/Fdelta_spec.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Fill.IcQ_congr`](GoldbachBoundaries/Paper2/M1/Fill/IcQ_congr.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Fill.Ic_differentiableOn`](GoldbachBoundaries/Paper2/M1/Fill/Ic_differentiableOn.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Fill.Ic_sub_Ic`](GoldbachBoundaries/Paper2/M1/Fill/Ic_sub_Ic.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Fill.KernelCommon`](GoldbachBoundaries/Paper2/M1/Fill/KernelCommon.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Fill.Qcont_conj`](GoldbachBoundaries/Paper2/M1/Fill/Qcont_conj.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Fill.Rcoef_eq_finsum`](GoldbachBoundaries/Paper2/M1/Fill/Rcoef_eq_finsum.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Fill.Rcoef_inv`](GoldbachBoundaries/Paper2/M1/Fill/Rcoef_inv.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Fill.Rcoef_real_conj`](GoldbachBoundaries/Paper2/M1/Fill/Rcoef_real_conj.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Fill.T_differentiableOn`](GoldbachBoundaries/Paper2/M1/Fill/T_differentiableOn.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Fill.T_eq_verticalIntegral'_KerS`](GoldbachBoundaries/Paper2/M1/Fill/T_eq_verticalIntegral'_KerS.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Fill.TcQ_congr`](GoldbachBoundaries/Paper2/M1/Fill/TcQ_congr.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Fill.Tc_analyticAt`](GoldbachBoundaries/Paper2/M1/Fill/Tc_analyticAt.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Fill.Tc_eq_T`](GoldbachBoundaries/Paper2/M1/Fill/Tc_eq_T.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Fill.Tc_indep`](GoldbachBoundaries/Paper2/M1/Fill/Tc_indep.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Fill.Tc_meromorphicAt`](GoldbachBoundaries/Paper2/M1/Fill/Tc_meromorphicAt.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Fill.Tc_mono_delta`](GoldbachBoundaries/Paper2/M1/Fill/Tc_mono_delta.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Fill.Tcont_conj`](GoldbachBoundaries/Paper2/M1/Fill/Tcont_conj.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Fill.Tcont_props`](GoldbachBoundaries/Paper2/M1/Fill/Tcont_props.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Fill.conj_mem_poleSetQ`](GoldbachBoundaries/Paper2/M1/Fill/conj_mem_poleSetQ.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Fill.differentiableOn_verticalIntegral'`](GoldbachBoundaries/Paper2/M1/Fill/differentiableOn_verticalIntegral'.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Fill.eventuallyEq_Tcont_of_codiscrete`](GoldbachBoundaries/Paper2/M1/Fill/eventuallyEq_Tcont_of_codiscrete.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Fill.exists_adm_reg`](GoldbachBoundaries/Paper2/M1/Fill/exists_adm_reg.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Fill.exists_goodHeight`](GoldbachBoundaries/Paper2/M1/Fill/exists_goodHeight.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Fill.finite_zeros_re_gt`](GoldbachBoundaries/Paper2/M1/Fill/finite_zeros_re_gt.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Fill.finsum_nu_eq_pairSum`](GoldbachBoundaries/Paper2/M1/Fill/finsum_nu_eq_pairSum.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Fill.half_le_Binf`](GoldbachBoundaries/Paper2/M1/Fill/half_le_Binf.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Fill.hasResidue_Qcont_Rcoef`](GoldbachBoundaries/Paper2/M1/Fill/hasResidue_Qcont_Rcoef.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Fill.hasResidue_Tc`](GoldbachBoundaries/Paper2/M1/Fill/hasResidue_Tc.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Fill.hasResidue_Tcont`](GoldbachBoundaries/Paper2/M1/Fill/hasResidue_Tcont.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Fill.integrable_KerS_Q_line`](GoldbachBoundaries/Paper2/M1/Fill/integrable_KerS_Q_line.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Fill.isOpen_RegC`](GoldbachBoundaries/Paper2/M1/Fill/isOpen_RegC.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Fill.isQCont_eventuallyEq`](GoldbachBoundaries/Paper2/M1/Fill/isQCont_eventuallyEq.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Fill.mellin_one_add_cpow_neg`](GoldbachBoundaries/Paper2/M1/Fill/mellin_one_add_cpow_neg.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Fill.meromorphicOn_term`](GoldbachBoundaries/Paper2/M1/Fill/meromorphicOn_term.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Fill.meromorphicOrderAt_Qcont_ge`](GoldbachBoundaries/Paper2/M1/Fill/meromorphicOrderAt_Qcont_ge.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Fill.meromorphicOrderAt_Qcont_neg_iff`](GoldbachBoundaries/Paper2/M1/Fill/meromorphicOrderAt_Qcont_neg_iff.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Fill.norm_KerS_mul_pow_le`](GoldbachBoundaries/Paper2/M1/Fill/norm_KerS_mul_pow_le.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Fill.norm_Qcont_le_growth`](GoldbachBoundaries/Paper2/M1/Fill/norm_Qcont_le_growth.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Fill.norm_gs_le_far`](GoldbachBoundaries/Paper2/M1/Fill/norm_gs_le_far.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Fill.norm_negLogDerivZeta_le_strip`](GoldbachBoundaries/Paper2/M1/Fill/norm_negLogDerivZeta_le_strip.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Fill.norm_sigmaTail_two_le`](GoldbachBoundaries/Paper2/M1/Fill/norm_sigmaTail_two_le.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Fill.not_mem_poleSetQ_of_goodHeight`](GoldbachBoundaries/Paper2/M1/Fill/not_mem_poleSetQ_of_goodHeight.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Fill.one_add_cpow_neg_eq_verticalIntegral'`](GoldbachBoundaries/Paper2/M1/Fill/one_add_cpow_neg_eq_verticalIntegral'.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Fill.pairSum_one_add`](GoldbachBoundaries/Paper2/M1/Fill/pairSum_one_add.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Fill.pinchPairs_finite`](GoldbachBoundaries/Paper2/M1/Fill/pinchPairs_finite.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Fill.pinchPairs_one_add_subset`](GoldbachBoundaries/Paper2/M1/Fill/pinchPairs_one_add_subset.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Fill.pinch_locallyFinite`](GoldbachBoundaries/Paper2/M1/Fill/pinch_locallyFinite.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Fill.poleSetQ_locallyFinite`](GoldbachBoundaries/Paper2/M1/Fill/poleSetQ_locallyFinite.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Fill.poleSetQ_re_bounds`](GoldbachBoundaries/Paper2/M1/Fill/poleSetQ_re_bounds.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Fill.poleSetQ_re_le_Bsup`](GoldbachBoundaries/Paper2/M1/Fill/poleSetQ_re_le_Bsup.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Fill.sum_zetaMult_window_le`](GoldbachBoundaries/Paper2/M1/Fill/sum_zetaMult_window_le.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Fill.verticalIntegral'_eq_add_sum_of_simplePoles`](GoldbachBoundaries/Paper2/M1/Fill/verticalIntegral'_eq_add_sum_of_simplePoles.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Growth`](GoldbachBoundaries/Paper2/M1/Growth.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Kernel`](GoldbachBoundaries/Paper2/M1/Kernel.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.QnoRH`](GoldbachBoundaries/Paper2/M1/QnoRH.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Residue`](GoldbachBoundaries/Paper2/M1/Residue.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Shift`](GoldbachBoundaries/Paper2/M1/Shift.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M1.Skeleton`](GoldbachBoundaries/Paper2/M1/Skeleton.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M2.Boundary`](GoldbachBoundaries/Paper2/M2/Boundary.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M2.Defs`](GoldbachBoundaries/Paper2/M2/Defs.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M2.Far`](GoldbachBoundaries/Paper2/M2/Far.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M2.Fill.ACommon`](GoldbachBoundaries/Paper2/M2/Fill/ACommon.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M2.Fill.BCommon`](GoldbachBoundaries/Paper2/M2/Fill/BCommon.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M2.Fill.Binf_eq_half_of_Hinf`](GoldbachBoundaries/Paper2/M2/Fill/Binf_eq_half_of_Hinf.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M2.Fill.Nzero_le_mul_log`](GoldbachBoundaries/Paper2/M2/Fill/Nzero_le_mul_log.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M2.Fill.Rcoef_div_of_isSingleRep`](GoldbachBoundaries/Paper2/M2/Fill/Rcoef_div_of_isSingleRep.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M2.Fill.SH_finite_ncard_le`](GoldbachBoundaries/Paper2/M2/Fill/SH_finite_ncard_le.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M2.Fill.cor_LW_branch`](GoldbachBoundaries/Paper2/M2/Fill/cor_LW_branch.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M2.Fill.cor_LW_ext`](GoldbachBoundaries/Paper2/M2/Fill/cor_LW_ext.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M2.Fill.den_div_two_mul_prime`](GoldbachBoundaries/Paper2/M2/Fill/den_div_two_mul_prime.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M2.Fill.eventuallyEq_codiscreteWithin_of_nhdsNE`](GoldbachBoundaries/Paper2/M2/Fill/eventuallyEq_codiscreteWithin_of_nhdsNE.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M2.Fill.eventually_four_mul_log_le`](GoldbachBoundaries/Paper2/M2/Fill/eventually_four_mul_log_le.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M2.Fill.eventually_le_sq_div_log_sq`](GoldbachBoundaries/Paper2/M2/Fill/eventually_le_sq_div_log_sq.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M2.Fill.eventually_nearBad_small`](GoldbachBoundaries/Paper2/M2/Fill/eventually_nearBad_small.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M2.Fill.exists_imagAxis_mem`](GoldbachBoundaries/Paper2/M2/Fill/exists_imagAxis_mem.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M2.Fill.far_tail`](GoldbachBoundaries/Paper2/M2/Fill/far_tail.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M2.Fill.far_tail_numeric`](GoldbachBoundaries/Paper2/M2/Fill/far_tail_numeric.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M2.Fill.ncard_far_shell_le`](GoldbachBoundaries/Paper2/M2/Fill/ncard_far_shell_le.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M2.Fill.ncard_lineZeros_window_ge`](GoldbachBoundaries/Paper2/M2/Fill/ncard_lineZeros_window_ge.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M2.Fill.ncard_notGood_le`](GoldbachBoundaries/Paper2/M2/Fill/ncard_notGood_le.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M2.Fill.ncard_primes_window_ge`](GoldbachBoundaries/Paper2/M2/Fill/ncard_primes_window_ge.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M2.Fill.ncard_zeros_im_Icc_le`](GoldbachBoundaries/Paper2/M2/Fill/ncard_zeros_im_Icc_le.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M2.Fill.ncard_zeros_le_Nzero`](GoldbachBoundaries/Paper2/M2/Fill/ncard_zeros_le_Nzero.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M2.Fill.nearBad_finite_ncard_le`](GoldbachBoundaries/Paper2/M2/Fill/nearBad_finite_ncard_le.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M2.Fill.neg_deriv_eventuallyEq_Qcont_of_isPBranch`](GoldbachBoundaries/Paper2/M2/Fill/neg_deriv_eventuallyEq_Qcont_of_isPBranch.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M2.Fill.norm_Rcoef_le_log`](GoldbachBoundaries/Paper2/M2/Fill/norm_Rcoef_le_log.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M2.Fill.norm_far_term_le`](GoldbachBoundaries/Paper2/M2/Fill/norm_far_term_le.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M2.Fill.pairSum_conj`](GoldbachBoundaries/Paper2/M2/Fill/pairSum_conj.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M2.Fill.pairSum_ne_zero_of_not_nearBad`](GoldbachBoundaries/Paper2/M2/Fill/pairSum_ne_zero_of_not_nearBad.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M2.Fill.pinchPairs_other_mem`](GoldbachBoundaries/Paper2/M2/Fill/pinchPairs_other_mem.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M2.Fill.poleSetQ_window_count`](GoldbachBoundaries/Paper2/M2/Fill/poleSetQ_window_count.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M2.Fill.prop_Lambda_core`](GoldbachBoundaries/Paper2/M2/Fill/prop_Lambda_core.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M2.Fill.prop_Lambda_of_core`](GoldbachBoundaries/Paper2/M2/Fill/prop_Lambda_of_core.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M2.Fill.rep_facts`](GoldbachBoundaries/Paper2/M2/Fill/rep_facts.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M2.Fill.rigPairs_mem_pairOf`](GoldbachBoundaries/Paper2/M2/Fill/rigPairs_mem_pairOf.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M2.Fill.singlePairs_bounds`](GoldbachBoundaries/Paper2/M2/Fill/singlePairs_bounds.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M2.Fill.singlePairs_finite_ncard_ge`](GoldbachBoundaries/Paper2/M2/Fill/singlePairs_finite_ncard_ge.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M2.Fill.singlePairs_injOn`](GoldbachBoundaries/Paper2/M2/Fill/singlePairs_injOn.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M2.Fill.singleRep_points_infinite`](GoldbachBoundaries/Paper2/M2/Fill/singleRep_points_infinite.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M2.Fill.summable_pinchPairs_one_add`](GoldbachBoundaries/Paper2/M2/Fill/summable_pinchPairs_one_add.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M2.Fill.summable_tsum_le_of_shells`](GoldbachBoundaries/Paper2/M2/Fill/summable_tsum_le_of_shells.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M2.Fill.zetaMult_le_log`](GoldbachBoundaries/Paper2/M2/Fill/zetaMult_le_log.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M2.Fill.zetaStar_facts`](GoldbachBoundaries/Paper2/M2/Fill/zetaStar_facts.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M2.LW`](GoldbachBoundaries/Paper2/M2/LW.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M2.Lambda`](GoldbachBoundaries/Paper2/M2/Lambda.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M2.QCount`](GoldbachBoundaries/Paper2/M2/QCount.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M2.Rigidity`](GoldbachBoundaries/Paper2/M2/Rigidity.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M2.Single`](GoldbachBoundaries/Paper2/M2/Single.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M2.Skeleton`](GoldbachBoundaries/Paper2/M2/Skeleton.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M3.AConst`](GoldbachBoundaries/Paper2/M3/AConst.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M3.Classical`](GoldbachBoundaries/Paper2/M3/Classical.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M3.Defs`](GoldbachBoundaries/Paper2/M3/Defs.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M3.Fill.Aconst_terms_le`](GoldbachBoundaries/Paper2/M3/Fill/Aconst_terms_le.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M3.Fill.CCommon`](GoldbachBoundaries/Paper2/M3/Fill/CCommon.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M3.Fill.D2Common`](GoldbachBoundaries/Paper2/M3/Fill/D2Common.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M3.Fill.FCommon`](GoldbachBoundaries/Paper2/M3/Fill/FCommon.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M3.Fill.GCommon`](GoldbachBoundaries/Paper2/M3/Fill/GCommon.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M3.Fill.Gamma_mul_Qcont_eq_of_mem`](GoldbachBoundaries/Paper2/M3/Fill/Gamma_mul_Qcont_eq_of_mem.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M3.Fill.LandauCommon`](GoldbachBoundaries/Paper2/M3/Fill/LandauCommon.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M3.Fill.Mcal_eq_formula`](GoldbachBoundaries/Paper2/M3/Fill/Mcal_eq_formula.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M3.Fill.Rcoef_eq_zero_of_mem_mellinConvSet`](GoldbachBoundaries/Paper2/M3/Fill/Rcoef_eq_zero_of_mem_mellinConvSet.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M3.Fill.Rcoef_of_half_le_re`](GoldbachBoundaries/Paper2/M3/Fill/Rcoef_of_half_le_re.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M3.Fill.analyticAt_Mform_of_eq_T`](GoldbachBoundaries/Paper2/M3/Fill/analyticAt_Mform_of_eq_T.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M3.Fill.differentiableOn_laplace`](GoldbachBoundaries/Paper2/M3/Fill/differentiableOn_laplace.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M3.Fill.eulerMascheroni_bounds`](GoldbachBoundaries/Paper2/M3/Fill/eulerMascheroni_bounds.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M3.Fill.exists_differentiableOn_balls`](GoldbachBoundaries/Paper2/M3/Fill/exists_differentiableOn_balls.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M3.Fill.exp_neg_one_le_Gamma`](GoldbachBoundaries/Paper2/M3/Fill/exp_neg_one_le_Gamma.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M3.Fill.hasResidue_Mform_Tcont_two_Bsup`](GoldbachBoundaries/Paper2/M3/Fill/hasResidue_Mform_Tcont_two_Bsup.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M3.Fill.hasResidue_two_of_codiscrete`](GoldbachBoundaries/Paper2/M3/Fill/hasResidue_two_of_codiscrete.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M3.Fill.integrableOn_Theta_Ioi`](GoldbachBoundaries/Paper2/M3/Fill/integrableOn_Theta_Ioi.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M3.Fill.integrableOn_hErr_mul_cpow_of_mem`](GoldbachBoundaries/Paper2/M3/Fill/integrableOn_hErr_mul_cpow_of_mem.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M3.Fill.integrableOn_hErr_sq_cpow_of_mem`](GoldbachBoundaries/Paper2/M3/Fill/integrableOn_hErr_sq_cpow_of_mem.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M3.Fill.integrableOn_laplace_of_lt`](GoldbachBoundaries/Paper2/M3/Fill/integrableOn_laplace_of_lt.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M3.Fill.iteratedDeriv_laplace`](GoldbachBoundaries/Paper2/M3/Fill/iteratedDeriv_laplace.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M3.Fill.laplaceConvSet_phiH`](GoldbachBoundaries/Paper2/M3/Fill/laplaceConvSet_phiH.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M3.Fill.laplace_no_extension`](GoldbachBoundaries/Paper2/M3/Fill/laplace_no_extension.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M3.Fill.laplace_phiH_eq_Mcal`](GoldbachBoundaries/Paper2/M3/Fill/laplace_phiH_eq_Mcal.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M3.Fill.log_pi_bounds`](GoldbachBoundaries/Paper2/M3/Fill/log_pi_bounds.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M3.Fill.measurable_phiH`](GoldbachBoundaries/Paper2/M3/Fill/measurable_phiH.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M3.Fill.mem_mellinConvSet_of_differentiableOn_balls`](GoldbachBoundaries/Paper2/M3/Fill/mem_mellinConvSet_of_differentiableOn_balls.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M3.Fill.mem_mellinConvSet_of_two_lt`](GoldbachBoundaries/Paper2/M3/Fill/mem_mellinConvSet_of_two_lt.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M3.Fill.mem_nontrivialZeros_of_zeta_eq_zero`](GoldbachBoundaries/Paper2/M3/Fill/mem_nontrivialZeros_of_zeta_eq_zero.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M3.Fill.meromorphicOn_Mform`](GoldbachBoundaries/Paper2/M3/Fill/meromorphicOn_Mform.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M3.Fill.norm_Gamma_sq_le`](GoldbachBoundaries/Paper2/M3/Fill/norm_Gamma_sq_le.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M3.Fill.order_Mform_Tcont_nonneg`](GoldbachBoundaries/Paper2/M3/Fill/order_Mform_Tcont_nonneg.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M3.Fill.order_Mform_nonneg_of_test`](GoldbachBoundaries/Paper2/M3/Fill/order_Mform_nonneg_of_test.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M3.Fill.order_residue_of_tendsto_ofReal`](GoldbachBoundaries/Paper2/M3/Fill/order_residue_of_tendsto_ofReal.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M3.Fill.pairSum_two_Bsup`](GoldbachBoundaries/Paper2/M3/Fill/pairSum_two_Bsup.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M3.Fill.pinchPairs_two_Bsup`](GoldbachBoundaries/Paper2/M3/Fill/pinchPairs_two_Bsup.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M3.Fill.real_mem_catalogue_iff`](GoldbachBoundaries/Paper2/M3/Fill/real_mem_catalogue_iff.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M3.Fill.sum_weight_le`](GoldbachBoundaries/Paper2/M3/Fill/sum_weight_le.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M3.Fill.tendsto_mul_Theta`](GoldbachBoundaries/Paper2/M3/Fill/tendsto_mul_Theta.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M3.Fill.tendsto_sub_two_mul_Gamma_T`](GoldbachBoundaries/Paper2/M3/Fill/tendsto_sub_two_mul_Gamma_T.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M3.Fill.tendsto_sub_two_mul_Mcal`](GoldbachBoundaries/Paper2/M3/Fill/tendsto_sub_two_mul_Mcal.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M3.Hsq`](GoldbachBoundaries/Paper2/M3/Hsq.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M3.Landau`](GoldbachBoundaries/Paper2/M3/Landau.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M3.Mellin`](GoldbachBoundaries/Paper2/M3/Mellin.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M3.Numerics`](GoldbachBoundaries/Paper2/M3/Numerics.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M3.Real`](GoldbachBoundaries/Paper2/M3/Real.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M3.Skeleton`](GoldbachBoundaries/Paper2/M3/Skeleton.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M3.Test`](GoldbachBoundaries/Paper2/M3/Test.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M3.Zeros`](GoldbachBoundaries/Paper2/M3/Zeros.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4a.Catalogue`](GoldbachBoundaries/Paper2/M4a/Catalogue.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4a.Coeff`](GoldbachBoundaries/Paper2/M4a/Coeff.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4a.Defs`](GoldbachBoundaries/Paper2/M4a/Defs.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4a.Fill.BCommon`](GoldbachBoundaries/Paper2/M4a/Fill/BCommon.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4a.Fill.DCommon`](GoldbachBoundaries/Paper2/M4a/Fill/DCommon.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4a.Fill.ECommon`](GoldbachBoundaries/Paper2/M4a/Fill/ECommon.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4a.Fill.GroupCCommon`](GoldbachBoundaries/Paper2/M4a/Fill/GroupCCommon.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4a.Fill.K2_kr`](GoldbachBoundaries/Paper2/M4a/Fill/K2_kr.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4a.Fill.Rcoef_div_of_RH`](GoldbachBoundaries/Paper2/M4a/Fill/Rcoef_div_of_RH.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4a.Fill.analyticOnNhd_bracket`](GoldbachBoundaries/Paper2/M4a/Fill/analyticOnNhd_bracket.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4a.Fill.analyticOnNhd_lineCoeff`](GoldbachBoundaries/Paper2/M4a/Fill/analyticOnNhd_lineCoeff.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4a.Fill.bracket_meromorphic_of_K4`](GoldbachBoundaries/Paper2/M4a/Fill/bracket_meromorphic_of_K4.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4a.Fill.cP_ne_zero_of_RH`](GoldbachBoundaries/Paper2/M4a/Fill/cP_ne_zero_of_RH.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4a.Fill.catalogueL_locallyFinite`](GoldbachBoundaries/Paper2/M4a/Fill/catalogueL_locallyFinite.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4a.Fill.differentiableOn_Jseg`](GoldbachBoundaries/Paper2/M4a/Fill/differentiableOn_Jseg.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4a.Fill.eq_div_of_continuousAt`](GoldbachBoundaries/Paper2/M4a/Fill/eq_div_of_continuousAt.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4a.Fill.exists_lineCoeff_ne_zero`](GoldbachBoundaries/Paper2/M4a/Fill/exists_lineCoeff_ne_zero.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4a.Fill.exists_ne_zero_of_isBigO_pow`](GoldbachBoundaries/Paper2/M4a/Fill/exists_ne_zero_of_isBigO_pow.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4a.Fill.hasDerivAt_Jseg_of_H2b`](GoldbachBoundaries/Paper2/M4a/Fill/hasDerivAt_Jseg_of_H2b.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4a.Fill.hasDerivAt_Jseg_of_app_eq`](GoldbachBoundaries/Paper2/M4a/Fill/hasDerivAt_Jseg_of_app_eq.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4a.Fill.infinite_pinches_of_infinite`](GoldbachBoundaries/Paper2/M4a/Fill/infinite_pinches_of_infinite.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4a.Fill.infinite_scaledZeros_near`](GoldbachBoundaries/Paper2/M4a/Fill/infinite_scaledZeros_near.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4a.Fill.integral_kernelt_le`](GoldbachBoundaries/Paper2/M4a/Fill/integral_kernelt_le.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4a.Fill.isBigO_Jseg_k0_one_one`](GoldbachBoundaries/Paper2/M4a/Fill/isBigO_Jseg_k0_one_one.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4a.Fill.isBigO_Jseg_kr_b_one`](GoldbachBoundaries/Paper2/M4a/Fill/isBigO_Jseg_kr_b_one.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4a.Fill.isBigO_Jseg_kr_one_b`](GoldbachBoundaries/Paper2/M4a/Fill/isBigO_Jseg_kr_one_b.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4a.Fill.isBigO_integral_param`](GoldbachBoundaries/Paper2/M4a/Fill/isBigO_integral_param.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4a.Fill.isMeromorphic₂_restrict_line`](GoldbachBoundaries/Paper2/M4a/Fill/isMeromorphic₂_restrict_line.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4a.Fill.meromorphicOn_H2b_rhs`](GoldbachBoundaries/Paper2/M4a/Fill/meromorphicOn_H2b_rhs.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4a.Fill.norm_KerS_le_kernelt`](GoldbachBoundaries/Paper2/M4a/Fill/norm_KerS_le_kernelt.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4a.Fill.norm_inv_Gamma_le`](GoldbachBoundaries/Paper2/M4a/Fill/norm_inv_Gamma_le.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4a.Fill.not_eventually_zero_of_eqOn_bracket`](GoldbachBoundaries/Paper2/M4a/Fill/not_eventually_zero_of_eqOn_bracket.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4a.Fill.pinchPairs_one_add`](GoldbachBoundaries/Paper2/M4a/Fill/pinchPairs_one_add.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4a.Fill.scaledPinch_facts`](GoldbachBoundaries/Paper2/M4a/Fill/scaledPinch_facts.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4a.Fill.segment_subset_Str`](GoldbachBoundaries/Paper2/M4a/Fill/segment_subset_Str.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4a.Fill.sub_one_mem_poleSetQ_of_mem_pinch`](GoldbachBoundaries/Paper2/M4a/Fill/sub_one_mem_poleSetQ_of_mem_pinch.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4a.H2log`](GoldbachBoundaries/Paper2/M4a/H2log.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4a.H3`](GoldbachBoundaries/Paper2/M4a/H3.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4a.Jseg`](GoldbachBoundaries/Paper2/M4a/Jseg.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4a.Kernel`](GoldbachBoundaries/Paper2/M4a/Kernel.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4a.Order`](GoldbachBoundaries/Paper2/M4a/Order.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4a.Restrict`](GoldbachBoundaries/Paper2/M4a/Restrict.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4a.Skeleton`](GoldbachBoundaries/Paper2/M4a/Skeleton.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4b.Boundary`](GoldbachBoundaries/Paper2/M4b/Boundary.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4b.Defs`](GoldbachBoundaries/Paper2/M4b/Defs.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4b.ExG`](GoldbachBoundaries/Paper2/M4b/ExG.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4b.Fill.ACommon`](GoldbachBoundaries/Paper2/M4b/Fill/ACommon.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4b.Fill.ACommonRising`](GoldbachBoundaries/Paper2/M4b/Fill/ACommonRising.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4b.Fill.BCommon`](GoldbachBoundaries/Paper2/M4b/Fill/BCommon.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4b.Fill.BShiftCommon`](GoldbachBoundaries/Paper2/M4b/Fill/BShiftCommon.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4b.Fill.C1Common`](GoldbachBoundaries/Paper2/M4b/Fill/C1Common.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4b.Fill.C2Common`](GoldbachBoundaries/Paper2/M4b/Fill/C2Common.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4b.Fill.DCommon`](GoldbachBoundaries/Paper2/M4b/Fill/DCommon.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4b.Fill.E1Common`](GoldbachBoundaries/Paper2/M4b/Fill/E1Common.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4b.Fill.Fmero_eq_strip`](GoldbachBoundaries/Paper2/M4b/Fill/Fmero_eq_strip.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4b.Fill.Fmero_eq_upper`](GoldbachBoundaries/Paper2/M4b/Fill/Fmero_eq_upper.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4b.Fill.Fmero_strip_facts`](GoldbachBoundaries/Paper2/M4b/Fill/Fmero_strip_facts.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4b.Fill.Fmero_upper_facts`](GoldbachBoundaries/Paper2/M4b/Fill/Fmero_upper_facts.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4b.Fill.Ilog_eq_of_no_pole`](GoldbachBoundaries/Paper2/M4b/Fill/Ilog_eq_of_no_pole.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4b.Fill.Ilog_step_one`](GoldbachBoundaries/Paper2/M4b/Fill/Ilog_step_one.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4b.Fill.Ilog_step_sub_one`](GoldbachBoundaries/Paper2/M4b/Fill/Ilog_step_sub_one.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4b.Fill.K2_kerS`](GoldbachBoundaries/Paper2/M4b/Fill/K2_kerS.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4b.Fill.K2_kerSq`](GoldbachBoundaries/Paper2/M4b/Fill/K2_kerSq.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4b.Fill.K4_kernels`](GoldbachBoundaries/Paper2/M4b/Fill/K4_kernels.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4b.Fill.W0_k0_rising`](GoldbachBoundaries/Paper2/M4b/Fill/W0_k0_rising.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4b.Fill.differentiableAt_integrand`](GoldbachBoundaries/Paper2/M4b/Fill/differentiableAt_integrand.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4b.Fill.differentiableOn_Ilog`](GoldbachBoundaries/Paper2/M4b/Fill/differentiableOn_Ilog.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4b.Fill.differentiableOn_Iminus_Iplus`](GoldbachBoundaries/Paper2/M4b/Fill/differentiableOn_Iminus_Iplus.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4b.Fill.differentiableOn_dser`](GoldbachBoundaries/Paper2/M4b/Fill/differentiableOn_dser.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4b.Fill.eventuallyEq_Fmero`](GoldbachBoundaries/Paper2/M4b/Fill/eventuallyEq_Fmero.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4b.Fill.exists_T0_ne_zero`](GoldbachBoundaries/Paper2/M4b/Fill/exists_T0_ne_zero.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4b.Fill.exists_differentiableOn_of_order_nonneg`](GoldbachBoundaries/Paper2/M4b/Fill/exists_differentiableOn_of_order_nonneg.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4b.Fill.exists_pole_near_line`](GoldbachBoundaries/Paper2/M4b/Fill/exists_pole_near_line.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4b.Fill.filter_series_aux`](GoldbachBoundaries/Paper2/M4b/Fill/filter_series_aux.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4b.Fill.hypR_k0`](GoldbachBoundaries/Paper2/M4b/Fill/hypR_k0.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4b.Fill.hypR_kerG_WG`](GoldbachBoundaries/Paper2/M4b/Fill/hypR_kerG_WG.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4b.Fill.hypR_kerG_WT`](GoldbachBoundaries/Paper2/M4b/Fill/hypR_kerG_WT.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4b.Fill.hypR_kerS`](GoldbachBoundaries/Paper2/M4b/Fill/hypR_kerS.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4b.Fill.hypR_kerSq`](GoldbachBoundaries/Paper2/M4b/Fill/hypR_kerSq.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4b.Fill.im_DH_eq_zero`](GoldbachBoundaries/Paper2/M4b/Fill/im_DH_eq_zero.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4b.Fill.isBigO_mul_sub_residue`](GoldbachBoundaries/Paper2/M4b/Fill/isBigO_mul_sub_residue.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4b.Fill.kH_eq_krise`](GoldbachBoundaries/Paper2/M4b/Fill/kH_eq_krise.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4b.Fill.kerS_basic`](GoldbachBoundaries/Paper2/M4b/Fill/kerS_basic.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4b.Fill.kerSq_basic`](GoldbachBoundaries/Paper2/M4b/Fill/kerSq_basic.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4b.Fill.mellinInv_kMB`](GoldbachBoundaries/Paper2/M4b/Fill/mellinInv_kMB.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4b.Fill.mero_mul_Qcont_app`](GoldbachBoundaries/Paper2/M4b/Fill/mero_mul_Qcont_app.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4b.Fill.meromorphicOn_Fmero`](GoldbachBoundaries/Paper2/M4b/Fill/meromorphicOn_Fmero.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4b.Fill.norm_integrand_le_far`](GoldbachBoundaries/Paper2/M4b/Fill/norm_integrand_le_far.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4b.Fill.order_Fmero_nonneg`](GoldbachBoundaries/Paper2/M4b/Fill/order_Fmero_nonneg.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4b.Fill.rising_differentiableOn`](GoldbachBoundaries/Paper2/M4b/Fill/rising_differentiableOn.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4b.Fill.rising_summable_eq`](GoldbachBoundaries/Paper2/M4b/Fill/rising_summable_eq.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4b.Fill.tsum_eq_verticalIntegral'_of_mellin`](GoldbachBoundaries/Paper2/M4b/Fill/tsum_eq_verticalIntegral'_of_mellin.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4b.Fill.verticalIntegral'_comp_affine`](GoldbachBoundaries/Paper2/M4b/Fill/verticalIntegral'_comp_affine.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4b.Kernels`](GoldbachBoundaries/Paper2/M4b/Kernels.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4b.MB`](GoldbachBoundaries/Paper2/M4b/MB.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4b.Mero`](GoldbachBoundaries/Paper2/M4b/Mero.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4b.Rising`](GoldbachBoundaries/Paper2/M4b/Rising.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4b.SeriesS`](GoldbachBoundaries/Paper2/M4b/SeriesS.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4b.Skeleton`](GoldbachBoundaries/Paper2/M4b/Skeleton.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4b.Squares`](GoldbachBoundaries/Paper2/M4b/Squares.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M4b.T0`](GoldbachBoundaries/Paper2/M4b/T0.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.Defs`](GoldbachBoundaries/Paper2/M5/Defs.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.Fill.CH_eq_tsum_limTerm`](GoldbachBoundaries/Paper2/M5/Fill/CH_eq_tsum_limTerm.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.Fill.CH_eq_two_terms`](GoldbachBoundaries/Paper2/M5/Fill/CH_eq_two_terms.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.Fill.F1Common`](GoldbachBoundaries/Paper2/M5/Fill/F1Common.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.Fill.F2Common`](GoldbachBoundaries/Paper2/M5/Fill/F2Common.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.Fill.F3Common`](GoldbachBoundaries/Paper2/M5/Fill/F3Common.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.Fill.F4Common`](GoldbachBoundaries/Paper2/M5/Fill/F4Common.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.Fill.FilLine_eq_of_le`](GoldbachBoundaries/Paper2/M5/Fill/FilLine_eq_of_le.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.Fill.Lambda0_eq_limit`](GoldbachBoundaries/Paper2/M5/Fill/Lambda0_eq_limit.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.Fill.QCommon`](GoldbachBoundaries/Paper2/M5/Fill/QCommon.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.Fill.Qleft_i`](GoldbachBoundaries/Paper2/M5/Fill/Qleft_i.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.Fill.Qleft_ii`](GoldbachBoundaries/Paper2/M5/Fill/Qleft_ii.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.Fill.Qleft_iii`](GoldbachBoundaries/Paper2/M5/Fill/Qleft_iii.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.Fill.T2Common`](GoldbachBoundaries/Paper2/M5/Fill/T2Common.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.Fill.T3Common`](GoldbachBoundaries/Paper2/M5/Fill/T3Common.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.Fill.TkLine_differentiableOn`](GoldbachBoundaries/Paper2/M5/Fill/TkLine_differentiableOn.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.Fill.TkLine_eq_of_no_pole`](GoldbachBoundaries/Paper2/M5/Fill/TkLine_eq_of_no_pole.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.Fill.TkLine_step_pole`](GoldbachBoundaries/Paper2/M5/Fill/TkLine_step_pole.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.Fill.TkLine_step_sub_one`](GoldbachBoundaries/Paper2/M5/Fill/TkLine_step_sub_one.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.Fill.TkStep_eq_strip`](GoldbachBoundaries/Paper2/M5/Fill/TkStep_eq_strip.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.Fill.TkStep_eq_upper`](GoldbachBoundaries/Paper2/M5/Fill/TkStep_eq_upper.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.Fill.TkStep_growth`](GoldbachBoundaries/Paper2/M5/Fill/TkStep_growth.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.Fill.TkStep_pole_facts`](GoldbachBoundaries/Paper2/M5/Fill/TkStep_pole_facts.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.Fill.TkStep_strip_formula`](GoldbachBoundaries/Paper2/M5/Fill/TkStep_strip_formula.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.Fill.Tk_strip_facts`](GoldbachBoundaries/Paper2/M5/Fill/Tk_strip_facts.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.Fill.Tk_succ_eq_verticalIntegral'`](GoldbachBoundaries/Paper2/M5/Fill/Tk_succ_eq_verticalIntegral'.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.Fill.analyticAt_Afun`](GoldbachBoundaries/Paper2/M5/Fill/analyticAt_Afun.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.Fill.differentiableOn_Fil`](GoldbachBoundaries/Paper2/M5/Fill/differentiableOn_Fil.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.Fill.differentiableOn_FilLine`](GoldbachBoundaries/Paper2/M5/Fill/differentiableOn_FilLine.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.Fill.differentiableOn_Jfil`](GoldbachBoundaries/Paper2/M5/Fill/differentiableOn_Jfil.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.Fill.differentiableOn_TkPlus_TkMin`](GoldbachBoundaries/Paper2/M5/Fill/differentiableOn_TkPlus_TkMin.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.Fill.eqOn_DH_H0f_of_T0`](GoldbachBoundaries/Paper2/M5/Fill/eqOn_DH_H0f_of_T0.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.Fill.eqOn_HH_of_eqOn_open`](GoldbachBoundaries/Paper2/M5/Fill/eqOn_HH_of_eqOn_open.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.Fill.evalH_root_bound`](GoldbachBoundaries/Paper2/M5/Fill/evalH_root_bound.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.Fill.eventuallyEq_of_tkPack`](GoldbachBoundaries/Paper2/M5/Fill/eventuallyEq_of_tkPack.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.Fill.exists_factor_H`](GoldbachBoundaries/Paper2/M5/Fill/exists_factor_H.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.Fill.exists_ordinate_in_interval`](GoldbachBoundaries/Paper2/M5/Fill/exists_ordinate_in_interval.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.Fill.exists_pole_near_line_Tk`](GoldbachBoundaries/Paper2/M5/Fill/exists_pole_near_line_Tk.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.Fill.exists_sep_height`](GoldbachBoundaries/Paper2/M5/Fill/exists_sep_height.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.Fill.exists_tau0_CH_ne_zero`](GoldbachBoundaries/Paper2/M5/Fill/exists_tau0_CH_ne_zero.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.Fill.filter_rect`](GoldbachBoundaries/Paper2/M5/Fill/filter_rect.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.Fill.filter_rect_limit`](GoldbachBoundaries/Paper2/M5/Fill/filter_rect_limit.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.Fill.filter_shift`](GoldbachBoundaries/Paper2/M5/Fill/filter_shift.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.Fill.meromorphicOn_TkStep`](GoldbachBoundaries/Paper2/M5/Fill/meromorphicOn_TkStep.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.Fill.noMeromorphicExtensionAt_of_line_blowup`](GoldbachBoundaries/Paper2/M5/Fill/noMeromorphicExtensionAt_of_line_blowup.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.Fill.norm_TkIntegrand_le_far`](GoldbachBoundaries/Paper2/M5/Fill/norm_TkIntegrand_le_far.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.Fill.norm_TkLine_le`](GoldbachBoundaries/Paper2/M5/Fill/norm_TkLine_le.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.Fill.norm_gA_le`](GoldbachBoundaries/Paper2/M5/Fill/norm_gA_le.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.Fill.norm_negLogDerivZeta_le_of_sep`](GoldbachBoundaries/Paper2/M5/Fill/norm_negLogDerivZeta_le_of_sep.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.Fill.norm_resTerm_le`](GoldbachBoundaries/Paper2/M5/Fill/norm_resTerm_le.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.Fill.norm_sigmaTail_four_le`](GoldbachBoundaries/Paper2/M5/Fill/norm_sigmaTail_four_le.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.Fill.order_residue_add_analyticAt`](GoldbachBoundaries/Paper2/M5/Fill/order_residue_add_analyticAt.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.Fill.order_residue_of_codiscrete_line`](GoldbachBoundaries/Paper2/M5/Fill/order_residue_of_codiscrete_line.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.Fill.poleSetQ_re_cases`](GoldbachBoundaries/Paper2/M5/Fill/poleSetQ_re_cases.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.Fill.rectangleIntegral'_eq_sum_of_simplePoles_rect`](GoldbachBoundaries/Paper2/M5/Fill/rectangleIntegral'_eq_sum_of_simplePoles_rect.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.Fill.summable_zeros_inv_sq`](GoldbachBoundaries/Paper2/M5/Fill/summable_zeros_inv_sq.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.Fill.tendsto_eta_Fil`](GoldbachBoundaries/Paper2/M5/Fill/tendsto_eta_Fil.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.Fill.tendsto_eta_midTerm`](GoldbachBoundaries/Paper2/M5/Fill/tendsto_eta_midTerm.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.Fill.tendsto_eta_resTerm`](GoldbachBoundaries/Paper2/M5/Fill/tendsto_eta_resTerm.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.Fill.tkPack_one`](GoldbachBoundaries/Paper2/M5/Fill/tkPack_one.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.Fill.tsum_add_prime_eq_verticalIntegral'`](GoldbachBoundaries/Paper2/M5/Fill/tsum_add_prime_eq_verticalIntegral'.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.FilterI`](GoldbachBoundaries/Paper2/M5/FilterI.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.FilterII`](GoldbachBoundaries/Paper2/M5/FilterII.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.FilterIII`](GoldbachBoundaries/Paper2/M5/FilterIII.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.FilterIV`](GoldbachBoundaries/Paper2/M5/FilterIV.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.General`](GoldbachBoundaries/Paper2/M5/General.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.Qleft`](GoldbachBoundaries/Paper2/M5/Qleft.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.Skeleton`](GoldbachBoundaries/Paper2/M5/Skeleton.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.Tk`](GoldbachBoundaries/Paper2/M5/Tk.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.TkLine`](GoldbachBoundaries/Paper2/M5/TkLine.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M5.TkStep`](GoldbachBoundaries/Paper2/M5/TkStep.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M6.Branch`](GoldbachBoundaries/Paper2/M6/Branch.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M6.Defs`](GoldbachBoundaries/Paper2/M6/Defs.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M6.ExG`](GoldbachBoundaries/Paper2/M6/ExG.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M6.Fill.BCommon`](GoldbachBoundaries/Paper2/M6/Fill/BCommon.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M6.Fill.J_swap_one`](GoldbachBoundaries/Paper2/M6/Fill/J_swap_one.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M6.Fill.Jseg_idL_kerG_eq_J`](GoldbachBoundaries/Paper2/M6/Fill/Jseg_idL_kerG_eq_J.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M6.Fill.OmegaP_inter_halfPlane_half`](GoldbachBoundaries/Paper2/M6/Fill/OmegaP_inter_halfPlane_half.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M6.Fill.OmegaP_subset`](GoldbachBoundaries/Paper2/M6/Fill/OmegaP_subset.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M6.Fill.P_conj`](GoldbachBoundaries/Paper2/M6/Fill/P_conj.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M6.Fill.Ptil_conj`](GoldbachBoundaries/Paper2/M6/Fill/Ptil_conj.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M6.Fill.Ptil_eqOn_P`](GoldbachBoundaries/Paper2/M6/Fill/Ptil_eqOn_P.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M6.Fill.Xcoef_idL_kerG_eq_X`](GoldbachBoundaries/Paper2/M6/Fill/Xcoef_idL_kerG_eq_X.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M6.Fill.add_real_mem_OmegaP`](GoldbachBoundaries/Paper2/M6/Fill/add_real_mem_OmegaP.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M6.Fill.conj_mem_OmegaP`](GoldbachBoundaries/Paper2/M6/Fill/conj_mem_OmegaP.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M6.Fill.contractibleSpace_OmegaP`](GoldbachBoundaries/Paper2/M6/Fill/contractibleSpace_OmegaP.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M6.Fill.eqOn_OmegaP_of_eqOn_halfPlane_one`](GoldbachBoundaries/Paper2/M6/Fill/eqOn_OmegaP_of_eqOn_halfPlane_one.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M6.Fill.eqOn_neg_log_add_Eaux`](GoldbachBoundaries/Paper2/M6/Fill/eqOn_neg_log_add_Eaux.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M6.Fill.eventuallyEq_add_const_of_hasDerivAt`](GoldbachBoundaries/Paper2/M6/Fill/eventuallyEq_add_const_of_hasDerivAt.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M6.Fill.exists_E_pole`](GoldbachBoundaries/Paper2/M6/Fill/exists_E_pole.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M6.Fill.halfPlane_one_subset_OmegaP`](GoldbachBoundaries/Paper2/M6/Fill/halfPlane_one_subset_OmegaP.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M6.Fill.hasCatalogueValues_congr`](GoldbachBoundaries/Paper2/M6/Fill/hasCatalogueValues_congr.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M6.Fill.hasDerivAt_Ptil`](GoldbachBoundaries/Paper2/M6/Fill/hasDerivAt_Ptil.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M6.Fill.hasDerivAt_log_ray`](GoldbachBoundaries/Paper2/M6/Fill/hasDerivAt_log_ray.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M6.Fill.isAdmissibleGermOn_eventually`](GoldbachBoundaries/Paper2/M6/Fill/isAdmissibleGermOn_eventually.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M6.Fill.isClosed_rayFrom`](GoldbachBoundaries/Paper2/M6/Fill/isClosed_rayFrom.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M6.Fill.isOpen_OmegaP`](GoldbachBoundaries/Paper2/M6/Fill/isOpen_OmegaP.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M6.Fill.isOpen_halfPlane_diff_poleSetQ`](GoldbachBoundaries/Paper2/M6/Fill/isOpen_halfPlane_diff_poleSetQ.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M6.Fill.isOpen_isPreconnected_slitHalf`](GoldbachBoundaries/Paper2/M6/Fill/isOpen_isPreconnected_slitHalf.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M6.Fill.isPathConnected_OmegaP`](GoldbachBoundaries/Paper2/M6/Fill/isPathConnected_OmegaP.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M6.Fill.local_form_slitDiscL_of_slitDisc`](GoldbachBoundaries/Paper2/M6/Fill/local_form_slitDiscL_of_slitDisc.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M6.Fill.norm_P_le`](GoldbachBoundaries/Paper2/M6/Fill/norm_P_le.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M6.Fill.norm_neg_log_add_Eaux_le`](GoldbachBoundaries/Paper2/M6/Fill/norm_neg_log_add_Eaux_le.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M6.Fill.uniformFamily_PBranchFam`](GoldbachBoundaries/Paper2/M6/Fill/uniformFamily_PBranchFam.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M6.Local`](GoldbachBoundaries/Paper2/M6/Local.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M6.Omega`](GoldbachBoundaries/Paper2/M6/Omega.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M6.Ptil`](GoldbachBoundaries/Paper2/M6/Ptil.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M6.Sheet`](GoldbachBoundaries/Paper2/M6/Sheet.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.M6.Skeleton`](GoldbachBoundaries/Paper2/M6/Skeleton.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Paper2.Statements`](GoldbachBoundaries/Paper2/Statements.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.PhaseCone.Sector`](GoldbachBoundaries/PhaseCone/Sector.lean) | ● | ✓ | ● |
| [`GoldbachBoundaries.PhaseCone.SectorPoly`](GoldbachBoundaries/PhaseCone/SectorPoly.lean) | ● | ● | ● |
| [`GoldbachBoundaries.Phi2.Defs`](GoldbachBoundaries/Phi2/Defs.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2.Fill.ACommon`](GoldbachBoundaries/Phi2/Fill/ACommon.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2.Fill.Aidx_bin_le`](GoldbachBoundaries/Phi2/Fill/Aidx_bin_le.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2.Fill.BCommon`](GoldbachBoundaries/Phi2/Fill/BCommon.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2.Fill.CCommon`](GoldbachBoundaries/Phi2/Fill/CCommon.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2.Fill.DCommon`](GoldbachBoundaries/Phi2/Fill/DCommon.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2.Fill.FL_basic`](GoldbachBoundaries/Phi2/Fill/FL_basic.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2.Fill.FL_eq_verticalIntegral'`](GoldbachBoundaries/Phi2/Fill/FL_eq_verticalIntegral'.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2.Fill.Gamma_mul_Phi2_split`](GoldbachBoundaries/Phi2/Fill/Gamma_mul_Phi2_split.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2.Fill.Gamma_mul_negLogDerivZeta_split`](GoldbachBoundaries/Phi2/Fill/Gamma_mul_negLogDerivZeta_split.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2.Fill.RrL_eq_cauchyT_add_Kc`](GoldbachBoundaries/Phi2/Fill/RrL_eq_cauchyT_add_Kc.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2.Fill.bKer_cone`](GoldbachBoundaries/Phi2/Fill/bKer_cone.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2.Fill.differentiable_e1L_E2L`](GoldbachBoundaries/Phi2/Fill/differentiable_e1L_E2L.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2.Fill.exists_large_pair`](GoldbachBoundaries/Phi2/Fill/exists_large_pair.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2.Fill.finite_exceptional`](GoldbachBoundaries/Phi2/Fill/finite_exceptional.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2.Fill.integral_zeroSum_sq`](GoldbachBoundaries/Phi2/Fill/integral_zeroSum_sq.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2.Fill.mellin_FL`](GoldbachBoundaries/Phi2/Fill/mellin_FL.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2.Fill.mellin_FL_sq`](GoldbachBoundaries/Phi2/Fill/mellin_FL_sq.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2.Fill.negLogDerivZeta_good_height`](GoldbachBoundaries/Phi2/Fill/negLogDerivZeta_good_height.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2.Fill.negLogDerivZeta_two_fifths`](GoldbachBoundaries/Phi2/Fill/negLogDerivZeta_two_fifths.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2.Fill.norm_Kc_le`](GoldbachBoundaries/Phi2/Fill/norm_Kc_le.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2.Fill.norm_bKer`](GoldbachBoundaries/Phi2/Fill/norm_bKer.lean) | ● | ✓ | ● |
| [`GoldbachBoundaries.Phi2.Fill.norm_bKer_le`](GoldbachBoundaries/Phi2/Fill/norm_bKer_le.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2.Fill.norm_hL_le`](GoldbachBoundaries/Phi2/Fill/norm_hL_le.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2.Fill.norm_verticalIntegral'_kernelL_two_fifths_le`](GoldbachBoundaries/Phi2/Fill/norm_verticalIntegral'_kernelL_two_fifths_le.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2.Fill.norm_zeroSum_le`](GoldbachBoundaries/Phi2/Fill/norm_zeroSum_le.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2.Fill.pairAtom_eq_two_tsum`](GoldbachBoundaries/Phi2/Fill/pairAtom_eq_two_tsum.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2.Fill.pairAtom_ne_zero_of_large`](GoldbachBoundaries/Phi2/Fill/pairAtom_ne_zero_of_large.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2.Fill.pairAtom_neg`](GoldbachBoundaries/Phi2/Fill/pairAtom_neg.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2.Fill.phi2_identity`](GoldbachBoundaries/Phi2/Fill/phi2_identity.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2.Fill.rect_kernelL`](GoldbachBoundaries/Phi2/Fill/rect_kernelL.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2.Fill.sum_bKer_ne_zero`](GoldbachBoundaries/Phi2/Fill/sum_bKer_ne_zero.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2.Fill.summable_norm_zeroCoef`](GoldbachBoundaries/Phi2/Fill/summable_norm_zeroCoef.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2.Fill.tendsto_eta_cauchyT`](GoldbachBoundaries/Phi2/Fill/tendsto_eta_cauchyT.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2.Fill.verticalIntegral'_kernelL_shift`](GoldbachBoundaries/Phi2/Fill/verticalIntegral'_kernelL_shift.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2.Fill.verticalIntegral'_kernelL_zero_shift`](GoldbachBoundaries/Phi2/Fill/verticalIntegral'_kernelL_zero_shift.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2.Fill.zetaMult_conj`](GoldbachBoundaries/Phi2/Fill/zetaMult_conj.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2.Proof.Defs`](GoldbachBoundaries/Phi2/Proof/Defs.lean) | ✓ | ✓ | ● |
| [`GoldbachBoundaries.Phi2.Proof.M1Continuation`](GoldbachBoundaries/Phi2/Proof/M1Continuation.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2.Proof.M2Explicit`](GoldbachBoundaries/Phi2/Proof/M2Explicit.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2.Proof.M3Base`](GoldbachBoundaries/Phi2/Proof/M3Base.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2.Proof.M3Radial`](GoldbachBoundaries/Phi2/Proof/M3Radial.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2.Proof.M4NonCancel`](GoldbachBoundaries/Phi2/Proof/M4NonCancel.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2.Proof.M5Boundary`](GoldbachBoundaries/Phi2/Proof/M5Boundary.lean) | ● | ✓ | ● |
| [`GoldbachBoundaries.Phi2.Statement`](GoldbachBoundaries/Phi2/Statement.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2HInf.Defs`](GoldbachBoundaries/Phi2HInf/Defs.lean) | ● | ● | ● |
| [`GoldbachBoundaries.Phi2HInf.Fill.analyticOn_M0_strip`](GoldbachBoundaries/Phi2HInf/Fill/analyticOn_M0_strip.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2HInf.Fill.bKer_cone_hinf`](GoldbachBoundaries/Phi2HInf/Fill/bKer_cone_hinf.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2HInf.Fill.cauchy_meromorphic`](GoldbachBoundaries/Phi2HInf/Fill/cauchy_meromorphic.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2HInf.Fill.collision_bin_le`](GoldbachBoundaries/Phi2HInf/Fill/collision_bin_le.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2HInf.Fill.collision_family`](GoldbachBoundaries/Phi2HInf/Fill/collision_family.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2HInf.Fill.contour_regularization`](GoldbachBoundaries/Phi2HInf/Fill/contour_regularization.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2HInf.Fill.critical_basic`](GoldbachBoundaries/Phi2HInf/Fill/critical_basic.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2HInf.Fill.critical_boundary`](GoldbachBoundaries/Phi2HInf/Fill/critical_boundary.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2HInf.Fill.critical_decomposition`](GoldbachBoundaries/Phi2HInf/Fill/critical_decomposition.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2HInf.Fill.differentiableOn_criticalC`](GoldbachBoundaries/Phi2HInf/Fill/differentiableOn_criticalC.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2HInf.Fill.exists_large_critical_pair`](GoldbachBoundaries/Phi2HInf/Fill/exists_large_critical_pair.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2HInf.Fill.good_height`](GoldbachBoundaries/Phi2HInf/Fill/good_height.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2HInf.Fill.hasResidue_C`](GoldbachBoundaries/Phi2HInf/Fill/hasResidue_C.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2HInf.Fill.interior_poles`](GoldbachBoundaries/Phi2HInf/Fill/interior_poles.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2HInf.Fill.meromorphicOn_M0`](GoldbachBoundaries/Phi2HInf/Fill/meromorphicOn_M0.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2HInf.Fill.meromorphicOn_exceptionalC`](GoldbachBoundaries/Phi2HInf/Fill/meromorphicOn_exceptionalC.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2HInf.Fill.negative_line`](GoldbachBoundaries/Phi2HInf/Fill/negative_line.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2HInf.Fill.norm_bKer_asymp`](GoldbachBoundaries/Phi2HInf/Fill/norm_bKer_asymp.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2HInf.Fill.norm_bKer_ratio_le`](GoldbachBoundaries/Phi2HInf/Fill/norm_bKer_ratio_le.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2HInf.Fill.pairCat_geometry`](GoldbachBoundaries/Phi2HInf/Fill/pairCat_geometry.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2HInf.Fill.phi2_hinf_continuation`](GoldbachBoundaries/Phi2HInf/Fill/phi2_hinf_continuation.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2HInf.Fill.r_boundary`](GoldbachBoundaries/Phi2HInf/Fill/r_boundary.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2HInf.Fill.r_cutoff`](GoldbachBoundaries/Phi2HInf/Fill/r_cutoff.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2HInf.Fill.r_finite_mellin`](GoldbachBoundaries/Phi2HInf/Fill/r_finite_mellin.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2HInf.Fill.r_identity`](GoldbachBoundaries/Phi2HInf/Fill/r_identity.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2HInf.Fill.r_remainder`](GoldbachBoundaries/Phi2HInf/Fill/r_remainder.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2HInf.Fill.rect_regularization`](GoldbachBoundaries/Phi2HInf/Fill/rect_regularization.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2HInf.Fill.stirling_log`](GoldbachBoundaries/Phi2HInf/Fill/stirling_log.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2HInf.Fill.sum_bKer_ne_zero_hinf`](GoldbachBoundaries/Phi2HInf/Fill/sum_bKer_ne_zero_hinf.lean) | ● | ✓ | ● |
| [`GoldbachBoundaries.Phi2HInf.Fill.summable_norm_zeroCoef_hinf`](GoldbachBoundaries/Phi2HInf/Fill/summable_norm_zeroCoef_hinf.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2HInf.Fill.tendsto_eta_criticalC`](GoldbachBoundaries/Phi2HInf/Fill/tendsto_eta_criticalC.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2HInf.Fill.zero_mellin`](GoldbachBoundaries/Phi2HInf/Fill/zero_mellin.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2HInf.Proof.Defs`](GoldbachBoundaries/Phi2HInf/Proof/Defs.lean) | ● | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2HInf.Proof.M1Regularization`](GoldbachBoundaries/Phi2HInf/Proof/M1Regularization.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2HInf.Proof.M2Catalogue`](GoldbachBoundaries/Phi2HInf/Proof/M2Catalogue.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2HInf.Proof.M3Cone`](GoldbachBoundaries/Phi2HInf/Proof/M3Cone.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2HInf.Proof.M4Critical`](GoldbachBoundaries/Phi2HInf/Proof/M4Critical.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2HInf.Proof.M5Boundary`](GoldbachBoundaries/Phi2HInf/Proof/M5Boundary.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2HInf.Proof.RBoundary`](GoldbachBoundaries/Phi2HInf/Proof/RBoundary.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2HInf.Proof.RCutoff`](GoldbachBoundaries/Phi2HInf/Proof/RCutoff.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2HInf.Proof.RDefs`](GoldbachBoundaries/Phi2HInf/Proof/RDefs.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2HInf.Proof.RMellin`](GoldbachBoundaries/Phi2HInf/Proof/RMellin.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2HInf.Proof.Ratio`](GoldbachBoundaries/Phi2HInf/Proof/Ratio.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Phi2HInf.Statements`](GoldbachBoundaries/Phi2HInf/Statements.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.PhiR.Defs`](GoldbachBoundaries/PhiR/Defs.lean) |  | ✓ | ● |
| [`GoldbachBoundaries.PhiR.Fill.BCommon`](GoldbachBoundaries/PhiR/Fill/BCommon.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.PhiR.Fill.Gamma_mul_PhiR_split`](GoldbachBoundaries/PhiR/Fill/Gamma_mul_PhiR_split.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.PhiR.Fill.PhiR_eq_explicit`](GoldbachBoundaries/PhiR/Fill/PhiR_eq_explicit.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.PhiR.Fill.QR_eq_sum`](GoldbachBoundaries/PhiR/Fill/QR_eq_sum.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.PhiR.Fill.RR_bounded_halfStrip`](GoldbachBoundaries/PhiR/Fill/RR_bounded_halfStrip.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.PhiR.Fill.analyticAt_phiRRest_line`](GoldbachBoundaries/PhiR/Fill/analyticAt_phiRRest_line.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.PhiR.Fill.analyticOnNhd_PhiRc`](GoldbachBoundaries/PhiR/Fill/analyticOnNhd_PhiRc.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.PhiR.Fill.differentiable_ER`](GoldbachBoundaries/PhiR/Fill/differentiable_ER.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.PhiR.Fill.exists_RR`](GoldbachBoundaries/PhiR/Fill/exists_RR.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.PhiR.Fill.hasResidue_PhiRc`](GoldbachBoundaries/PhiR/Fill/hasResidue_PhiRc.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.PhiR.Fill.mellin_FL_pow`](GoldbachBoundaries/PhiR/Fill/mellin_FL_pow.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.PhiR.Fill.noMeromorphicExtensionAt_comp_sub_iff`](GoldbachBoundaries/PhiR/Fill/noMeromorphicExtensionAt_comp_sub_iff.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.PhiR.Fill.noMeromorphicExtensionAt_iff_of_eq_add_mul`](GoldbachBoundaries/PhiR/Fill/noMeromorphicExtensionAt_iff_of_eq_add_mul.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.PhiR.Fill.norm_QR_le`](GoldbachBoundaries/PhiR/Fill/norm_QR_le.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.PhiR.Fill.riemannZeta_ne_zero_of_re_eq_zero`](GoldbachBoundaries/PhiR/Fill/riemannZeta_ne_zero_of_re_eq_zero.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.PhiR.Fill.tendsto_eta_Phi2c`](GoldbachBoundaries/PhiR/Fill/tendsto_eta_Phi2c.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.PhiR.Proof.Defs`](GoldbachBoundaries/PhiR/Proof/Defs.lean) |  | ✓ | ● |
| [`GoldbachBoundaries.PhiR.Proof.M1Mellin`](GoldbachBoundaries/PhiR/Proof/M1Mellin.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.PhiR.Proof.M2Continuation`](GoldbachBoundaries/PhiR/Proof/M2Continuation.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.PhiR.Proof.M3Boundary`](GoldbachBoundaries/PhiR/Proof/M3Boundary.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.PhiR.Proof.M4Reduction`](GoldbachBoundaries/PhiR/Proof/M4Reduction.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.PhiR.Proof.M5Radial`](GoldbachBoundaries/PhiR/Proof/M5Radial.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.PhiR.RealPoint`](GoldbachBoundaries/PhiR/RealPoint.lean) |  |  | ● |
| [`GoldbachBoundaries.PhiR.Statement`](GoldbachBoundaries/PhiR/Statement.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.ResidueAPI`](GoldbachBoundaries/ResidueAPI.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.ResidueClass.BinaryBoundary`](GoldbachBoundaries/ResidueClass/BinaryBoundary.lean) |  |  | ● |
| [`GoldbachBoundaries.ResidueClass.BinaryContinuation`](GoldbachBoundaries/ResidueClass/BinaryContinuation.lean) |  |  | ● |
| [`GoldbachBoundaries.ResidueClass.BoundaryDensity`](GoldbachBoundaries/ResidueClass/BoundaryDensity.lean) |  |  | ● |
| [`GoldbachBoundaries.ResidueClass.CauchySquare`](GoldbachBoundaries/ResidueClass/CauchySquare.lean) |  |  | ✓ |
| [`GoldbachBoundaries.ResidueClass.ContourBounds`](GoldbachBoundaries/ResidueClass/ContourBounds.lean) |  |  | ✓ |
| [`GoldbachBoundaries.ResidueClass.ContourShift`](GoldbachBoundaries/ResidueClass/ContourShift.lean) |  |  | ● |
| [`GoldbachBoundaries.ResidueClass.Correction`](GoldbachBoundaries/ResidueClass/Correction.lean) |  |  | ● |
| [`GoldbachBoundaries.ResidueClass.Definitions`](GoldbachBoundaries/ResidueClass/Definitions.lean) |  |  | ● |
| [`GoldbachBoundaries.ResidueClass.EulerFactors`](GoldbachBoundaries/ResidueClass/EulerFactors.lean) |  |  | ● |
| [`GoldbachBoundaries.ResidueClass.GammaWeights`](GoldbachBoundaries/ResidueClass/GammaWeights.lean) |  |  | ● |
| [`GoldbachBoundaries.ResidueClass.HigherReduction`](GoldbachBoundaries/ResidueClass/HigherReduction.lean) |  |  | ● |
| [`GoldbachBoundaries.ResidueClass.JensenCount`](GoldbachBoundaries/ResidueClass/JensenCount.lean) |  |  | ● |
| [`GoldbachBoundaries.ResidueClass.LFunctionGrowth`](GoldbachBoundaries/ResidueClass/LFunctionGrowth.lean) |  |  | ✓ |
| [`GoldbachBoundaries.ResidueClass.LocalLogDerivative`](GoldbachBoundaries/ResidueClass/LocalLogDerivative.lean) |  |  | ✓ |
| [`GoldbachBoundaries.ResidueClass.MellinSquare`](GoldbachBoundaries/ResidueClass/MellinSquare.lean) |  |  | ✓ |
| [`GoldbachBoundaries.ResidueClass.PoleWindows`](GoldbachBoundaries/ResidueClass/PoleWindows.lean) |  |  | ● |
| [`GoldbachBoundaries.ResidueClass.RadialLimit`](GoldbachBoundaries/ResidueClass/RadialLimit.lean) |  |  | ● |
| [`GoldbachBoundaries.ResidueClass.RealPoint`](GoldbachBoundaries/ResidueClass/RealPoint.lean) |  |  | ● |
| [`GoldbachBoundaries.ResidueClass.SelectedHeights`](GoldbachBoundaries/ResidueClass/SelectedHeights.lean) |  |  | ✓ |
| [`GoldbachBoundaries.ResidueClass.Series`](GoldbachBoundaries/ResidueClass/Series.lean) |  |  | ● |
| [`GoldbachBoundaries.ResidueClass.Smoothed`](GoldbachBoundaries/ResidueClass/Smoothed.lean) |  |  | ✓ |
| [`GoldbachBoundaries.ResidueClass.Statement`](GoldbachBoundaries/ResidueClass/Statement.lean) |  |  | ● |
| [`GoldbachBoundaries.ResidueClass.WeightedCone`](GoldbachBoundaries/ResidueClass/WeightedCone.lean) |  |  | ● |
| [`GoldbachBoundaries.ResidueClass.ZeroWindows`](GoldbachBoundaries/ResidueClass/ZeroWindows.lean) |  |  | ✓ |
| [`GoldbachBoundaries.ResidueClass.Zeros`](GoldbachBoundaries/ResidueClass/Zeros.lean) |  |  | ● |
| [`GoldbachBoundaries.Series`](GoldbachBoundaries/Series.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.SigmaFinite`](GoldbachBoundaries/SigmaFinite.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.SigmaMeromorphic`](GoldbachBoundaries/SigmaMeromorphic.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.Statements`](GoldbachBoundaries/Statements.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.T0HInf.Catalogue`](GoldbachBoundaries/T0HInf/Catalogue.lean) |  | ● |  |
| [`GoldbachBoundaries.T0HInf.CorrectionContour`](GoldbachBoundaries/T0HInf/CorrectionContour.lean) |  | ✓ |  |
| [`GoldbachBoundaries.T0HInf.CriticalCatalogue`](GoldbachBoundaries/T0HInf/CriticalCatalogue.lean) |  | ● |  |
| [`GoldbachBoundaries.T0HInf.Cutoff`](GoldbachBoundaries/T0HInf/Cutoff.lean) |  | ● |  |
| [`GoldbachBoundaries.T0HInf.Defs`](GoldbachBoundaries/T0HInf/Defs.lean) |  | ● | ✓ |
| [`GoldbachBoundaries.T0HInf.ErrorBounds`](GoldbachBoundaries/T0HInf/ErrorBounds.lean) |  | ✓ |  |
| [`GoldbachBoundaries.T0HInf.ErrorContinuation`](GoldbachBoundaries/T0HInf/ErrorContinuation.lean) |  | ✓ |  |
| [`GoldbachBoundaries.T0HInf.ExplicitFormula`](GoldbachBoundaries/T0HInf/ExplicitFormula.lean) |  | ● |  |
| [`GoldbachBoundaries.T0HInf.FilteredKernel`](GoldbachBoundaries/T0HInf/FilteredKernel.lean) |  | ✓ |  |
| [`GoldbachBoundaries.T0HInf.FilteredRemainder`](GoldbachBoundaries/T0HInf/FilteredRemainder.lean) |  | ✓ |  |
| [`GoldbachBoundaries.T0HInf.FpBasic`](GoldbachBoundaries/T0HInf/FpBasic.lean) |  | ✓ |  |
| [`GoldbachBoundaries.T0HInf.GammaIntegrals`](GoldbachBoundaries/T0HInf/GammaIntegrals.lean) |  | ✓ |  |
| [`GoldbachBoundaries.T0HInf.InverseFilter`](GoldbachBoundaries/T0HInf/InverseFilter.lean) |  | ✓ |  |
| [`GoldbachBoundaries.T0HInf.InverseMellinDerivative`](GoldbachBoundaries/T0HInf/InverseMellinDerivative.lean) |  | ✓ | ✓ |
| [`GoldbachBoundaries.T0HInf.MellinAssembly`](GoldbachBoundaries/T0HInf/MellinAssembly.lean) |  | ✓ |  |
| [`GoldbachBoundaries.T0HInf.MomentMellin`](GoldbachBoundaries/T0HInf/MomentMellin.lean) |  | ✓ |  |
| [`GoldbachBoundaries.T0HInf.PrimeCorrection`](GoldbachBoundaries/T0HInf/PrimeCorrection.lean) |  | ✓ |  |
| [`GoldbachBoundaries.T0HInf.PrimeCorrectionBounds`](GoldbachBoundaries/T0HInf/PrimeCorrectionBounds.lean) |  | ✓ |  |
| [`GoldbachBoundaries.T0HInf.PrimeExplicitValue`](GoldbachBoundaries/T0HInf/PrimeExplicitValue.lean) |  | ✓ |  |
| [`GoldbachBoundaries.T0HInf.PrimeMellin`](GoldbachBoundaries/T0HInf/PrimeMellin.lean) |  | ● |  |
| [`GoldbachBoundaries.T0HInf.Regularization`](GoldbachBoundaries/T0HInf/Regularization.lean) |  | ● |  |
| [`GoldbachBoundaries.T0HInf.RegularizationIdentity`](GoldbachBoundaries/T0HInf/RegularizationIdentity.lean) |  | ✓ |  |
| [`GoldbachBoundaries.T0HInf.RemainderBoundProof`](GoldbachBoundaries/T0HInf/RemainderBoundProof.lean) |  | ✓ |  |
| [`GoldbachBoundaries.T0HInf.RemainderTransform`](GoldbachBoundaries/T0HInf/RemainderTransform.lean) |  | ✓ |  |
| [`GoldbachBoundaries.T0HInf.RhatProof`](GoldbachBoundaries/T0HInf/RhatProof.lean) |  | ✓ |  |
| [`GoldbachBoundaries.T0HInf.SectorBoundary`](GoldbachBoundaries/T0HInf/SectorBoundary.lean) |  | ● |  |
| [`GoldbachBoundaries.T0HInf.SectorBridge`](GoldbachBoundaries/T0HInf/SectorBridge.lean) |  | ● |  |
| [`GoldbachBoundaries.T0HInf.ZeroCoefficients`](GoldbachBoundaries/T0HInf/ZeroCoefficients.lean) |  | ● |  |
| [`GoldbachBoundaries.T0HInf.ZeroDerivative`](GoldbachBoundaries/T0HInf/ZeroDerivative.lean) |  | ✓ |  |
| [`GoldbachBoundaries.T0HInf.ZeroFilter`](GoldbachBoundaries/T0HInf/ZeroFilter.lean) |  | ✓ |  |
| [`GoldbachBoundaries.T0HInf.ZeroMellin`](GoldbachBoundaries/T0HInf/ZeroMellin.lean) |  | ✓ |  |
| [`GoldbachBoundaries.TBoundary`](GoldbachBoundaries/TBoundary.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.TIdentity.Assembly`](GoldbachBoundaries/TIdentity/Assembly.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.TIdentity.Basic`](GoldbachBoundaries/TIdentity/Basic.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.TIdentity.G7a_ZetaBound`](GoldbachBoundaries/TIdentity/G7a_ZetaBound.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.TIdentity.G7b_LogDerivBound`](GoldbachBoundaries/TIdentity/G7b_LogDerivBound.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.TIdentity.G7c_LogDerivZetaBound`](GoldbachBoundaries/TIdentity/G7c_LogDerivZetaBound.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.TIdentity.G7d_QcontBound`](GoldbachBoundaries/TIdentity/G7d_QcontBound.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.TIdentity.G8b_IntegrableOneLt`](GoldbachBoundaries/TIdentity/G8b_IntegrableOneLt.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.TIdentity.G8c_IntegrableRH`](GoldbachBoundaries/TIdentity/G8c_IntegrableRH.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.TIdentity.G8d_ContourShift`](GoldbachBoundaries/TIdentity/G8d_ContourShift.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.TIdentity.G9a_FwBasic`](GoldbachBoundaries/TIdentity/G9a_FwBasic.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.TIdentity.G9b_MellinFw`](GoldbachBoundaries/TIdentity/G9b_MellinFw.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.TIdentity.G9c_MellinFwSq`](GoldbachBoundaries/TIdentity/G9c_MellinFwSq.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.TIdentity.G9d_MellinInversion`](GoldbachBoundaries/TIdentity/G9d_MellinInversion.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.TIdentity.G9e_SplitQ`](GoldbachBoundaries/TIdentity/G9e_SplitQ.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.TIdentity.G9f_SplitT`](GoldbachBoundaries/TIdentity/G9f_SplitT.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.TIdentity.G9g_HolomorphyIoc`](GoldbachBoundaries/TIdentity/G9g_HolomorphyIoc.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.TIdentity.G9h_HolomorphyIoi`](GoldbachBoundaries/TIdentity/G9h_HolomorphyIoi.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.ThmA.Assembly`](GoldbachBoundaries/ThmA/Assembly.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.ThmA.Defs`](GoldbachBoundaries/ThmA/Defs.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.ThmA.Fill.CCommon`](GoldbachBoundaries/ThmA/Fill/CCommon.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.ThmA.Fill.Dc_access_two`](GoldbachBoundaries/ThmA/Fill/Dc_access_two.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.ThmA.Fill.Dc_eq_diag`](GoldbachBoundaries/ThmA/Fill/Dc_eq_diag.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.ThmA.Fill.Dc_local_two`](GoldbachBoundaries/ThmA/Fill/Dc_local_two.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.ThmA.Fill.ECommonCauchy`](GoldbachBoundaries/ThmA/Fill/ECommonCauchy.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.ThmA.Fill.ECommonDom`](GoldbachBoundaries/ThmA/Fill/ECommonDom.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.ThmA.Fill.ECommonF0`](GoldbachBoundaries/ThmA/Fill/ECommonF0.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.ThmA.Fill.ECommonLf`](GoldbachBoundaries/ThmA/Fill/ECommonLf.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.ThmA.Fill.ECommonLines`](GoldbachBoundaries/ThmA/Fill/ECommonLines.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.ThmA.Fill.F0_mellin`](GoldbachBoundaries/ThmA/Fill/F0_mellin.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.ThmA.Fill.F0_split`](GoldbachBoundaries/ThmA/Fill/F0_split.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.ThmA.Fill.FCommon`](GoldbachBoundaries/ThmA/Fill/FCommon.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.ThmA.Fill.GCommon`](GoldbachBoundaries/ThmA/Fill/GCommon.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.ThmA.Fill.Gb_spec`](GoldbachBoundaries/ThmA/Fill/Gb_spec.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.ThmA.Fill.GeometryCommon`](GoldbachBoundaries/ThmA/Fill/GeometryCommon.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.ThmA.Fill.Gnat_access`](GoldbachBoundaries/ThmA/Fill/Gnat_access.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.ThmA.Fill.Gnat_local`](GoldbachBoundaries/ThmA/Fill/Gnat_local.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.ThmA.Fill.Gnat_spec`](GoldbachBoundaries/ThmA/Fill/Gnat_spec.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.ThmA.Fill.J_spec`](GoldbachBoundaries/ThmA/Fill/J_spec.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.ThmA.Fill.M0_identity`](GoldbachBoundaries/ThmA/Fill/M0_identity.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.ThmA.Fill.N1A_access`](GoldbachBoundaries/ThmA/Fill/N1A_access.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.ThmA.Fill.N1A_local`](GoldbachBoundaries/ThmA/Fill/N1A_local.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.ThmA.Fill.PsegA_split`](GoldbachBoundaries/ThmA/Fill/PsegA_split.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.ThmA.Fill.Pv_eq_Eb_add`](GoldbachBoundaries/ThmA/Fill/Pv_eq_Eb_add.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.ThmA.Fill.Pv_spec`](GoldbachBoundaries/ThmA/Fill/Pv_spec.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.ThmA.Fill.Qcont_pole_split`](GoldbachBoundaries/ThmA/Fill/Qcont_pole_split.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.ThmA.Fill.X_deriv_spec`](GoldbachBoundaries/ThmA/Fill/X_deriv_spec.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.ThmA.Fill.analyticAt_N1A`](GoldbachBoundaries/ThmA/Fill/analyticAt_N1A.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.ThmA.Fill.analyticOn_Dc`](GoldbachBoundaries/ThmA/Fill/analyticOn_Dc.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.ThmA.Fill.catalogue_countable`](GoldbachBoundaries/ThmA/Fill/catalogue_countable.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.ThmA.Fill.catalogue_locallyFinite`](GoldbachBoundaries/ThmA/Fill/catalogue_locallyFinite.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.ThmA.Fill.cauchyEnd`](GoldbachBoundaries/ThmA/Fill/cauchyEnd.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.ThmA.Fill.cauchyInt`](GoldbachBoundaries/ThmA/Fill/cauchyInt.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.ThmA.Fill.cutDisc_facts`](GoldbachBoundaries/ThmA/Fill/cutDisc_facts.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.ThmA.Fill.cuts_locallyFinite`](GoldbachBoundaries/ThmA/Fill/cuts_locallyFinite.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.ThmA.Fill.decomp_exists`](GoldbachBoundaries/ThmA/Fill/decomp_exists.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.ThmA.Fill.differentiableOn_intervalIntegral_of_continuousOn`](GoldbachBoundaries/ThmA/Fill/differentiableOn_intervalIntegral_of_continuousOn.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.ThmA.Fill.exists_Eaux`](GoldbachBoundaries/ThmA/Fill/exists_Eaux.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.ThmA.Fill.exists_component_reaching_line`](GoldbachBoundaries/ThmA/Fill/exists_component_reaching_line.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.ThmA.Fill.exists_continuationAlong_of_uniform`](GoldbachBoundaries/ThmA/Fill/exists_continuationAlong_of_uniform.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.ThmA.Fill.exists_goodSlant_of_countable`](GoldbachBoundaries/ThmA/Fill/exists_goodSlant_of_countable.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.ThmA.Fill.exists_good_discs`](GoldbachBoundaries/ThmA/Fill/exists_good_discs.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.ThmA.Fill.exists_path_into`](GoldbachBoundaries/ThmA/Fill/exists_path_into.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.ThmA.Fill.germ_unique`](GoldbachBoundaries/ThmA/Fill/germ_unique.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.ThmA.Fill.isBranch_uniform_cut`](GoldbachBoundaries/ThmA/Fill/isBranch_uniform_cut.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.ThmA.Fill.isContinuationAlong_concat`](GoldbachBoundaries/ThmA/Fill/isContinuationAlong_concat.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.ThmA.Fill.isPreconnected_Omega_inter`](GoldbachBoundaries/ThmA/Fill/isPreconnected_Omega_inter.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.ThmA.Fill.jump_of_access`](GoldbachBoundaries/ThmA/Fill/jump_of_access.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.ThmA.Fill.logEnd`](GoldbachBoundaries/ThmA/Fill/logEnd.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.ThmA.Fill.logInt`](GoldbachBoundaries/ThmA/Fill/logInt.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.ThmA.Fill.no_analytic_across_log`](GoldbachBoundaries/ThmA/Fill/no_analytic_across_log.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.ThmA.Fill.norm_Eaux_le`](GoldbachBoundaries/ThmA/Fill/norm_Eaux_le.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.ThmA.Fill.slitDisc_facts`](GoldbachBoundaries/ThmA/Fill/slitDisc_facts.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.ThmA.Fill.verticalIntegral_CauchyS_shift`](GoldbachBoundaries/ThmA/Fill/verticalIntegral_CauchyS_shift.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.ThmA.Fill.verticalIntegral_Eb_shift`](GoldbachBoundaries/ThmA/Fill/verticalIntegral_Eb_shift.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.ThmA.G13_Continuation`](GoldbachBoundaries/ThmA/G13_Continuation.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.ThmA.G14_Geometry`](GoldbachBoundaries/ThmA/G14_Geometry.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.ThmA.G15_Kernel`](GoldbachBoundaries/ThmA/G15_Kernel.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.ThmA.G16_Decomp`](GoldbachBoundaries/ThmA/G16_Decomp.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.ThmA.G18_LocalAccess`](GoldbachBoundaries/ThmA/G18_LocalAccess.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.ThmA.G20_Branches`](GoldbachBoundaries/ThmA/G20_Branches.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.ThmA.Skeleton`](GoldbachBoundaries/ThmA/Skeleton.lean) | ✓ | ✓ | ✓ |
| [`GoldbachBoundaries.ZetaRealNonvanishing`](GoldbachBoundaries/ZetaRealNonvanishing.lean) | ✓ | ✓ | ✓ |

## Declaration lookup

All cited project declarations were located. The class-one appendix prints public statements. The class-one README lists the private helpers. The pointwise Gamma identity is `norm_Gamma_half_sq`, a private lemma in [`Phi2/Fill/norm_bKer.lean`](GoldbachBoundaries/Phi2/Fill/norm_bKer.lean). Lean and Mathlib supply the standard axioms, notation, and `RiemannHypothesis`.

An imported module retains five `sorry` placeholders on results outside the cited set: `thm_class_i`, `thm_class_ii`, `rem_class_domain`, `ex_squares` and `ex_S`. [Paper2/Statements.lean](GoldbachBoundaries/Paper2/Statements.lean)
