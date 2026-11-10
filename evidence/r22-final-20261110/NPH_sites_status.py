#!/usr/bin/env python3
"""NPH_ (run of 2026-11-10 evening): annotate the tightened screen (NPH_sites_scan2.py) with the
per-site status of this run and the direct callers of each site (its contexts), and write the
checklist NPH_SITES.json. status values:
  W_LEMMA          a Lean lemma proves: W inputs at the site give ok W outputs (every kernel call
                   inside receives W arguments); the site's own inputs come from its contexts.
  EVERY_INPUT      a Lean lemma proves the site ok with W output for every input (a frontier).
  JOINED_094       the 094 query-path join of NPH_R22Join094/Join094Step discharges the inputs.
  NOT_EXECUTING    the declaration is a Prop-valued predicate (no execution).
  OPEN             no lemma in this packet.
A family's kernels move to judgment (b) only when every site is EVERY_INPUT, JOINED or
NOT_EXECUTING, or is W_LEMMA with every context closed in turn. Usage:
NPH_sites_status.py CONE.json OLD_SITES.json OUT.json SRC_DIR"""
import sys,json,runpy
g=runpy.run_path(__file__.replace('NPH_sites_status.py','NPH_sites_scan2.py'),run_name='nph_scan')
out=json.load(open(sys.argv[3]));refs=g['refs']
callers={}
for k,v in refs.items():
  for c in v: callers.setdefault(c,set()).add(k)
P='AspisR1.NPH_R22'
L={  # site -> (status, lemma)
 # CW in-family (tower)
 'AspisR1CurrentWide.field.CM31.add':('W_LEMMA',P+'Producers.CW_CM31_add_weak'),
 'AspisR1CurrentWide.field.CM31.sub':('W_LEMMA',P+'Producers.CW_CM31_sub_weak'),
 'AspisR1CurrentWide.field.M31.double':('W_LEMMA',P+'Producers.CW_M31_double_weak'),
 'AspisR1CurrentWide.field.QM31.add':('W_LEMMA',P+'Producers.CW_QM31_add_weak'),
 'AspisR1CurrentWide.field.QM31.mul':('W_LEMMA',P+'Producers.CW_QM31_mul_weak'),
 'AspisR1CurrentWide.field.QM31.sub':('W_LEMMA',P+'Producers.CW_QM31_sub_weak'),
 'AspisR1CurrentWide.field.mul_by_r':('W_LEMMA',P+'Producers.CW_mul_by_r_weak'),
 'AspisR1CurrentWide.field.wide_exact.WideExact.add':('W_LEMMA',P+'Callbacks.CW_WideExact_add_weak'),
 'AspisR1CurrentWide.field.wide_exact.WideExact.mul':('W_LEMMA',P+'Callbacks.CW_WideExact_mul_weak'),
 'AspisR1CurrentWide.field.wide_exact.WideExact.sub':('W_LEMMA',P+'Callbacks.CW_WideExact_sub_weak'),
 'AspisR1CurrentWide.field.wide_exact.mul_u':('W_LEMMA',P+'Callbacks.CW_mul_u_weak'),
 'AspisR1CurrentWide.Proof.finishAdd':('W_LEMMA',P+'JoinCW.finishAdd_W'),
 'AspisR1CurrentWide.Proof.finishArithmetic':('OPEN','record builder; its add slot is finishAdd (finishAdd_W); record-level statement not written'),
 'AspisR1CurrentWide.Proof.finishCheckedArithmetic':('OPEN','record builder over finishArithmetic'),
 'AspisR1CurrentWide.Proof.finishConcreteField':('OPEN','record builder over finishCheckedArithmetic'),
 'AspisR1.FIn_Polynomial.mul':('W_LEMMA',P+'JoinCW.FIn_mul_W'),
 'AspisR1.FIn_Primitives.add':('W_LEMMA',P+'JoinCW.FIn_add_W'),
 'AspisR1.FIp_CircleSource.circle':('W_LEMMA',P+'Callbacks.CircleSource_circle_W'),
 'AspisR1.SAQ_LineSource.line':('W_LEMMA',P+'Callbacks.LineSource_line_W'),
 'AspisR1.SAQ_Arithmetic.add':('W_LEMMA',P+'Callbacks.SAQ_Arithmetic_add_W'),
 'AspisR1.SAQ_Arithmetic.mulK':('W_LEMMA',P+'Callbacks.SAQ_Arithmetic_mulK_W'),
 'AspisR1.SAQ_MixedSource.source':('W_LEMMA',P+'Callbacks.SAQ_MixedSource_source_W'),
 'AspisR1CurrentPreparedClaim.aspis_core.field.WideExact.add':('W_LEMMA',P+'JoinCW.claimAdd_W'),
 'AspisR1CurrentPreparedClaim.aspis_core.field.WideExact.mul':('W_LEMMA',P+'JoinCW.claimMul_W'),
 'AspisR1.SAG_DotAdapter.kernel':('OPEN','finish_query_dot under finishConcreteField: dot loop walk not done'),
 'NHE_DotBody.ops':('OPEN','record over finishConcreteField; no reached definition calls it'),
 # SM
 'AspisR1SelectedMaskProbe.field.CM31.add':('W_LEMMA',P+'Towers.SM_CM31_add_weak'),
 'AspisR1SelectedMaskProbe.field.CM31.double':('W_LEMMA',P+'Towers.SM_CM31_double_weak'),
 'AspisR1SelectedMaskProbe.field.CM31.sub':('W_LEMMA',P+'Towers.SM_CM31_sub_weak'),
 'AspisR1SelectedMaskProbe.field.M31.double':('W_LEMMA',P+'Towers.SM_M31_double_weak'),
 'AspisR1SelectedMaskProbe.field.QM31.add':('W_LEMMA',P+'Towers.SM_QM31_add_weak'),
 'AspisR1SelectedMaskProbe.field.QM31.mul':('W_LEMMA',P+'Towers.SM_QM31_mul_weak'),
 'AspisR1SelectedMaskProbe.field.QM31.square':('W_LEMMA',P+'Towers.SM_QM31_square_weak'),
 'AspisR1SelectedMaskProbe.field.mul_by_r':('W_LEMMA',P+'Towers.SM_mul_by_r_weak'),
 'AspisR1SelectedMaskProbe.field.QM31.sub':('W_LEMMA',P+'JoinSM.QM31_sub_W'),
 'AspisR1SelectedMaskProbe.field.PreparedQm31Multiplier.mul':('W_LEMMA',P+'JoinSM.PM_mul_W (any prepared value; W right operand)'),
 'AspisR1SelectedMaskProbe.field.PreparedQm31Multiplier.mul.closure.Insts.CoreOpsFunctionFnPairArrayM313CM31CM31.call':('W_LEMMA',P+'JoinSM.PM_mul_closure_W'),
 'AspisR1SelectedMaskProbe.field.PreparedQm31Multiplier.new':('W_LEMMA',P+'JoinSM.PM_new_ok'),
 'AspisR1SelectedMaskProbe.field.PreparedQm31Multiplier.new.closure.Insts.CoreOpsFunctionFnTupleCM31ArrayM313.call':('W_LEMMA',P+'JoinSM.PM_new_closure_ok'),
 'AspisR1SelectedMaskProbe.state_only_hiding.cm31_mul_i':('W_LEMMA',P+'JoinSM.mul_i_W'),
 'AspisR1SelectedMaskProbe.state_only_hiding.cm31_mul_r':('W_LEMMA',P+'JoinSM.mul_r_W'),
 'AspisR1SelectedMaskProbe.state_only_hiding.mul_tower_basis':('W_LEMMA',P+'JoinSM.basis_W (coordinate < 4)'),
 'AspisR1SelectedMaskProbe.state_only_hiding.mask_power_26':('W_LEMMA',P+'JoinSM.power26_W'),
 'AspisR1SelectedMaskProbe.state_only_hiding.selected_mask_linears_loop.body':('W_LEMMA',P+'JoinSM.linears_body_site (one iteration; W state, W point array)'),
 'AspisR1SelectedMaskProbe.state_only_hiding.selected_mask_linears':('W_LEMMA',P+'JoinSM.linears_tail (tail after the loop; loop composition not stated)'),
 'AspisR1SelectedMaskProbe.state_only_hiding.state_only_selected_mask_value_loop0.body':('W_LEMMA',P+'JoinSM.coeff_site (W c1 array)'),
 'AspisR1SelectedMaskProbe.state_only_hiding.state_only_selected_mask_value_loop1.body':('W_LEMMA',P+'JoinSM.coeff_site pattern (W mask_only_c1 array); not separately stated'),
 'AspisR1SelectedMaskProbe.state_only_hiding.state_only_selected_mask_value_loop2.body':('W_LEMMA',P+'JoinSM.loop2_body_site (W coefficient array)'),
 'AspisR1SelectedMaskProbe.state_only_hiding.state_only_selected_mask_value':('W_LEMMA',P+'JoinSM.mask_tail_sites (prepare and tail; the coefficient-array invariant across loop0/loop1 updates and the loop compositions are not stated)'),
 'AspisR1.FIp_SemanticArithmetic.add':('W_LEMMA',P+'JoinSM.FIp_add_W'),
 'AspisR1.FIp_SemanticArithmetic.mul':('W_LEMMA',P+'JoinSM.FIp_mul_W'),
 'AspisR1.FIp_SemanticArithmetic.mask':('OPEN','wrapper of state_only_selected_mask_value; inputs c1, mask_only_c1, g, point from the semantic-boundary caller'),
 'AspisR1.PoseidonPreparedProductCells.rightBuilder':('W_LEMMA',P+'JoinSM.rightBuilder_ok (no reached definition calls it)'),
 'AspisR1PoseidonPreparedSum3Source.field.qm31_sum_products3_prepared_loop0':('W_LEMMA',P+'JoinSM.sum3_step_site (W right entry)'),
 'AspisR1PoseidonPreparedSum3Source.field.qm31_from_karatsuba_channel_sums':('EVERY_INPUT',P+'JoinSM.karatsuba_W'),
 'AspisR1PoseidonPreparedSum3Source.field.qm31_from_karatsuba_channel_sums.closure.Insts.CoreOpsFunctionFnTupleArrayU643CM31.call':('EVERY_INPUT',P+'JoinSM.karatsuba_closure_W'),
 'AspisR1.ExtractedMaskPreparedState.PreparedFor':('NOT_EXECUTING','Prop-valued predicate'),
 'AspisR1.ExtractedMaskCoefficientLoop0.writeAt0':('W_LEMMA',P+'JoinSM.coeff_site (model of loop0; same call)'),
 'AspisR1.ExtractedMaskCoefficientLoop1.writeAt1':('W_LEMMA',P+'JoinSM.coeff_site pattern (model of loop1)'),
 'NBO_FieldSemantics.add':('JOINED_094',P+'Join094.tail_sites'),
 'NBO_FieldSemantics.product':('JOINED_094',P+'Join094.tail_sites'),
 'NBO_FieldSemantics.power':('JOINED_094',P+'Join094.tail_sites'),
 # QA
 'AspisR1Qm31ArithmeticProbe.field.CM31.add':('W_LEMMA',P+'Producers.QA_CM31_add_weak'),
 'AspisR1Qm31ArithmeticProbe.field.CM31.sub':('W_LEMMA',P+'Producers.QA_CM31_sub_weak'),
 'AspisR1Qm31ArithmeticProbe.field.M31.double':('W_LEMMA',P+'Producers.QA_M31_double_weak'),
 'AspisR1Qm31ArithmeticProbe.field.QM31.add':('W_LEMMA',P+'Producers.QA_QM31_add_weak'),
 'AspisR1Qm31ArithmeticProbe.field.QM31.mul':('W_LEMMA',P+'Producers.QA_QM31_mul_weak'),
 'AspisR1Qm31ArithmeticProbe.field.mul_by_r':('W_LEMMA',P+'Producers.QA_mul_by_r_weak'),
 'AspisR1CurrentWideMul.field.QM31.add':('W_LEMMA','alias of QA QM31.add: '+P+'Producers.QA_QM31_add_weak'),
 'AspisR1CurrentWideMul.field.QM31.mul':('W_LEMMA','alias of QA QM31.mul: '+P+'Producers.QA_QM31_mul_weak'),
 'AspisR1CurrentWideMul.field.cm.CM31.sub':('W_LEMMA','alias of QA CM31.sub: '+P+'Producers.QA_CM31_sub_weak'),
 'AspisR1CurrentWideMul.field.mul_by_r':('W_LEMMA','alias of QA mul_by_r: '+P+'Producers.QA_mul_by_r_weak'),
 'AspisR1CurrentWideMul.field.QM31.sub':('W_LEMMA',P+'JoinQA.CWM_QM31_sub_W'),
 'AspisR1CurrentWideMul.field.wide_exact.mul_u':('W_LEMMA',P+'JoinQA.CWM_mul_u_W'),
 'AspisR1CurrentWideMul.field.wide_exact.WideExact.mul':('W_LEMMA',P+'JoinQA.CWM_WideExact_mul_W'),
 'NFN_NEB_GeometryPrimitives.install':('W_LEMMA',P+'JoinQA.NFN_install_W (slots op7-op10)'),
 'NFN_NEW_GeometryPolynomial.cohort':('EVERY_INPUT',P+'JoinQA.cohort_W'),
 'AspisR1.SAQ_Geometry.install':('W_LEMMA',P+'Installers.SAQ_Geometry_install_W'),
 'AspisR1.SAQ_Query.install':('W_LEMMA',P+'Installers (QueryM31W)'),
 'LIBC_QueryOps.seed':('W_LEMMA',P+'Installers (QueryM31W); 094 node sites JOINED in Join094'),
 'NJJ_QueryOps.concrete':('W_LEMMA',P+'Installers (QueryM31W); 094 node sites JOINED in Join094'),
 'NBF_BasisInstall.install':('W_LEMMA',P+'Installers (QueryM31W); 094 node sites JOINED in Join094'),
 'R17CurrentCM31Semantics.operations':('W_LEMMA',P+'Installers.R17 CM31 operations'),
 'R17CurrentM31Semantics.operations':('W_LEMMA',P+'Installers.R17_M31_operations_W'),
 'S7Kani3BasisOuter.double':('W_LEMMA',P+'Installers.S7_double_pres'),
 'S7Kani3BasisOuter.t2':('W_LEMMA',P+'Installers.S7_t2_pres'),
}
summ=out['_summary']
for f in ['CW','QA','SM','SC','FIq','R72']:
  for y in out[f]:
    st,lem=L.get(y['site'],('OPEN','not examined in this run'))
    y['status']=st;y['lemma_or_reason']=lem
    y['contexts_direct_callers']=sorted(callers.get(y['site'],[]))
  c={}
  for y in out[f]: c[y['status']]=c.get(y['status'],0)+1
  summ[f]['status_counts']=c
  summ[f]['family_complete_for_b']=False
out['_summary']=summ
out['_rulings']={'1':'R65/R66 proof-only references are NOT_EXECUTED in NPH_R22_CONE.json (no site list)','2':'tightened screen: in-family callers, hand-written wrappers under the family namespace, open/namespace name resolution, one alias level; sources from the replayed L187 src tree'}
out['_contexts_open']={
 'CW':['Stage2 finish round alpha = p.alpha[0], p.alpha[1] of the finish Prepared (round_sites needs WE alpha)','finish dot: SAG_DotClosed.source / SAG_DotAdapter.kernel (finish_query_dot under finishConcreteField)','FIn_Install.finishOps <- FIn_WeightsInstall.install','CurrentPreparedClaim sum loops (prepared_claim_sum, owned_sum, borrowed_abi.owned_sum): accumulator and term invariant','query dictionaries other than the 094 Dcon/Dsel: NJJ_Common.query, NNH_Tx2SourceConfiguration.fill, NNH_HostSeed.m0, NNH_Run5bQuerySlots.model, NNX_QueryOutput.run, LIBC_QueryLoop.model, NFS_QueryOps.base, SAQ_LineQuery.install, FIp_Install.select, SAQ_QuerySource.install (op16/op17 line/circle, op2/op3/op9 where not replaced by NFS_QueryOps.installed)'],
 'SM':['FIp_SemanticArithmetic.install / IDa_Deployed.boundaries / NNG_InstallArithmetic / NNG_LegacyConfig136.boundaries / NNG_ModelMask.call: W of the semantic-boundary operands and of the mask inputs c1, mask_only_c1, g, point','state_only_selected_mask_value: ArrW of the 27-entry coefficient array after the loop0/loop1 updates (Array.repeat ZERO then W writes), and the loop compositions','qm31_sum_products3_prepared (loop0 callers, FJe_Sum3IndexBridge.old, PoseidonPreparedIndex* loops): W of the right operands'],
 'QA':['NFN_NEB_GeometryPrimitives.install op14/op15 under NFN_NEA_FieldProduct.ops','installer contexts outside 094 (the Installers W-lemmas are conditional on the arguments the gate passes)','CurrentWideMulCanonical WideExact.mul callers'],
}
json.dump(out,open(sys.argv[3],'w'),indent=1)
for f in ['CW','QA','SM','SC','FIq','R72']: print(f,summ[f]['sites'],summ[f]['status_counts'])
