from pathlib import Path
import json
E=Path(__file__).resolve().parent
rows=json.loads((E/'NCJ_TARGETS.json').read_text())
u12={
'r0::statement_points':('K025/026 successor and K027/028 absorption windows','NCJ_ConstructorPoints.wrapper/source; NCJ_ConstructorSuccessor.source','Full native wrapper/carrier association; no whole native constructor gate.'),
'state_only_statement_points':('K025/026 and K027/028','NCJ_ConstructorPoints.source; exact reverse induction','Native window-to-body association and complete returned record transport.'),
'Weights::box_from_parts':('K045/046 factors; K047/048 points; K049/050 extras','NCJ_BoxParts; NCJ_ArrayWindows; NCJ_BoxWindows','Sparse native windows: full heap allocation, frame, ownership and copy context still required.'),
'Weights::new':('K019/020 factor cell; K041/042 factor-address window','Constructor field totality and statement-points induction','Factor/circle outer recurrence and native constructor call composition remain open.'),
'Weights::pair':('No completed native parent gate','NCJ_PairLength rejects wrong final length before allocation','Same final bytes/kappa/parts, actual guard, all lower calls, Result/errors and receiver frame must compose.'),
'Weights::scalar_factor':('K017/018 post-read closure step','NCJ_ScalarCellTotal; see final Lean index for fold totality','Native permutation/read-to-fragment and full four-step call association, plus powers4 lower bridge.'),
'Weights::tensor':('K015/016 arbitrary prestate one iteration; K043/044 native reverse cursor','NCJ_TensorCellTotal; NCJ_TensorInnerTotal; NCJ_TensorFrame; outer proof status in final index','Full slice/carrier and source fission association; actual native outer-step bridge required.'),
'double':('K013/014 actual frozen loop-free double','NCJ_DoubleAssociation; NCJ_CallLog.repeated_qm; NCJ_ConstructorQM.double','Native primitive add/sub and canonical operand transport; retained lower ports. Two source products are identified only after deterministic Lean substitution.'),
'factored_s2_libra_weights':('K059/060 one post-read term; K061/062 one side update','NCJ_Grouping symbolic algebra; bounds','Actual source read/call association, powers7 and full loop induction/value association.'),
'grouped_inactive_pair':('K029/030 actual GROUPS coefficient step; K031/032 subset; K033/034 contraction; K035/036 kappa step','NCJ_Grouping; index/domain laws','Native stage-to-stage carrier and table/mask composition with same parts/kappa, plus all group-loop induction.'),
'high_dot':('K053/054 actual public Dot push in one call fragment','NCJ_DotInduction; bounded count4','Whole caller source/carrier association, exact same final field and U06 finalization bridge.'),
'partial_dot':('K051/052 actual public Dot push in one call fragment','NCJ_DotInduction; bounded count16','Whole caller source/carrier association, exact same final field and U06 finalization bridge.'),
'process_kind':('No native parent bridge','Scalar/tensor/group/dot component lemmas','Select actual factor row by kind; compose actual callees with their exact domains and preserve errors/scratch/parts.'),
'process_regular_kinds':('K063 TIMEOUT90s; K064 negative failed; NO CREDIT','No complete parent induction','Split one kind call at arbitrary call index plus frame/Lean composition. Process-kind stub is OPEN. Do not rerun K063 unchanged.'),
'push_byte_products':('K055/056 one actual public Dot push source fragment','NCJ_DotInduction; bounded count64','Source buffer index/length and whole loop association; exact U06 receiver/finalization needed.'),
's2_grouped_inactive_pair':('K021/022 common tensor cell; K023/024 low cell; group step windows above','NCJ_Grouping and canonical arithmetic laws','Full low/common/group tensor induction and same outputs/parts; padded-array native carrier association remains open.'),
'shared_high':('K021/022 local common-cell window; dot high step','NCJ_DotInduction; grouping laws','Actual common/high calls, same shared factors and final bytes; whole native loop association.'),
'shared_partials':('K023/024 low-cell window; partial Dot step','NCJ_DotInduction; grouping laws','Actual shared low/partial calls and same final bytes/parts, all loop association.'),
'shared_two_point_guard':('K004/005;006/007;008/009;010/011 actual helper','NCJ_GuardExact.source; NCJ_GuardRejected; NCJ_QEquality','Local helper evidence uses arbitrary relevant raw factors, other fields zero. Arbitrary receiver frame and exact native/cohort error/boolean transport remain explicit.'),
}
u13={
'finish_query_dot':('K057/058 one actual public Dot push call fragment','NCJ_DotInduction; count64<4096','Complete same-message/weights source loop and exact U06 finish reply; no whole-buffer unwinding.'),
'finish_relation':('NOT attempted whole parent: Option<fn> observer quarantine','Component canonicality, field32 bounds, polynomial source port','Two rounds and claim from SAME resume; U12 SAME final/kappa; next22 and actual=rhs; all errors/marks. Native mark observer needs K-2 resolution; no renamed harness.'),
'finish_relation_round':('K037/038 ACTUAL frozen helper under OPEN field/poly stubs','Field/scale/mul laws; Horner source-port induction','Replace decoder and polynomial stubs by CLOSED same-byte callees; associate exact parent context (no separate adopted counterpart). Preserve lhs=claim/4 then Horner and errors.'),
'polynomial':('K039/040 one literal Horner update; K065/066 actual field224; K067/068 actual field2048 windows','NCJ_HornerBytes; NCJ_PolynomialTotal; conditional adopted association if green in final index','Native one-step-to-whole original closure association; exact primitive port mappings to adopted polynomial carrier and byte ownership still explicit. Source port alone is not adopted installation.'),
}
for unit,details in [('U12',u12),('U13',u13)]:
 text=f'# NCJ {unit} bridge ledger\n\n**OPEN.** No complete {unit} native/cohort bridge or headline premise removal is claimed. Frozen Rust `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`; adopted closure authority `AspisR1.RPx_Deployed.deployed` and coherent SInt2 objects. Every listed Lean name requires its green exact-source receipt in NCJ_FINAL_INDEX.json; a draft is not evidence.\n\n'
 text+='| Function | Native evidence | Lean evidence | Exact remaining obligation |\n|---|---|---|---|\n'
 for r in rows:
  if r['bridge_unit']!=unit:continue
  n=r['name'];native,lean,remaining=details[n]
  text+=f'| `{n}` | {native} | {lean} | OPEN: {remaining} |\n'
 text+='\nEach positive credited window has its matched failing control. KMX exact patch SHA256 `bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67`; pointer negative K002, slice negative K070, to_vec negative K069. Windows/fission fragments are not complete parent bridges. Canonical arithmetic products are opaque logs substituted only by the paired Lean theorems in NCJ_LPh_STUBS.md. No Kani multiplication, contracts, SHA implementation or new runtime assumption is used.\n\n'
 text+='The next lane must retain explicit lower hypotheses until merged CLOSED results apply on these exact domains: `NCJ_FilledNative64` (actual successful zeroed64 Vec with same allocation/ownership and Result), `NCJ_Powers4Native` and `NCJ_Powers7Native` (same canonical argument/output carriers; powers29 does not imply these), `NCJ_U06DotNative` (same native receiver history, bounded count, raw accumulation, error/final reply), `NCJ_U01PrimitivePorts` (same native/add/sub canonicality and typed Result maps). These are **named open obligations**, not declarations or assumed CLOSED theorems. Field224/2048 single-window passes narrow decoder data flow; all-context exact callee/carrier/error mapping is still required. NBS/NCB/NBQ/NBG names are not wholesale closure claims.\n'
 (E/f'NCJ_{unit}_BRIDGE.md').write_text(text)
