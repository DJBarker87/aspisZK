from pathlib import Path
import json,lzma,hashlib
E=Path(__file__).resolve().parent;F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
load=lambda n:json.loads((E/n).read_text())
scan=[json.loads(l)for l in (E/'NGM_LOADED_scan.jsonl').read_text().splitlines()]
proof=load('NGM_final_audit/proof0.json');fixtures=load('NGM_final_audit/fixtures.json')
assert proof['exit_status']==fixtures['exit_status']==0 and len(proof['results'])==18 and len(fixtures['results'])==8
assert all(set(x['walked_axioms'])==set(x['collect_axioms'])<={'propext','Classical.choice','Quot.sound'}for x in proof['results'])
assert all(not r['dangling']and not r['duplicate_owners']and r['imports_match']for r in scan)
audit=dict(status='PASS stage2 focused cached composition',combined='NGM_COMBINED_IMPORT',combined_attempt='NGM_L018',raw_attempt='NGM_L021',scan_attempt='NGM_L022',raw_roots=len(proof['results']),same_binary_fixtures=8,standard_axioms_only=True,modules=len(scan),dangling=0,incompatible_owners=0,import_mismatches=0,prior_scan_failure='NGM_L021: own implicit Init baselines repaired, scan only rerun; no validation weakened',cold_release_replay=False)
(E/'NGM_AUDIT.json').write_text(json.dumps(audit,indent=2)+'\n')
f='crates/aspis-r1-cost-probe/src/weights.rs::shared_two_point_guard'
c=dict(function=f,rows=['TX2:145'],status='CLOSED',form='ruling (y) exact native contract and raw-word reference',domain='SAME complete Weights record, arbitrary raw u32 limbs, all variants and usize folds; no canonicality precondition',native_positive='NGM_K001',matched_control='NGM_K002',copy_pair=['NGM_K003','NGM_K004'],lean_root='NGM_GuardRawModel.cohort',axioms=['propext','Classical.choice','Quot.sound'],frame='empty modifies; borrowed readonly input; no callback, allocation, multiplication or protocol event',inner_hypotheses_remaining=[],extraction='reused NDL_GuardRef; reference qeq_ref/roweq_ref/guard_raw_ref preserved; prefix-only Lean extraction namespace changes; provenance NGM_NATIVE_PROVENANCE.json',trust='P6/D188 option A retained/reclassified; nothing removed')
(E/'NGM_CLOSED.json').write_text(json.dumps(dict(schema_version=1,frozen_revision=F,new_composed_functions=1,new_composed_rows=1,driver_root_status='OPEN',functions=[c]),indent=2)+'\n')
delta=dict(baseline='evidence/ledger8-20261105/NGJ_LEDGER.json.xz',new_closed_rows=['TX2:145'],new_count=1,rows=[dict(row='TX2:145',function=f,before='OPEN',after='CLOSED')],no_other_status_change=True,not_a_premise_retirement=True,trust_reclassification='P6/D188 option A retained; never removed',validator_checks_added=['frozen source identity','fresh frozen resolved graph every native run','identical lock before/after','deployed feature parity','matched native and KMX controls','empty modifies','reference/cohort equality on full raw record','headline combined replay','standard raw ax2 audit with same-binary fixtures','zero-defect NFX-style scan'])
(E/'NGM_LEDGER_DELTA.json').write_text(json.dumps(delta,indent=2)+'\n')
(E/'NGM_EDGES.json').write_text(json.dumps(dict(closed_edges=[],reason='Guard has no inventory callees. TX2 write-back is a checked model boundary fragment; the actual NFW caller is not promoted.',boundary_theorem='AspisR1.NGM_FinishDomain.tx2_writeback'),indent=2)+'\n')
(E/'NGM_BRIDGES.md').write_text('''# NGM bridge checkpoint

CLOSED: shared_two_point_guard, TX2:145. The actual frozen helper is checked against the retained safe raw-word reference, with empty modifies, fresh deployed-feature graph and frozen lock on every run, matched failure and exact KMX copy controls. NGM_GuardRawModel.cohort proves reference = canonical emitted function on the SAME full raw Weights record and arbitrary folds. No inner callee-domain hypothesis remains. Native contract transport retains P6/D188 option A.

Model-only boundary: NGM_QueryExit.tx2 and NGM_FinishDomain.tx2_writeback derive the SAME accepted query-loop poststate and exact flush/reconstruction predicate; see NGM_DOMAIN.md. These do not close tx2_common.

OPEN caller fragment: K005..K022 check full finish control Result, arguments and order with unconstrained full child replies. The source-fission erasure has four rejected mutations. Their simple inverted-assertion controls are being strengthened to reached-argument/child-reply corruptions before final use. One rename-stability pair is included under (ae). NGM_FinishControl.source is exact emitted-source equality preserving every rejection/runtime Result branch; it does not discharge callbacks or equal the separately extracted reference yet.

Exploratory Lean failures L001/L013..L016 are excluded. L001 tried a legacy polynomial import; the replacement uses canonical owners. L013..L016 failed a factored source normal form; L017 preserves the exact emitted branching body and compiles. No failed elaboration or its diagnostic sorryAx is a proof credit. Source contains no admissions.

The replay L018 includes NGJ_VERIFIER_IMPORT and the deployed headline; L021 raw-walks18 roots and validates8 fixtures in the same optimized binary. The L021 scan had only omitted implicit Init import baselines. Source-derived repair retains exact import equality; scan-only L022 has13387 modules, zero defects. This is a cached coherent hybrid packet, not a cold release replay or a security theorem.
''')
with (E/'NGM_HANDOFF.md').open('a')as out:out.write('''
Stage2 focused checkpoint: one new CLOSED row, TX2:145 shared_two_point_guard. Native K001/002 and KMX003/004; raw18 roots standard, same-binary8 fixtures, scanner13387 modules zero defects. Model TX2 write-back/domain derivation compiles. Full acceptance-tail roots remain OPEN. K005..022 are preliminary control fragments; stronger reached-argument/reply controls and independent double support are next. The NGM_Double* and NGM_ProbeTransport files are uncompiled candidates at this checkpoint. Budget charged so far:22 Kani,22 Lean/audit,1 extraction. All receipts retained. Work continues; this is not an early stop.
''')
graph=load('NGM_TAIL_GRAPH.json')
reasons={
'finish_relation':'Needs strengthened native control controls, extracted-reference/cohort association, all CLOSED callee packets and their SAME-call domains; Weights::new/pair remain OPEN. Exact final Result is checked as a caller-control fragment, not promoted.',
'finish_query_dot':'Needs typed source-step transport to canonical EbyKDot, finite induction with abort prefixes, new/finish association, and exact adopted SAG dot model equality.',
'finish_relation_round':'Needs opaque mul_m31 paired law, exact byte fields, native branch/control packet, polynomial packet and full Result/cohort association.',
'polynomial':'Needs one native Horner iteration, paired opaque WideExact.mul law, canonical coefficient/domain propagation and seven-step emitted-model induction.',
'Weights::new':'Needs statement_points, factor loops, double, boxed-record source/value/error/frame association; SAME canonical semantic-alpha/z producers are NFW boundaries.',
'Weights::pair':'Needs tensor/guard/libra/grouped/scalar/dot helper packets, all source-ordered branches and exact caller-domain transport.',
'Weights::box_from_parts':'Needs native owned record move/allocation/error/frame and emitted constructor association; no allocation availability assumption.',
'double':'Independent canonical-input helper: local opaque two-product observation packet and paired total natural product law plus emitted model/reference association pending.',
'shared_two_point_guard':'CLOSED by NGM_GuardRawModel.cohort and K001..004; no internal callees.',
'QM31::square':'Ledger8 OPEN; subsequent merged NGH packet is CLOSED on same canonical receiver, must be revalidated/imported with provenance before use; never duplicate proof.',
'powers':'NFW caller boundary: import its committed canonical packet read-only if CLOSED and revalidated; do not duplicate.'}
lines=['# NGM TX2 acceptance tail','', 'Target not yet established. No complete entry-to-accepted-spend path is closed.','', 'The exact incoming accumulator predicate is NGM_FinishDomain.AccumulatorDomain. Remaining Prepared/view producer predicates and the distinction between native-control and child domains are in NGM_DOMAIN.md.','']
remaining=[]
for r in graph:
 if r['status']!='OPEN':continue
 name=r['function'].split('.rs::')[-1];reason=reasons.get(name,'Needs source-ordered native local-record/one-iteration packet with matched controls, exact emitted-model/reference association, and SAME caller/callee domain/frame composition. Its dependencies in NGM_TAIL_GRAPH.json are not assumed CLOSED.')
 status='CLOSED'if name=='shared_two_point_guard'else'OPEN';lines+=['## '+r['row']+' '+name,'',status+': '+reason,''];remaining.append(dict(row=r['row'],function=r['function'],status=status,obligation=reason))
(E/'NGM_TX2_TAIL.md').write_text('\n'.join(lines));(E/'NGM_REMAINING.md').write_text('# NGM remaining work — active\n\nNo budget stop; work continues.\n\n'+'\n\n'.join(r['row']+' '+r['function']+': '+r['obligation']for r in remaining if r['status']=='OPEN')+'\n')
(E/'NGM_REMAINING.json').write_text(json.dumps(remaining,indent=2)+'\n')
