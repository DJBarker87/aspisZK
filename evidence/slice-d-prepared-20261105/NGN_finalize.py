"""Validate local evidence; emit an OPEN-only additive ledger delta."""
from pathlib import Path
import json,hashlib,re,lzma,subprocess
E=Path(__file__).resolve().parent;J=lambda p:json.loads((E/p).read_text());put=lambda p,x:(E/p).write_text(json.dumps(x,indent=1)+'\n')
roots=J('NGN_AUDIT_ROOTS.json')['groups'][0];raw=J('NGN_audit/batch0/proof0.json');fx=J('NGN_audit/fixtures/fixtures.json');scan=J('NGN_audit/scan/scan.json');allowed={'propext','Classical.choice','Quot.sound'}
assert raw['exit_status']==0 and {r['root'] for r in raw['results']}==set(roots)
assert all(r['equal'] and set(r['walked_axioms'])<=allowed for r in raw['results'])
expected={'NEP_Planted.matcher':'NEP_Planted.matchAx','NEP_Planted.viaPrivate':'NEP_Planted.privateAx','NEP_Planted.proof':'NEP_Planted.proofAx','NEP_Planted.viaAux':'NEP_Planted.auxAx'}
assert fx['exit_status']==0 and len(fx['results'])==8
for r in fx['results']:assert r['equal'] and r['walked_axioms']==([expected[r['root']]] if r['root'] in expected else [])
modules=[json.loads(l) for l in (E/'NGN_LOADED_scan.jsonl').read_text().splitlines()];assert scan['exit_status']==0 and all(not r['dangling'] and not r.get('duplicate_owners',[]) and r['imports_match'] for r in modules)
receipts=[json.loads(p.read_text()) for p in E.glob('NGN_*/receipt.json')];metrics={a:{k:J(a+'/receipt.json').get(k) for k in ['module','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','source_hashes','print_axioms','limits','cgroup_memory_peak_bytes']} for a in ['NGN_E001','NGN_L016','NGN_L019','NGN_L025','NGN_L027','NGN_L033','NGN_L034','NGN_L035','NGN_L036']}
for r in receipts:assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
# Match final admitted source bytes to successful compile snapshots.
for m in ['NGN_Cuts','NGN_Opening','NGN_FrameChain','NGN_RowArithmetic','NGN_EmittedEq','NGN_ScalarDomains','NGN_TypeTransport','NGN_RawTypes','NGN_Emitted','NGN_COMBINED_IMPORT']:
 rs=[r for r in receipts if r['kind']=='lean' and r['module']==m and r['exit_status']==0];assert rs,m
 r=sorted(rs,key=lambda r:r['attempt'])[-1];h=hashlib.sha256((E/(m+'.lean')).read_bytes()).hexdigest();assert r['source_hashes']['NGN_generated/'+m+'.lean']==h,m
put('NGN_AUDIT.json',dict(status='PASS_SUPPORT_ONLY',row_admission=False,new_top_theorems=len(roots)-1,headline='AspisR1.RPx_Deployed.deployed',raw_roots=len(roots),standard_axioms=sorted(allowed),raw_collect_agree=True,fixtures=8,loaded_modules=len(modules),dangling_references=0,duplicate_owner_defects=0,import_baseline_failures=0,source_revision_note='Per-attempt revision plus exact dirty-source snapshot hashes; final admitted source hashes checked against successful receipts',metrics=metrics))
pairs=[]
for a,b,role in [(4,5,'initial'),(6,7,'initial'),(8,9,'initial'),(10,11,'initial'),(12,13,'assignment'),(14,15,'initial')]+[(n,n+1,'strengthened log-frame') for n in [16,18,20,22,24]]+[(26,27,'Box inverted value'),(26,28,'Box wrong allocation'),(29,30,'Box actual value corruption'),(29,31,'Box wrong allocation, matched source')]:
 an=f'NGN_K{a:03d}';bn=f'NGN_K{b:03d}';p=J(an+'/receipt.json');q=J(bn+'/receipt.json');assert p['exit_status']==0 and q['exit_status']!=0
 assert 'VERIFICATION:- SUCCESSFUL' in (E/an/'stdout.log').read_text() and 'VERIFICATION:- FAILED' in (E/bn/'stdout.log').read_text()
 for n in [an,bn]:
  assert J(n+'-graph-check.json')['graph_matches_frozen'] and J(n+'-lock-check.json')['unchanged']
  assert J(n+'-graph-check.json')['graph_sha256']==(E/'NGN_FULL_GRAPH.json.sha256').read_text().strip()
 pairs.append(dict(harness=p['module'],positive=an,control=bn,role=role,local_cut_only=True,callee_law_installed=False))
put('NGN_NATIVE_PAIRS.json',pairs)
matrix=[]
for r in sorted((r for r in receipts if r['kind']=='kani'),key=lambda r:r['attempt']):
 a=r['attempt'];out=(E/a/'stdout.log').read_text();status='PASS_FRAGMENT' if 'VERIFICATION:- SUCCESSFUL' in out else 'MATCHED_CONTROL_FAILURE' if 'VERIFICATION:- FAILED' in out else 'OWN_INPUT_FAILURE'
 matrix.append(dict(attempt=a,harness=r['module'],status=status,exit_status=r['exit_status'],wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],source_revision=r['source_revision'],source_hashes=r['source_hashes'],native_receipt=a+'/receipt.json',graph=a+'-graph-check.json' if (E/(a+'-graph-check.json')).exists() else None,lock=a+'-lock-check.json' if (E/(a+'-lock-check.json')).exists() else None,all_crate_features='NGN_ALL_CRATE_FEATURES.json' if (E/(a+'-graph-check.json')).exists() else None,full_graph_sha256=(E/'NGN_FULL_GRAPH.json.sha256').read_text().strip() if (E/(a+'-graph-check.json')).exists() else None,row_credit=False))
put('NGN_NATIVE_MATRIX.json',dict(attempts=matrix,quarantined_function_pointer_passes=[],suspended_writable_static_passes=[]))
count=dict(kani=len(matrix),lean_support=sum(r['attempt'].startswith('NGN_L') for r in receipts)+1,extraction=sum(r['kind']=='extract' for r in receipts));assert count['kani']<=80 and count['lean_support']<=70 and count['extraction']<=1
put('NGN_BUDGET.json',dict(used=count,limits=dict(kani=80,lean_support=70,extraction=1),prelaunch_own_input_failure='NGN_L030',stopping_below_80_percent_explanation='NGN_REMAINING.md enumerates every stage of the sole assigned member and the exact missing callee laws; no additional independent root is assigned. Passing NFW shapes are reused, never replayed. No whole-success/native-output premise is added.'))
put('NGN_CLOSED.json',dict(new_composed_rows=[],newly_closed_count=0,prepared_new='OPEN',prepared_claim_installation='OPEN',supportive_roots=len(roots)-1,route_attempted='ai',native_model_composition_complete=False))
gaps=J('NGN_CALLEE_GAPS.json');parent=next(r for r in gaps['rows'] if r['row']=='TX1:179')
put('NGN_EDGES.json',dict(caller_row='TX1:179',edges=[dict(caller=parent['function'],callee=c['callee'],status='OPEN_NATIVE_ASSOCIATION',required_named_hypotheses=c['required_named_hypotheses'],model_stage_chain='NGN_Opening.source + NGN_Cuts.source + NGN_FrameChain',reason='Named native callee/domain law not installed on the same execution; source/model fragments do not close a composed edge') for c in parent['callees']]))
put('NGN_LEDGER_DELTA.json',dict(basis='NGJ_LEDGER.json on 599-row NGB inventory',basis_sha256=gaps['source_sha256'],row_changes=[],newly_closed_count=0,retained_open_rows=['TX1:179','TX1:193'],route='attempted(ai); no CLOSED tag',trust_removed=[],trust_added=[],transport='Existing P6/D188 option-A semantic transport retained/reclassified; never removal',headline_target_established=False))
print(json.dumps(dict(audit='PASS_SUPPORT_ONLY',new_theorems=len(roots)-1,modules=len(modules),native_pairs=len(pairs),budget=count,new_rows=0)))
