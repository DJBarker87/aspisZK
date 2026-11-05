from pathlib import Path
import json,hashlib,lzma,collections,re
E=Path(__file__).resolve().parent;R=E.parents[1]
J=lambda p:json.loads(Path(p).read_bytes())
def put(n,x):(E/n).write_text(json.dumps(x,indent=1)+'\n')
# Preserve conservatively charged prelaunch refusals, separate from actual scopes.
pre=J(E/'NHH_PRELAUNCH.json');p=E/'NHH_L036/sources/NHH_generated/NHH_QBridge.lean';q=E/'NHH_L034-input-source.lean.txt';q.write_bytes(p.read_bytes())
if not any(x['attempt']=='NHH_L034'for x in pre):pre.append(dict(attempt='NHH_L034',module='NHH_QBridge',kind='prelaunch-input-rejection',charged_lean_attempt=True,compiler_launched=False,exit_status=1,wall_seconds=None,peak_rss_kib=None,swaps=None,source_sha256=hashlib.sha256(q.read_bytes()).hexdigest(),source_snapshot=q.name,print_axioms='N/A: no compiler launch',reason='private dependency preflight refused the not-yet-green QTrace object'))
put('NHH_PRELAUNCH.json',pre)
receipts=[J(p)for p in E.glob('NHH_[KL][0-9][0-9][0-9]/receipt.json')];actual={r['attempt']:r for r in receipts};assert len(actual)==len(receipts)
assert set(actual)|{r['attempt']for r in pre}=={f'NHH_K{k:03}'for k in range(1,79)}|{f'NHH_L{k:03}'for k in range(1,50)}
limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
assert all(r['limits']==limits and str(r['swaps'])=='0'for r in receipts)
assert len(receipts)==124 and len(pre)==3
assert all('-M7000'in r['command']for r in receipts if r['kind']=='lean')
put('NHH_BUDGET.json',dict(authorized={'kani':80,'lean_and_support':70,'extraction':2},charged={'kani':78,'lean_and_support':49,'extraction':0},actual_scopes={'kani':78,'lean_and_support':46},prelaunch_refusals=[x['attempt']for x in pre],remaining={'kani':2,'lean_and_support':21,'extraction':2},all_scopes_terminal=True,resource_limits=limits,peak_rss_kib=max(int(r['peak_rss_kib'])for r in receipts),all_swap_zero=True,timeout_or_memory_kills=[],unchanged_timeout_reruns=0,budget_disposition='Not exhaustion. Every target is attempted; only generic K-2 native semantics and missing adopted neg endpoint remain. NHH_REMAINING.md accounts for each member. No remaining Lean-only field-law obligation is held behind a native budget.'))
accepted={'Embedding':4,'BaseOps':10,'ScalarDomain':11,'EncodedScalar':13,'CMInverse':15,'CMTrace':16,'CMSampler':20,'CMAlgebra':21,'CMBridge':22,'AllScalar':25,'CMAll':27,'QInverse':26,'QAll':32,'QTrace':35,'QBridge':37,'QNeg':40,'StubDomains':38,'InverseOutcomes':46}
items=[]
for m,n in accepted.items():
 name='NHH_'+m;rc=actual[f'NHH_L{n:03}'];src=E/(name+'.lean');snap=E/f'NHH_L{n:03}'/'sources/NHH_generated'/(name+'.lean');assert src.read_bytes()==snap.read_bytes()and rc['exit_status']==0
 assert all('sorryAx'not in l for l in rc['print_axioms']);items.append(dict(module=name,source=str(src.relative_to(R)),sha256=hashlib.sha256(src.read_bytes()).hexdigest(),accepted_attempt=rc['attempt'],receipt=f"{rc['attempt']}/receipt.json",print_axioms=rc['print_axioms']))
put('NHH_PROOF_SOURCES.json',dict(status='PASS',modules=items,explicit_top_theorems=112,final_raw_audit='NHH_L049',not_a_cold_release_replay=True))
base=json.loads(lzma.decompress((R/'evidence/ledger9-20261105/NGZ_LEDGER.json.xz').read_bytes()));d=J(E/'NHH_LEDGER_DELTA.json');closed=set(d['new_closed_rows']);target=J(E/'NHH_TARGETS.json')['rows'];byfn={f['function']:f for f in J(E/'NHH_CLOSED.json')['functions']}
lines=['# NHH remaining targets and budget disposition','','12/14 target occurrences are CLOSED under conditional hybrid semantics. The deployed100-bit per-attempt target is not established. No broad security/runtime/compiler/source-to-ELF premise was removed.','','| Row | Exact function | Final state and remaining admissible action |','|---|---|---|']
for r in target:
 if r['row']in closed:reason='CLOSED: '+byfn[r['function']]['model_root']+'. No local obligation remains; an unchanged replay would add no evidence.'
 elif r['row']=='TX1:006':reason='OPEN: full arbitrary-backend checked Result model NHH_CMAll.inv_with is proved. Only inv_with(M31::inv) has an admitted native packet. Generic native function-pointer credit remains quarantined under K-2; no additional Lean field law or admitted generic native shape can close it. Needs a lead-approved fidelity/semantic route.'
 else:reason='OPEN: canonical native K055/056 and complete four-coordinate model NHH_QNeg.canonical_result are proved. L041 finds zero adopted headline *.QM31.neg endpoints. Needs an actual existing enclosing dictionary/model association or separately reviewed authoritative reachability disposition. Another standalone value proof or extraction would repeat the rejected shape.'
 lines.append('| '+r['row']+' | '+r['function']+' | '+reason+' |')
lines+=['','Charged78/80 Kani,49/70 Lean/support (46 actual scopes plus3 prelaunch refusals),0/2 extraction. These are not exhaustion claims. All14 members were attempted. The two independent OPEN units have complete permitted model support; their remaining conditions are external interface/tool admission, not another multiplication proof, larger cap or unrelated callee. No remaining admitted member could be attempted to close a row using the unused2 native/21 Lean/2 extraction slots. Re-extracting unchanged source cannot create an adopted endpoint or lift K-2. A generic pointer experiment remains quarantined and cannot close the row; a fresh stand-in is not an adopted endpoint.','', 'The final source-identity receipt was initially missing; K045–078 re-established the final native pairs under735-file hashing, frozen offline dependencies, deployed features, exact KMX patch and direct argument controls. No timeout, memory kill, cap raise or unchanged killed/timed-out rerun occurred.','', 'All proof and audit scopes are terminal. No shipped source, key, wallet, account, ELF, session-A/sibling worktree or security contract changed. No push.']
(E/'NHH_REMAINING.md').write_text('\n'.join(lines)+'\n')
rev=collections.defaultdict(set)
for r in base['rows']:
 for c in r['canonical_callees']:rev[c].add(r['function'])
lines=['# NHH source-boundary consumers','','The following reachability is from the unchanged NGZ conservative graph. It identifies potential driver cones, not actual call instances or driver closure. Typed alternatives remain explicit in NHH_SOURCE_GRAPH_FINDING.md and NHH_EDGES.json.','']
for f in J(E/'NHH_CLOSED.json')['functions']:
 seen=set();todo=[f['function']]
 while todo:
  n=todo.pop()
  for p in rev[n]:
   if p not in seen:seen.add(p);todo.append(p)
 drivers=sorted(n for n in seen if any(t in n for t in ['Prepared::new','::prepare','::tx1','::tx2_common','::finish_relation','::verify_observed','::process_r1_cost_probe_instruction','Transcript<H>::queries','QueryGeometry::for_range','::query_loop','::accumulate_batched_with_node']))
 lines+=['## '+f['function'],'','Rows: '+', '.join(f['rows'])+'. Domain: '+f['domain']+'.','', 'Immediate conservative consumers: '+('; '.join(sorted(rev[f['function']]))or'(none)')+'.','', 'Potential driver cones: '+('; '.join(drivers)or'(no named driver in this conservative reverse closure)')+'.','']
lines+=['Actual source CM31 inverse is consumed by QM31::try_inv on its SAME canonical nonzero quartic norm; the new Q packet proves that domain, rather than assuming it. The inverse wrapper consumes the SAME derived Some child reply. Circle::secure_circle_point_from_parameter is the real try-inverse parent and must supply canonical parameter/domain and its original source/cohort carrier; this job closes no circle/Prepared/entry driver row. The newly closed embeddings supply unrestricted raw-word source laws plus the SAME canonical accumulation callback association.','', 'The default inv_with(M31::inv) edge is a fixed specialized callee packet; generic TX1:006 remains OPEN. QM31 negation has no adopted endpoint association and unblocks no certified driver edge yet.']
(E/'NHH_CONSUMERS.md').write_text('\n'.join(lines)+'\n')
print(json.dumps(dict(status='PASS',actual_scopes=len(receipts),charged_prelaunch=len(pre),rows_closed=12,remaining=2)))
