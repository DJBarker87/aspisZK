"""One final checked row/edge snapshot and auditable member-by-member stop report."""
from pathlib import Path
import json,subprocess,sys,collections
import NEX_validate as v
E=v.E;R=v.R;P=E.parent/'slice-s-compose7-20261103'
base=v.read(R/'evidence/native-ledger3-20261029/NDT_LEDGER.json');packet=v.read(E/'NEX_LEDGER_DELTA.json');reviewed=v.read(E/'NEX_REVIEWED_CERTIFICATES.json')
out=v.compose(base,packet,reviewed);summary=v.inherited.summary(out)
(E/'NEX_VALIDATION.json').write_text(json.dumps(summary,indent=1)+'\n')
sl=v.read(R/'docs/research/100bit-spend-path-20261013/design/VERTICAL-SLICES-20261029.json')['slices']['S'];by={}
for r in out['rows']:
 if r['function'] in sl['functions']:by.setdefault(r['function'],[]).append(r)
rows=[{k:r[k] for k in ['row','function','composed_status','bridge_status','selected_claims','named_hypotheses','caller_domain_obligations','open_transitive_dependencies']} for rs in by.values() for r in rs]
(E/'NEX_CHECKED_ROWS.json').write_text(json.dumps(rows,indent=1)+'\n')
edges=v.read(P/'NEU_EDGES.json');counts=collections.Counter()
for e in edges['edges']:
 caller,callee=e['edge'].split(' -> ',1)
 obs=[o for r in by[caller] for o in r['caller_domain_obligations'] if o.get('callee')==callee]
 e['caller_composed']=all(r['composed_status']=='CLOSED' for r in by[caller]);e['callee_composed']=all(r['composed_status']=='CLOSED' for r in by[callee])
 e['status']='CLOSED' if obs and all(o['status']=='CLOSED' and o['discharged_by'] for o in obs) else 'OPEN'
 if e['edge'] in packet.get('edges',{}):
  c=packet['edges'][e['edge']];e['certificate_id']=c['id'];e['certificate_theorems']=[t['name'] for t in c.get('domain_theorems',[])];e['certificate_location']='NEX_LEDGER_DELTA.json.xz#edges/'+e['edge']
 else:e['exact_obstacle']='Missing accepted native caller-to-selected-callee domain/carrier/Result/state/ordered-frame certificate; conservative alternatives retained.'
 counts[e['status']]+=1
edges.update(provenance='Immutable 129-edge inventory, every alternative retained; status from final additive checked ledger',counts=dict(counts));(E/'NEX_EDGES.json').write_text(json.dumps(edges,indent=1)+'\n')
old=v.read(P/'NEU_STOP_AUDIT.json');ob={x['function']:x['exact_remaining_obligation'] for x in old['members']}
p='crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::'
ob[p+'decode_pool_v1_pair_forest_terminal_statement_v1']='All common/payment children now CLOSED. Need split native terminal return-record projections plus the exact validator argument/result/call-order/Box-unbox frame join. K133 full26-field selector timed out at90s; never rerun unchanged. L012 terminal model continuation, L033 general length partition and L035 complete record extensionality are accepted supporting facts.'
ob['programs/r1-cost-probe/src/r1_pool_adapter.rs::decode_public_statement_box']='Need native forwarding/error-map/fresh-Box value and identity certificate and CLOSED terminal parent on the same live input. L032 proves exact coherent installed op47 model/carrier endpoint. NEX_prepare_public.py is unexecuted, no credit.'
ob['programs/r1-cost-probe/src/r1_pool_adapter.rs::emit_result']='Need actual binding-validator bridge and792-byte encoder parent/child/frame association at derived statement, then original guard and root join. K135..140 add only matched header/lane/digest assignment windows. L039 retains explicit BindingBridge/EncoderBridge. Ruling(ab) adds RuntimeReturnData and model event/order/bound laws; it does not discharge either native child. Native closed(ab) uses=0.'
remaining=[]
for f,rs in by.items():
 if all(r['composed_status']=='CLOSED' for r in rs):continue
 remaining.append(dict(function=f,rows=[r['row'] for r in rs],composed_status='OPEN',exact_remaining_obligation=ob[f],lean_only_obligation_remaining=False,why_more_Lean_alone_is_insufficient='Existing model, range, record/carrier and induction laws are reused; the missing witness identifies the actual frozen native body/call arguments/Result/ordered frame or an OPEN native child. No further independent pure Lean obligation is identified. More model equalities cannot provide this native association.',open_dependencies=sorted(set(g for r in rs for g in r['open_transitive_dependencies'])),open_call_domains=[o['id'] for r in rs for o in r['caller_domain_obligations'] if o['status']!='CLOSED']))
audit=dict(target='not yet established',closed_rows=summary['closed_row_count'],closed_roots=summary['root_closed_count'],kani_used=140,kani_limit=140,lean_used=40,lean_limit=60,whole_budget_fraction=180/200,members=remaining,root_results=[dict(function=f,status='CLOSED' if all(r['composed_status']=='CLOSED' for r in by[f]) else 'OPEN',exact_remaining_obligation=ob.get(f,'')) for f in sl['roots']],runtime_return_data_ab=dict(classification='ADDED approved runtime trust',closed_native_uses=0,supporting_modules=['NEX_ReturnData','NEX_EmitRuntime']))
(E/'NEX_STOP_AUDIT.json').write_text(json.dumps(audit,indent=1)+'\n')
# Existing full root statements are retained verbatim by the root report generator.
subprocess.run([sys.executable,str(E/'NEX_refresh_reports.py')],check=True)
# Its historical edge descriptions do not determine the checked status: restore this snapshot.
(E/'NEX_EDGES.json').write_text(json.dumps(edges,indent=1)+'\n')
q=E/'NEX_COMPOSED.md';text=q.read_text();a=text.index('## Newly admitted exact helper')
text=text[:a]+'''## Native composition added in this job

Ten additional inventory rows are CLOSED (72→82); 49/61 functions, still2/7 roots. The new functions are exact, raw afterstate decoder, raw snapshot decoder, boxed afterstate, boxed snapshot, lane transition, late public statement, and common boxed decoder. Exact certificates, selected domains, complete field projections, all child Results/errors, native argument/Box identity/cleanup checks and Lean substitution/domain/axiom receipts are in NEX_LEDGER_DELTA.json.xz. Every unchanged inherited gate remains active.

NEX_EDGES.json and NEX_CHECKED_ROWS.json are the final per-call authority. Each retained inner qualification is discharged at its actual callsite before closure; a new child's domain and physical names are added to the domain view, never removed. Mutation tests remove/wrongly replace these certificates and leave callers OPEN. No conservative alternative is pruned.

The five outstanding native root theorems are unestablished. Their member-by-member current obstacles supersede historical descriptions above and are recorded in NEX_STOP_AUDIT.json. Native bridge hypotheses for these OPEN roots remain explicit; root closure is not obtained by assuming the root bridge. The statement decoder's latest native parent check K133 timed out and is excluded; all its real children are now CLOSED.

## Current emission model with explicit native leaves

Ruling(ab) use: supporting MODEL only; zero CLOSED native uses. RuntimeReturnData is ADDED trust. Full theorem below retains BindingBridge and EncoderBridge. Native parent/frame association is still required.

```lean
'''+(E/'NEX_EmitRuntime.lean').read_text().split('theorem result_state_effects',1)[1].split('/-- Exact event',1)[0].strip()+'\n```\n\nAxioms: [propext, Classical.choice, Quot.sound], NEX_L039. The successful modeled path appends precisely one setReturnData event with the exact792-byte payload, and no later write; NEX_ReturnData.runtime_bound proves the runtime length bound. These laws do not prove platform readback.\n\n'+text[a:]
text=text.replace('```lean\n{A E','```lean\ntheorem result_state_effects {A E')
q.write_text(text)
print(json.dumps(dict(rows=summary['closed_row_count'],roots=summary['root_closed_count'],edges=counts,remaining_members=len(remaining))))

subprocess.run([sys.executable,str(E/'NEX_project_reports.py')],check=True)
