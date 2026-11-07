"""Report blocked downstream work without manufacturing graph verdicts."""
import json,lzma,pathlib,collections
E=pathlib.Path(__file__).resolve().parent; R=E.parents[1]
load=lambda p:json.loads(p.read_text())
a=load(E/'PCH_AUTHORITY.json'); assert a['admitted'] is False
n=R/'evidence/pool-inventory2-20261109';t=load(n/'NKZ_TRACTABILITY.json')
rows=[r for r in t['rows'] if r['genuinely_new'] and r['scope']=='ON_CONSERVATIVE_CLOSURE'];assert len(rows)==278
base=json.loads(lzma.open(R/'evidence/pool-ledger1-20261110/PCE_LEDGER.json.xz').read()); delta=load(R/'evidence/pc-helpers2-20261110/PCG_LEDGER_DELTA.json')
status={r['id']:r['status'] for r in base['rows']};status.update({r['id']:r['status'] for r in delta['rows']})
assert sum(status[r['row']]=='CLOSED' for r in rows)==39
live={'PCD_':{311,312,313,314,319,320,339,347,348,350},'PCF_':{165,199,220,222,272,279,280,304,309,326,332,364,365}}
reported=[]
for r in rows:
 owners=[o for o,ids in live.items() if int(r['row'].split(':')[1]) in ids]
 reported.append({'row':r['row'],'function':r['function'],'class_':r['class_'],'inherited_status':status[r['row']],'live_owner':owners or None,'verdict':None,'assessment_status':'NOT_ASSESSED_AUTHORITY_BLOCKED','reason':'PCH-F1: no admitted rustc 1.94.1 / SBF / deployed-ELF build; graph stage prohibited by Stage 1 stop.','needs_Kani':False,'needs_Lean':False,'next_dependency':'Lead resolves compiler requirement against pinned 1.89.0-dev SBF receipt; then authorized compiler graph audit.'})
(E/'PCH_VERDICTS.json').write_text(json.dumps({'status':'NOT_RUN_STAGE1_BLOCKED','authority':'PCH_AUTHORITY.json','not_a_reachability_verdict':True,'rows':reported},indent=2)+'\n')
(E/'PCH_VERDICTS.md').write_text('# Reachability verdicts withheld\n\nAll 278 verdicts are NOT ASSESSED because Stage 1 authority is blocked.\nNo REACHABLE, EXCLUDED-CANDIDATE, CODEGEN-PRESENT-UNREACHED, or UNRESOLVED-path verdict is asserted.\nAn authority failure is not evidence of an unresolved call edge. Per-row details: PCH_VERDICTS.json.\n')
(E/'PCH_DIFF_PCB_REACH.md').write_text('# PCB comparison blocked\n\nPCB_REACH assesses 71 rows in a conservative graph; it is not compiler authority.\nPCH has no admitted graph and therefore no comparable verdicts or claimed differences.\nAll 71 PCB assessments are retained without adoption. No row was reclassified from that assessment.\n')
(E/'PCH_LEDGER_DELTA.json').write_text(json.dumps({'schema':'PCH-LEDGER-DELTA-1','status':'BLOCKED_NO_CHANGE','base':'evidence/pool-ledger1-20261110/PCE_LEDGER.json.xz','overlay':'evidence/pc-helpers2-20261110/PCG_LEDGER_DELTA.json','rows':[],'closed_changed':0,'excluded':0,'live_owned_rows_changed':0,'evidence':'PCH_AUTHORITY.json','security_target_established':False},indent=2)+'\n')
count='Pool rows CLOSED: 39 of 278 new (A 39 / B 0 / C 0 / D 0); EXCLUDED 0 (unreachable in the deployed build; not closed); OPEN 239; target not yet established'
opens=collections.Counter(r['class_'] for r in rows if status[r['row']]!='CLOSED')
(E/'PCH_COUNT.md').write_text(count+'\n\nEXCLUDED 0 means no exclusions admitted, not that all rows are reachable.\n\nRemaining OPEN by class: '+', '.join(f'{k} {opens[k]}' for k in 'ABCD')+'.\nREACHABLE among OPEN: unknown in every class; all 239 unassessed.\nCLOSED statuses are inherited from PCE plus PCG; no proof gate was replayed here.\n')
lines=['# Remaining obligations','', 'Stage 1 is blocked by PCH-F1. The explicit Stage 1 stop applies before stages 2–4.', '', 'Budget used: 0/6 build scopes, 1/20 host script/audit scopes, 0/0 Kani, 0/0 Lean proof scopes.', 'Stop below 80%: every remaining row needs the same missing authoritative compiler build.', 'More scopes on the retained 1.89 compiler cannot establish the required 1.94.1 conjunction.', 'No independent body proofs or shared-body work are authorized in this job.', 'No remaining obligation requires Kani; this is an authority stop, not Kani exhaustion.', '', '## Stage dependencies','', 'Stage 2: monomorphized graph, every required edge kind, shortest witnesses, SBF codegen cross-check and PCB differences await Stage 1.', 'Stage 3: validator and all five mutation tests await the admitted graph; NONE ran. PCH_VALIDATOR.py and PCH_GRAPH.json are intentionally not fabricated.', 'Stage 4: nonempty exclusion delta awaits stages 1–3; empty report-only delta preserves all statuses.', '', '## Every member','', '| Row | Class | Inherited | Live owner | Why no remaining attempt |','|---|---|---|---|---|']
for r in reported:lines.append(f"| {r['row']} | {r['class_']} | {r['inherited_status']} | {','.join(r['live_owner'] or []) or '—'} | PCH-F1: authority required before graph audit; no independent Kani/Lean body work authorized. |")
(E/'PCH_REMAINING.md').write_text('\n'.join(lines)+'\n')
(E/'PCH_VALIDATION.json').write_text(json.dumps({'status':'NOT_RUN_STAGE1_BLOCKED','validator_exit_status':None,'scope_exit_status':None,'mutation_tests':{k:'NOT_RUN' for k in ['planted_POOL_246','deleted_real_call','deleted_fn_pointer','deleted_vtable','missing_codegen_check']},'validation_claim':None,'reason':'No authoritative graph; no validator pass or mutation rejection is claimed.'},indent=2)+'\n')
print('PCH blocked-stage accounting: 278 assessed-for-scope; 0 reachability verdicts; 39 CLOSED inherited / 0 excluded / 239 OPEN')
