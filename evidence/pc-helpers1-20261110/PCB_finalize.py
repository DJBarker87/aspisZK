from pathlib import Path
import json,collections,ast
E=Path(__file__).resolve().parent
old=json.load(open(E/'PCB_AUDIT.json'));assert old['status']=='PASS','already finalized; accepted audit must never be overwritten'
(E/'PCB_AUDIT_ACCEPTED_STAGE6.json').write_text(json.dumps(old,indent=1)+'\n')
raw=[json.loads(l[11:]) for l in (E/'PCB_L060/stdout.log').read_text().splitlines() if l.startswith('NEP_RESULT ')]
assert len(raw)==29 and sum(not r['equal'] for r in raw)==1
assert all(set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'} for r in raw)
latest=dict(status='FAIL_COLLECTOR_RAW_MISMATCH',combined='PCB_L058',scan='PCB_L059',raw='PCB_L060',raw_exit_status=1,roots=raw,all_raw_axioms_standard=True,mismatches=[r for r in raw if not r['equal']],adopted_new_pool_rows=0,reason='Aggregate gate exit1; no promotion of the four candidates. No walker change, axiom padding, scope-budget increase or unrecorded rerun.',next='Use a semantically complete actual carrier/value-and-frame law for preparation, review its statement and raw type closure; then compile and re-gate all candidates under a lead budget. Do not merely pad the axioms or weaken the walker.')
(E/'PCB_AUDIT_LATEST.json').write_text(json.dumps(latest,indent=1)+'\n')
old.update(status='PARTIAL_ACCEPTED_11_LATEST_GATE_FAILED',accepted_gate='PCB_AUDIT_ACCEPTED_STAGE6.json',latest_gate='PCB_AUDIT_LATEST.json',accepted_pool_rows=11,all_current_top_roots_raw_audited=False,current_candidate_combined='PCB_COMBINED_IMPORT.lean;29 roots; not adopted',claims='11 prior stage-gated Pool rows retained; no candidate promotion or parent/headline soundness claim')
(E/'PCB_AUDIT.json').write_text(json.dumps(old,indent=1)+'\n')
parsed=ast.parse((E/'PCB_close_final.py').read_text());statements=next(ast.literal_eval(n.value) for n in parsed.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='statements' for t in n.targets))
rootmap={'370':'PCB_RegistryLaws.selection','371':'PCB_RegistryLaws.owner','344':'PCB_FinalLaws.clear','290':'PCB_FinalLaws.preparation'}
inv=json.load(open(E.parent/'pool-inventory2-20261109/NKZ_INVENTORY.json'))['rows'];byid={r['id']:r for r in inv}
candidates=[];clauses=json.load(open(E/'PCB_CALLER_CLAUSES.json'))
for id,root in rootmap.items():
 rid='POOL:'+id;r=byid[rid];v=next(x for x in raw if x['root']==root)
 candidates.append(dict(id=rid,function=r['function'],status='OPEN_GATE_BLOCKED',root=root,statement=statements[id],named_hypotheses=[],caller_clause='all valid Rust arguments; no additional semantic predicate',modifies_native_memory=[],external_effects=['clear return-data slot via existing RuntimeReturnDataClear'] if id=='344' else [],individual_raw=v,body_hash=r['frozen_body_sha256'],native={'370':['PCB_K111','PCB_K112'],'371':['PCB_K113','PCB_K114'],'344':['PCB_K070','PCB_K071','PCB_K115','PCB_K116','PCB_K117','PCB_K118','PCB_K119'],'290':['PCB_K072','PCB_K074','PCB_K075','PCB_K076','PCB_K077','PCB_K078']}[id],gate='PCB_AUDIT_LATEST.json',correspondence='PCB_BOUNDARY_CORRESPONDENCE.json',trust='P6/D188 option-A semantic-transport reclassification; no trust removal'))
 for caller in inv:
  if r['function'] in caller['callees']:clauses.append(dict(callee=rid,caller=caller['id'],caller_function=caller['function'],status='OPEN_CANDIDATE_ONLY',verbatim_domain='all valid Rust arguments; no additional semantic predicate',named_hypotheses=[],occurrences=[e for e in caller['edges'] if r['function'] in e['targets']]))
r=byid['POOL:279']
for caller in inv:
 if r['function'] in caller['callees']:clauses.append(dict(callee='POOL:279',caller=caller['id'],caller_function=caller['function'],status='OPEN_PROPOSED_LOOP_DOMAIN',verbatim_domain='data.len() >= 8256 and usize::from(header.filled) + roots.len() <= 256; valid mutable byte slice and live immutable roots/header',named_hypotheses=['geometry cap on own header/count; offset<count inside loop; no encoder domain beyond shared all-raw-u32 domain'],occurrences=[e for e in caller['edges'] if r['function'] in e['targets']]))
(E/'PCB_CANDIDATES.json').write_text(json.dumps(candidates,indent=1)+'\n');(E/'PCB_CALLER_CLAUSES.json').write_text(json.dumps(clauses,indent=1)+'\n')
used=list(map(json.loads,(E/'PCB_ATTEMPTS.jsonl').read_text().splitlines()));count=collections.Counter('lean' if r['kind'] in ['lean','link','audit'] else r['kind'] for r in used);assert count==dict(kani=100,lean=60,extract=12)
(E/'PCB_BUDGET.json').write_text(json.dumps(dict(used=dict(count),limits=dict(kani=100,lean=60,extract=12),remaining=dict(kani=0,lean=0,extract=0),stop='All authorized scope budgets exhausted; no over-budget repair attempted',one_scope_at_a_time=True),indent=1)+'\n')
print('PCB finalized:11 accepted rows; four OPEN candidates;100/60/12 scopes used')
