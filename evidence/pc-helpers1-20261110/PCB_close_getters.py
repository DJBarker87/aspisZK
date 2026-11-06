from pathlib import Path
import json
E=Path(__file__).resolve().parent;std={'propext','Classical.choice','Quot.sound'}
roots=[json.loads(l[11:]) for l in (E/'PCB_L045/stdout.log').read_text().splitlines() if l.startswith('NEP_RESULT ')];assert len(roots)==23
assert all(r['equal'] and set(r['walked_axioms'])<=std and r['walked_axioms']==r['collect_axioms'] for r in roots)
scan=[json.loads(l) for l in (E/'PCB_LOADED_scan.jsonl').read_text().splitlines()];assert all(not r['dangling'] and not r.get('duplicate_owners',[]) and r['imports_match'] for r in scan)
for a in ['PCB_L043','PCB_L044','PCB_L045']:assert json.loads((E/a/'receipt.json').read_text())['exit_status']==0
items=[('178','tree','PCB_K067','PCB_K058','receiver.inner'),('291','seed','PCB_K061','PCB_K062','receiver.seed'),('343','value','PCB_K063','PCB_K064','receiver.value.deref'),('355','state','PCB_K065','PCB_K066','receiver.state.deref')]
for id,root,pos,neg,place in items:
 assert 'VERIFICATION:- SUCCESSFUL' in (E/pos/'stdout.log').read_text()
 raw=(E/neg/'stdout.log').read_text();assert 'VERIFICATION:- FAILED' in raw and 'Failed Checks: assertion failed: core::ptr::eq' in raw
 for a in [pos,neg]:
  assert json.loads((E/(a+'-graph-check.json')).read_text())['graph_matches_frozen'];assert json.loads((E/(a+'-lock-check.json')).read_text())['unchanged']
ids=json.loads((E/'PCB_GETTER_IDENTITIES.json').read_text());assert sum(r['mutations_rejected'] for r in ids['rows'])==20
x=json.load(open(E.parent/'pool-inventory2-20261109/NKZ_INVENTORY.json'));rows={r['id']:r for r in x['rows']};cl=json.loads((E/'PCB_CLOSED.json').read_text());delta=json.loads((E/'PCB_LEDGER_DELTA.json').read_text());clauses=json.loads((E/'PCB_CALLER_CLAUSES.json').read_text())
statements={
 '178':'∀ x : PCB_GetterRef.Validated, PCB_GetterRef.tree_ref x = Aeneas.Result.ok x.inner',
 '291':'∀ {P : Type} (x : PCB_GetterRef.Plan P), PCB_GetterRef.seed_ref x = Aeneas.Result.ok x.seed',
 '343':'∀ x : PCB_GetterRef.Auth AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalResultV1, PCB_GetterRef.value_ref x = Aeneas.Result.ok x.value',
 '355':'∀ {P S : Type} (x : PCB_GetterRef.Canonical P S), PCB_GetterRef.state_ref x = Aeneas.Result.ok x.state'}
for id,root,pos,neg,place in items:
 rid='POOL:'+id;r=rows[rid];domain='any valid live immutable Rust receiver; no additional semantic predicate'
 assert not any(a['id']==rid for a in cl)
 cl.append(dict(id=rid,function=r['function'],status='CLOSED',classification='NEW_UNDER_Y_PRIME',root='PCB_GetterLaws.'+root,statement=statements[id],named_hypotheses=[],caller_clause=domain,borrowed_place=place,borrow_kind='shared; lifetime of actual receiver; no new alias/allocation',modifies=[],native_correct_place=pos,native_wrong_place=neg,extraction='PCB_E009',source_identity='PCB_GETTER_IDENTITIES.json',frozen_body_sha256=r['frozen_body_sha256'],gate='PCB_AUDIT.json',trust='ruling y-prime source identity/extracted value law/actual-place caller controls; P6/D188 option-A RECLASSIFICATION; std Box/borrow/compiler/ABI/source-to-ELF retained'))
 delta.append(dict(id=rid,old='OPEN',new='CLOSED',classification='NEW_UNDER_Y_PRIME',root='PCB_GetterLaws.'+root))
 for caller in x['rows']:
  if r['function'] in caller['callees']:clauses.append(dict(callee=rid,caller=caller['id'],caller_function=caller['function'],verbatim_domain=domain,named_hypotheses=[],borrowed_place=place,occurrences=[e for e in caller['edges'] if r['function'] in e['targets']]))
for n,value in [('PCB_CLOSED.json',cl),('PCB_LEDGER_DELTA.json',delta),('PCB_CALLER_CLAUSES.json',clauses)]:(E/n).write_text(json.dumps(value,indent=1)+'\n')
a=json.loads((E/'PCB_AUDIT.json').read_text());a.update(combined='PCB_L043',scan='PCB_L044',raw='PCB_L045',roots=roots,scan_module_count=len(scan),borrowed_getters=[dict(row='POOL:'+i,positive=p,negative=n) for i,_,p,n,_ in items],raw_mismatch='PCB_RAW_MISMATCH.json; fixed by actual native carrier specialization, not axiom padding',all_current_top_roots_raw_audited=True);(E/'PCB_AUDIT.json').write_text(json.dumps(a,indent=1)+'\n')
with (E/'PCB_HANDOFF.md').open('a') as f:f.write('\nStage6: four y-prime getters178/291/343/355 NEW CLOSED. Source identities reject20 wrong-place/effect mutations; E009 models/L035–037/L042, matched pointer controls067/058,061/062,063/064,065/066; actual canonical result carrier specialization fixes L040 generic summary mismatch without axiom padding or walker changes. CombinedL043, scanL044 zero dangling/duplicates, rawL045 all23 roots equal/standard. Total10 CLOSED Pool rows:7 new,3 re-gated.176 native caller tests remain pending until178 adoption; no borrowed stub_verified is used.\n')
print('PCB getters gate PASS: four new rows; total10 CLOSED Pool rows')
