from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent
std={'propext','Classical.choice','Quot.sound'}
for a in ['PCB_L058','PCB_L059','PCB_L060']:assert json.load(open(E/a/'receipt.json'))['exit_status']==0,a
roots=[json.loads(l[11:]) for l in (E/'PCB_L060/stdout.log').read_text().splitlines() if l.startswith('NEP_RESULT ')]
assert [r['root'] for r in roots]==json.load(open(E/'PCB_AUDIT_ROOTS.json'))['roots']
assert len(roots)==29 and all(r['equal'] and set(r['walked_axioms'])<=std and r['walked_axioms']==r['collect_axioms'] for r in roots)
scan=list(map(json.loads,(E/'PCB_LOADED_scan.jsonl').read_text().splitlines()))
assert scan and all(not r['dangling'] and not r.get('duplicate_owners',[]) and r['imports_match'] for r in scan)
fixtures=[json.loads(l[11:]) for l in (E/'PCB_L009/stdout.log').read_text().splitlines() if l.startswith('NEP_RESULT ')]
assert len(fixtures)==8 and all(r['equal'] and len(r['walked_axioms'])==(1 if i<4 else 0) for i,r in enumerate(fixtures))
def native(a,positive,needle=None):
 s=(E/a/'stdout.log').read_text();assert 'VERIFICATION:- '+('SUCCESSFUL' if positive else 'FAILED') in s,a
 if needle:assert needle in s,a
 assert 'Timed out' not in s and '\nerror' not in s,a
 assert json.load(open(E/(a+'-graph-check.json')))['graph_matches_frozen'],a
 assert json.load(open(E/(a+'-lock-check.json')))['unchanged'],a
 features=(E/(a+'-selected-features.txt')).read_text();assert features.startswith('aspis-pool ') and all(f in features.splitlines()[0] for f in ['pair-forest-account-evidence','pair-forest-source-invariant-audit','pair-forest-source-result-invariant-audit','pair-forest-verifier-lane-invariant-audit','r1-split-checkpoint'])
for a in ['PCB_K111','PCB_K113','PCB_K070','PCB_K072','PCB_K115','PCB_K117']:native(a,True)
for a,n in [('PCB_K112','Failed Checks: |r|'),('PCB_K114','Failed Checks: |r|'),('PCB_K071','assertion failed: !bytes.is_empty()'),('PCB_K078','Failed Checks: |r|'),('PCB_K076','Failed Checks:'),('PCB_K077','is assignable'),('PCB_K116','x[0]!=0'),('PCB_K118','Failed Checks:'),('PCB_K119','is assignable')]:native(a,False,n)
for a in ['PCB_K074','PCB_K075']:
 assert 'VERIFICATION:- SUCCESSFUL' in (E/a/'stdout.log').read_text()
inv=json.load(open(E.parent/'pool-inventory2-20261109/NKZ_INVENTORY.json'))['rows'];byid={r['id']:r for r in inv}
closed=json.load(open(E/'PCB_CLOSED.json'));delta=json.load(open(E/'PCB_LEDGER_DELTA.json'));clauses=json.load(open(E/'PCB_CALLER_CLAUSES.json'))
statements={
'370':'∀ (s : PCB_RegistryRef.AuthenticatedVerifierSelectionV1) (p v q r : Aeneas.Std.Array Aeneas.Std.U8 32#usize) (version : Aeneas.Std.U8), PCB_RegistryRef.matches_ref s p v q r version = Aeneas.Result.ok (decide (s.pool.val = p.val ∧ s.verifier_program.val = v.val ∧ s.profile_binding.val = q.val ∧ s.release_binding.val = r.val ∧ s.statement_version = version))',
'371':'∀ (s : PCB_RegistryRef.AuthenticatedVerifierSelectionV1) (p : PCB_RegistryRef.Pubkey), PCB_RegistryRef.owner_ref s p = Aeneas.Result.ok (match s.expected_verifier_loader with | none => true | some expected => decide (p.val = expected.val))',
'344':'∀ {S R : Type} (setReturnData : List Aeneas.Std.U8 → S → R) (state : S), PCB_FinalLaws.clearStep setReturnData state = setReturnData [] state ∧ PCB_FinalRef.clear_ref = Aeneas.Result.ok ()',
'290':'∀ {P : Type} (x : PCB_FinalRef.Plan P), PCB_FinalRef.preparation_ref x = Aeneas.Result.ok x.preparation'}
for id,root,pos,neg,ext in [('370','PCB_RegistryLaws.selection','PCB_K111','PCB_K112','PCB_E011'),('371','PCB_RegistryLaws.owner','PCB_K113','PCB_K114','PCB_E011'),('344','PCB_FinalLaws.clear','PCB_K070','PCB_K071','PCB_E012'),('290','PCB_FinalLaws.preparation','PCB_K072','PCB_K078','PCB_E012')]:
 rid='POOL:'+id;r=byid[rid];assert not any(x['id']==rid for x in closed)
 domain='all valid Rust arguments; no additional semantic predicate'
 extra={}
 if id=='344':extra=dict(runtime_trust='existing RuntimeReturnDataClear; exact empty slice request; unique unit reply; no value realization added',boundary_correspondence='PCB_BOUNDARY_CORRESPONDENCE.json',unit_controls=['PCB_K115','PCB_K116','PCB_K117','PCB_K118','PCB_K119'])
 if id=='290':extra=dict(enum_controls=['PCB_K074','PCB_K075','PCB_K076','PCB_K077','PCB_K078'],carrier_correspondence='PCB_BOUNDARY_CORRESPONDENCE.json')
 if id in ['370','371']:extra=dict(carrier_correspondence='PCB_BOUNDARY_CORRESPONDENCE.json')
 closed.append(dict(id=rid,function=r['function'],status='CLOSED',classification='NEW',root=root,statement=statements[id],named_hypotheses=[],caller_clause=domain,modifies=[],frozen_body_sha256=r['frozen_body_sha256'],native=pos,negative=neg,extraction=ext,gate='PCB_AUDIT.json',trust='P6/D188 option-A native semantic transport RECLASSIFICATION; compiler/ABI/source-to-ELF trust retained',**extra))
 delta.append(dict(id=rid,old='OPEN',new='CLOSED',classification='NEW',root=root))
 for caller in inv:
  if r['function'] in caller['callees']:clauses.append(dict(callee=rid,caller=caller['id'],caller_function=caller['function'],verbatim_domain=domain,named_hypotheses=[],occurrences=[e for e in caller['edges'] if r['function'] in e['targets']]))
for n,v in [('PCB_CLOSED.json',closed),('PCB_CALLER_CLAUSES.json',clauses),('PCB_LEDGER_DELTA.json',delta)]: (E/n).write_text(json.dumps(v,indent=1)+'\n')
a=json.load(open(E/'PCB_AUDIT.json'));a.update(status='PASS',combined='PCB_L058',scan='PCB_L059',raw='PCB_L060',roots=roots,scan_module_count=len(scan),dangling=0,duplicate_owners=0,all_current_top_roots_raw_audited=True,closed_pool_rows=len(closed),new_pool_rows=sum(r['classification']!='RE-GATED' for r in closed),binary_sha256=json.load(open(E/'PCB_AUDIT_BINARY_PINS.json')),scope='all29 roots; headline + own/helper utility roots; NLG closure imported coherently; eight prior fixtures same binary')
(E/'PCB_AUDIT.json').write_text(json.dumps(a,indent=1)+'\n')
print('PCB final gate PASS:29 roots,15 Pool rows CLOSED, zero dangling/duplicates')
