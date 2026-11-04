"""Additive delta checks only; preserves historical NDT/NGB/NGJ evidence.
No prover launch and no mutation of any inherited ledger or predicate."""
from pathlib import Path
import json,hashlib,lzma,copy,re,sys
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parents[1]
J=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
standard={'propext','Classical.choice','Quot.sound'}
base=R/'evidence/inv-repair-20261104/NGB_ADMITTED_LEDGER.json.xz';b=json.loads(lzma.decompress(base.read_bytes()));rows={r['row']:r for r in b['rows']};assert len(rows)==599
summary=J(E/'NGO_final_audit/SUMMARY.json');assert summary['status']=='PASS'
audit={r['root']:r for c in summary['commands']if c['target'].startswith('proof')for r in c['results']}
assert set(audit)==set(J(E/'NGO_AUDIT_ROOTS.json')['roots']) and len(audit)==57
for r in audit.values():assert r['equal'] and set(r['walked_axioms'])==set(r['collect_axioms'])<=standard
fixtures=next(c for c in summary['commands']if c['target']=='fixtures')['results'];assert len(fixtures)==8
assert all(len(r['walked_axioms'])==1 for r in fixtures[:4])and all(not r['walked_axioms']for r in fixtures[4:])
scan=[json.loads(l)for l in (E/'NGO_final_audit/LOADED_scan.jsonl').read_text().splitlines()]
assert len(scan)>12000 and all(not x['dangling']and not x['duplicate_owners']and x['imports_match']for x in scan)
assert J(E/'NGO_WALKER_IDENTITY.json')['equal']
assert 'import NGJ_VERIFIER_IMPORT' in (E/'NGO_COMBINED_IMPORT.lean').read_text()
assert 'import NGO_CanonicalPort' in (E/'NGO_COMBINED_IMPORT.lean').read_text()
assert not any(x.startswith('import NGO_'+n)for x in (E/'NGO_COMBINED_IMPORT.lean').read_text().splitlines()for n in ['DecodePort','ZeroLaw','DecodeComposed'])
for a in ['NGO_L089','NGO_L090','NGO_A001']:
 r=J(E/a/'receipt.json');ad=J(E/(a+'-admission.json'))
 assert r['exit_status']==0 and ad['exit']==0 and ad['reservation']['allowed']is True
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}and int(r['swaps'])==0
pairs=[(5,6),(8,9),(10,11),(12,13),(14,15),(16,17)]
for positive,negative in pairs:
 for i,expected in [(positive,'SUCCESSFUL'),(negative,'FAILED')]:
  a=f'NGO_K{i:03d}';cfg=J(E/(a+'.json'));r=J(E/a/'receipt.json');text=(E/a/'stdout.log').read_text();ad=J(E/(a+'-admission.json'))
  assert f'VERIFICATION:- {expected}' in text
  assert r['exit_status']==(0 if expected=='SUCCESSFUL'else 1)
  assert ad['exit']==0 and ad['reservation']['allowed']is True
  assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
  assert cfg['env']['CARGO_NET_OFFLINE']=='true' and '-Copt-level=3' in cfg['env']['RUSTFLAGS']
  assert cfg['native_command'][cfg['native_command'].index('--features')+1]=='private-leaf-salts,optimized-terminal,program-build'
  assert '--locked'not in cfg['native_command']
  graph=J(E/(a+'-graph-check.json'));lock=J(E/(a+'-lock-check.json'))
  assert graph['graph_matches_frozen'] and not graph['new_package_tuples']and not graph['edge_errors']
  assert lock['unchanged']and lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
  assert graph['graph_sha256']==sha(E/'NGO_K018-graph-full.json')
  features={x['name']:x['features']for x in graph['selected_closure']}
  assert {'private-leaf-salts','optimized-terminal','program-build'}<=set(features['aspis-r1-cost-probe'])
assert 'VERIFICATION:- FAILED' in (E/'NGO_K007/stdout.log').read_text()
assert J(E/'NGO_K018-graph-reconstruction.json')['all_resolved_crates']==441
assert sha(R/'evidence/kani-mitig-20261028/KMX_copy_stubs.patch')=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
for x in J(E/'NGO_REUSED.json'):assert sha(R/x['path'])==x['sha256'] and not x['replayed']
# Original NDT CLOSED obligations are retained: selected bridge, no open inner
# hypothesis, all canonical callees certified, no open transitive callee. Root
# input/realization trust is reported separately, as in admitted hybrid packets.
def validate(c,d,es):
 assert c['new_composed_functions']==1 and c['new_composed_rows']==1 and len(c['functions'])==1
 p=c['functions'][0];assert p['rows']==['TX1:147'] and p['status']=='CLOSED'
 assert p['function']==rows['TX1:147']['function']and p['frozen_body_sha256']==rows['TX1:147']['frozen_body_sha256']
 assert p['lean_root']=='NGO_DecodeComposed.result'and p['lean_root']in audit and p['canonical_module']=='NGO_CanonicalPort'
 assert not p['inner_hypotheses_remaining']and p['retained_root_interpretation']
 assert set(x['callee']for x in p['internal_edges'])==set(rows['TX1:147']['canonical_callees'])
 assert all(x['status']=='CLOSED'and x['proof']and x['selected_claim'].startswith('NET::')for x in p['internal_edges'])
 assert p['native_positive']==['NGO_K005','NGO_K008','NGO_K010','NGO_K012','NGO_K014','NGO_K016']
 assert p['matched_controls']==['NGO_K006','NGO_K009','NGO_K011','NGO_K013','NGO_K015','NGO_K017']
 assert p['q_stub_theorem']=='NGO_QBridge.stub_law'and p['q_stub_theorem']in audit
 assert set(p['domain_roots']+p['trace_roots'])<=set(audit)
 assert len(es)==len(J(R/'evidence/slice-d-parser-20261104/NGD_EDGES.json'))
 assert sum(x['status']=='CLOSED'for x in es)==1
 assert all(x['row']=='TX1:147'for x in es if x['status']=='CLOSED')
 assert d['baseline_sha256']==sha(base)and d['new_closed_rows']==['TX1:147']and d['no_other_status_change']
 assert len(d['rows'])==1 and d['rows'][0]['before']=='OPEN'and d['rows'][0]['after']=='CLOSED'
 assert c['driver_root_status']=='OPEN'and len(c['other_members'])==3 and all(x['status']=='OPEN'for x in c['other_members'])
# All archived validation/harness/reference inputs remain committed and hash-exact.
pack=E/'NGO_PACK.json'
if pack.exists():
 for entry in J(pack)['entries']:
  data=lzma.decompress((E/entry['blob']).read_bytes())
  assert len(data)==entry['bytes'] and hashlib.sha256(data).hexdigest()==entry['sha256']
  assert J(E/(entry['original']+'.REFERENCE.json'))==entry
c=J(E/'NGO_CLOSED.json');d=J(E/'NGO_LEDGER_DELTA.json');edges=J(E/'NGO_EDGES.json');validate(c,d,edges)
controls=[]
mutations=[('open inner callee',lambda c,d,e:c['functions'][0].update(inner_hypotheses_remaining=['missing'])),('missing control',lambda c,d,e:c['functions'][0].update(matched_controls=[])),('different row',lambda c,d,e:c['functions'][0].update(rows=['TX1:151'])),('unsupported root',lambda c,d,e:c['functions'][0].update(lean_root='True.intro')),('stale owner',lambda c,d,e:c['functions'][0].update(canonical_module='NGO_DecodeComposed')),('suspended callee',lambda c,d,e:c['functions'][0]['internal_edges'][0].update(selected_claim='NBG::stale')),('open call edge',lambda c,d,e:c['functions'][0]['internal_edges'][0].update(status='OPEN')),('extra closure',lambda c,d,e:d['new_closed_rows'].append('TX1:151')),('missing Q association',lambda c,d,e:c['functions'][0].update(q_stub_theorem='True.intro')),('body mismatch',lambda c,d,e:c['functions'][0].update(frozen_body_sha256='0'*64))]
for name,mutate in mutations:
 cc,dd,ee=copy.deepcopy((c,d,edges));mutate(cc,dd,ee)
 try:validate(cc,dd,ee)
 except AssertionError:controls.append(name)
 else:raise AssertionError('Accepted mutation '+name)
(E/'NGO_VALIDATION.json').write_text(json.dumps(dict(status='PASS',checks_added_only=True,original_predicates_unchanged=['NDT_validate.py','NGB producer/599-row inventory','NGJ verifier/cohort audit','NGD previous slot certificate'],baseline_sha256=sha(base),new_closed_rows=['TX1:147'],raw_roots=len(audit),scan_modules=len(scan),mutations_rejected=controls),indent=2))
print(json.dumps(dict(status='PASS',new_closed_rows=['TX1:147'],mutations_rejected=len(controls),raw_roots=len(audit),scan_modules=len(scan))))
