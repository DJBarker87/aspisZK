"""Validate the literal gate outputs, never infer closure from exit0 alone."""
from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent
std={'propext','Classical.choice','Quot.sound'}
def results(a):return [json.loads(l[11:]) for l in (E/a/'stdout.log').read_text().splitlines() if l.startswith('NEP_RESULT ')]
for a in ['PCB_L005','PCB_L007','PCB_L008','PCB_L009','PCB_L010','PCB_L011']:
 r=json.loads((E/a/'receipt.json').read_text());assert r['exit_status']==0,a
scan=[json.loads(l) for l in (E/'PCB_LOADED_scan.jsonl').read_text().splitlines()]
assert scan and all(not r['dangling'] and not r.get('duplicate_owners',[]) and r['imports_match'] for r in scan)
f=results('PCB_L009');assert len(f)==8
for i,r in enumerate(f):assert r['equal'] and (len(r['walked_axioms'])==1 if i<4 else not r['walked_axioms']),r
roots=results('PCB_L011');expected=json.loads((E/'PCB_AUDIT_ROOTS.json').read_text())['roots'];assert [r['root'] for r in roots]==expected
for r in roots:assert r['equal'] and set(r['walked_axioms'])<=std and r['walked_axioms']==r['collect_axioms'],r
assert 'VERIFICATION:- SUCCESSFUL' in (E/'PCB_K006/stdout.log').read_text()
assert 'VERIFICATION:- FAILED' in (E/'PCB_K007/stdout.log').read_text()
for a in ['PCB_K006','PCB_K007']:
 g=json.loads((E/(a+'-graph-check.json')).read_text());assert g['graph_matches_frozen']
 k=json.loads((E/(a+'-lock-check.json')).read_text());assert k['unchanged']
 features=(E/(a+'-selected-features.txt')).read_text().splitlines();assert 'FEATURES=pool-v1-kernel' in features[0]
 assert not any('FEATURES=r0' in l for l in features if l.startswith('aspis-core '))
assert all(('[propext, Classical.choice, Quot.sound]' in l) for l in json.loads((E/'PCB_L004/receipt.json').read_text())['print_axioms'])
audit=dict(status='PASS',combined='PCB_L005',scan='PCB_L010',scan_module_count=len(scan),dangling=0,duplicate_owners=0,fixtures='PCB_L009',fixture_count=8,raw='PCB_L011',roots=roots,native_positive='PCB_K006',matched_control='PCB_K007',print_axioms=[r['walked_axioms'] for r in roots],limits=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64),claims='local helper packet only, no parent/reachability/headline security closure')
(E/'PCB_AUDIT.json').write_text(json.dumps(audit,indent=1)+'\n')
print('PCB gate PASS: '+str(len(roots))+' roots, eight fixtures, zero dangling/duplicates')
