from pathlib import Path
import json,hashlib,re,lzma
E=Path(__file__).resolve().parent
read=lambda p:json.loads((E/p).read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
auth=read('AUTHORIZATION.json');rev=auth['revision'];seq=read('agg-92080/SEQUENCE.json');receipt=read('lean-92080/receipt.json')
assert seq['status']=='PASS' and seq['composition_counts'] is True and len(seq['steps'])==3
assert receipt['source_revision']==rev==seq['source_revision'] and receipt['exit_status']==0
assert receipt['limits']=={'memory.high':'15032385536','memory.max':'17179869184','memory.swap.max':'0','pids.max':'64'}
assert read('LAUNCH-RESULT.json')['attempts']==1
assert read('admission-status-0.json')['exit_status']==0 and read('admission-92080-0.json')['allowed'] is True
for n,h in receipt['source_hashes'].items():assert sha(E/'lean-92080/sources'/n)==h,n
for s in seq['steps']:assert s['source_revision']==rev and s['exit_status']==0 and s['swaps']=='0'
A=E/'agg-92080';scan=read('agg-92080/SCAN.json')
rows=list(map(json.loads,(A/'COMBINED-SCAN-ROWS.jsonl').read_text().splitlines()))
assert len(rows)==16539 and {r['module'] for r in rows}==set(read('agg-92080/EXPECTED-SCAN-MODULES.json'))
assert all(not r['dangling'] and r['imports_match'] for r in rows)
assert sha(A/'COMBINED-SCAN-ROWS.jsonl')==scan['rows_sha256']
raw=read('agg-92080/RAW-AXIOMS.json');log=(A/'step-3.log').read_text()
results=[json.loads(s) for s in re.findall(r'NEP_RESULT (\{[^\n]+\})',log)]
assert results==raw['roots'] and len(results)==32 and 'NEP_FAILURE' not in log
assert {r['root'] for r in results}==set(read('agg-92080/RAW-ROOTS.json'))
expected={r['root']:r for r in read('agg-92080/inputs/NER_AXIOMS.json')['roots']}
for r in results:
 assert r['equal'] and r['walked_axioms']==r['collect_axioms'] and set(r['walked_axioms'])<= {'Classical.choice','Quot.sound','propext'}
 if r['root'] in expected:
  for k in ['reachable_constants','edges_scanned','walked_axioms','collect_axioms','equal']:assert r[k]==expected[r['root']][k]
reach=read('reachable/MANIFEST.json');assert len(reach)==32 and {r['root'] for r in reach}=={r['root'] for r in results}
byroot={r['root']:r for r in results}
for r in reach:
 h=hashlib.sha256();n=0;size=0;found=False
 with lzma.open(E/'reachable'/r['file'],'rb') as f:
  for line in f:
   h.update(line);n+=1;size+=len(line);found |= line.rstrip(b'\n')==r['root'].encode()
 assert h.hexdigest()==r['uncompressed_sha256'] and n==r['lines']==byroot[r['root']]['reachable_constants'] and size==r['uncompressed_bytes'] and found
# All executable inputs match the committed pins from the authorized revision.
pins=read('COMMITTED-INPUT-PINS.json')
S=E/'lean-92080/sources/evhc10-92080'
for n,h in pins.items():assert sha(S/n)==h,n
assert sha(S/'codex-pv-evhc9-20261104/NEP_WALKER.lean')=='e93447db5a4c402d73e78259bb8c5f3ac09faf3e778250e889bcbcc94acf7344'
result=dict(status='PASS',source_revision=rev,steps=3,scope_attempts=1,admission_exit=0,admission_allowed=True,scan_modules=16539,dangling_references=0,imports_all_match=True,raw_roots=32,unresolved_constants=0,standard_axioms_only=True,soundness_matches_NER_AXIOMS=True,full_reachable_lists_verified=32,compiled_walker_sha256=read('PREFLIGHT.json')['compiled_walker_sha256'])
(E/'RECEIPT-VALIDATION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
