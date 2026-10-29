"""Final evidence-only consistency check; no compiler, solver or host launch."""
from pathlib import Path
import json,re,hashlib,subprocess
E=Path(__file__).resolve().parent;R=E.parent.parent
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
budget=read(E/'NED_BUDGET_FINAL.json');assert budget['consumed']=={'kani':40,'lean':150}
assert len(list(E.glob('NED_L*/receipt.json')))==150 and len(list(E.glob('NED_K*/receipt.json')))==40
active=read(E/'NED_ACTIVE_PROOFS.json');assert len(active['active'])==59
for a in active['active']:
 p=E/a['source'];assert sha(p)==a['source_sha256'];assert sha(E/a['receipt'])==a['receipt_sha256']
 s=p.read_text();decls=re.findall(r'^(?:private )?(?:theorem|lemma)\s+(\w+)',s,re.M);prints=re.findall(r'^#print axioms (\S+)',s,re.M)
 assert all(any(x==n or x.endswith('.'+n) for x in prints) for n in decls)
 assert read(E/a['receipt'])['exit_status']==0
r=read(E/'NED_L153/receipt.json');assert r['exit_status']==0 and len(r['print_axioms'])==214
assert sha(E/'NED_FinalAudit.lean')==r['source_hashes']['NED_generated/NED_FinalAudit.lean']
for line in r['print_axioms']:
 m=re.search(r'\[([^]]*)\]',line)
 assert ('does not depend on any axioms' in line) or (m and set(y.strip() for y in m[1].split(','))<={'propext','Classical.choice','Quot.sound'})
for p in [*E.glob('NED_L*/receipt.json'),*E.glob('NED_K*/receipt.json')]:
 q=read(p);assert q['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'} and int(q['swaps'])==0
 assert all(k in q for k in ['command','exit_status','wall_seconds','peak_rss_kib','source_revision','print_axioms'])
delta=read(E/'NED_LEDGER_DELTA.json');assert delta['composed_rows_closed']==[] and all(not delta[k] for k in ['edges','roots','members','hypotheses','externals'])
assert len(read(E/'NED_EDGES.json')['edges'])==129 and len(read(E/'NED_REMAINING.json')['members'])==61
assert all(e['status']=='OPEN' and e['certificate'] is None and e['obstacle'] for e in read(E/'NED_EDGES.json')['edges'])
assert read(E/'NED_SCHEMA_STAGE8.json')['exit_status']==0 and read(E/'NED_LEDGER_STAGE8.json')['exit_status']==0
assert read(E/'NED_ERASURE_FINAL.json')['exit_status']==0 and read(E/'NED_BINDINGS_STAGE7_FINAL.json')['exit_status']==0
assert read(E/'NED_SCHEMA_STAGE8.json')['source_sha256']==sha(E/'NED_tests.py')
assert read(E/'NED_LEDGER_STAGE8.json')['source_sha256']==sha(E/'NED_validate.py')
cache=read(E/'NED_CACHE_FINAL.json');assert all(x['absent'] for x in cache['cleanup']) and len(cache['objects'])==194
assert read(E/'NED_ARCHIVE/receipt.json')['exit_status']==0
assert not (E/'NED_ACTIVE.json').exists()
assert not list(E.rglob('*.olean'))
assert not [p for p in E.rglob('*') if p.is_file() and p.stat().st_size>20*1024*1024]
changed=subprocess.check_output(['git','diff','--name-only','220d1cd55b4b5e0094b5493241b69353fe997392'],cwd=R,text=True).splitlines()
assert changed and all(p.startswith('evidence/slice-s-compose-20261029/') for p in changed),changed
print(json.dumps(dict(proof_scopes=budget['consumed'],active_modules=59,audited_top_theorems=214,composed_roots_closed=0,composed_rows_closed=0,all_changes_in_own_evidence=True,compiled_scratch_cleaned=True,cache_retained=True,shipped_source_changed=False,elf_rebuild='not triggered; no new build attestation')))
