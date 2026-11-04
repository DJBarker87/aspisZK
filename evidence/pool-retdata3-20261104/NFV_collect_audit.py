"""Read-only recovery and classification of unchanged ax2/loaded-scan outputs."""
from pathlib import Path
import subprocess,json,hashlib,lzma,sys
E=Path(__file__).resolve().parent
audit_attempt,scan_attempt,fixture_attempt=sys.argv[1:4]
plan=json.loads((E/'NFV_AUDIT_PLAN.json').read_text())
code="""from pathlib import Path
import json,lzma,sys,hashlib
b=Path('/home/dombarker/project-offloads/codex-cx-pool-retdata3-20261104')
p=b/'NFV_LOADED.jsonl'
files={'NFV_LOADED.jsonl':p.read_text()}
pins={str(q):dict(sha256=hashlib.sha256(q.read_bytes()).hexdigest(),size=q.stat().st_size) for q in [b/'NFO_native/NFV_Coherence']}
sys.stdout.buffer.write(lzma.compress(json.dumps(dict(files=files,pins=pins),sort_keys=True).encode(),preset=6))
"""
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code.encode(),capture_output=True)
assert r.returncode==0,r.stderr
raw=lzma.decompress(r.stdout);data=json.loads(raw)
(E/'NFV_SCAN_ARTIFACTS.json.xz').write_bytes(r.stdout)
(E/'NFV_SCAN_ARTIFACTS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
loaded=[json.loads(line) for line in data['files']['NFV_LOADED.jsonl'].splitlines()]
inherited=[row for row in loaded if row['dangling'] and not row['module'].startswith('NFV_')]
own=[row for row in loaded if row['module'].startswith('NFV_')]
assert all(not row['dangling'] for row in own)
assert sum(len(row['dangling']) for row in inherited)==650
old=json.loads((E.parent/'pool-retdata2-20261104/NFR_INHERITED_INCOHERENCE.json').read_text())
assert {row['module']:row['dangling'] for row in old['modules']}=={row['module']:row['dangling'] for row in inherited}
(E/'NFV_INHERITED_INCOHERENCE.json').write_text(json.dumps(dict(source='NFV_SCAN_ARTIFACTS.json.xz',prior_source=old['source'],classification='Inherited, not waived; exact same650 references as NFO; no imported module repaired',total_unresolved=650,modules=inherited,new_modules=own,new_module_unresolved=0),indent=1)+'\n')
fixtures=[json.loads(line.split('NEP_RESULT ',1)[1]) for line in (E/fixture_attempt/'stdout.log').read_text().splitlines() if line.startswith('NEP_RESULT ')]
roots=[json.loads(line.split('NEP_RESULT ',1)[1]) for line in (E/audit_attempt/'stdout.log').read_text().splitlines() if line.startswith('NEP_RESULT ')]
standard={'propext','Classical.choice','Quot.sound'}
assert len(fixtures)==8 and len(roots)==plan['total_roots']
assert all(row['walked_axioms'] and any(n.startswith('NEP_Planted.') for n in row['walked_axioms']) for row in fixtures[:4])
assert all(row['walked_axioms']==[] for row in fixtures[4:])
assert all(row['equal'] for row in fixtures+roots)
assert all(set(row['walked_axioms'])<=standard for row in roots)
walker=E.parent/'pool-retdata2-20261104/NFR_WALKER.lean'
assert hashlib.sha256(walker.read_bytes()).hexdigest()=='e93447db5a4c402d73e78259bb8c5f3ac09faf3e778250e889bcbcc94acf7344'
scan_receipt=json.loads((E/scan_attempt/'receipt.json').read_text());audit_receipt=json.loads((E/audit_attempt/'receipt.json').read_text())
assert scan_receipt['exit_status']==1 and audit_receipt['exit_status']==0
(E/'NFV_AUDIT.json').write_text(json.dumps(dict(disposition='PASS own proof roots; inherited incoherence OPEN; native composition OPEN on B',authoritative='raw checked-kernel ax2 traversal',walker_identical=True,walker_sha256=hashlib.sha256(walker.read_bytes()).hexdigest(),driver_diff='NFV_DRIVER.diff',fixture_results=fixtures,roots=roots,root_count=len(roots),new_root_unresolved=0,collect_disagreements=[],compiled_proof_modules=plan['modules'],audit_receipt=audit_receipt,scan_receipt=scan_receipt,loaded_modules=len(loaded),own_modules=[row['module'] for row in own],own_module_unresolved=0,inherited_unresolved=650,inherited_modules=15,inherited_waived=False,formal_release=False,cold_replay=False),indent=1)+'\n')
print(len(roots),'raw roots standard; own modules',len(own),'zero unresolved; inherited',len(inherited),'/650 unchanged')
