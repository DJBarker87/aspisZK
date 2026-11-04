"""Read-only recovery and classification of unchanged ax2/loaded-scan outputs."""
from pathlib import Path
import subprocess,json,hashlib,lzma,sys
E=Path(__file__).resolve().parent
audit_attempt,scan_attempt=sys.argv[1:3] if len(sys.argv)>1 else ('NFR_B044','NFR_B047')
code="""from pathlib import Path
import json,lzma,sys,hashlib
b=Path('/home/dombarker/project-offloads/codex-cx-pool-retdata2-20261104')
p=b/'NFR_LOADED.jsonl'
files={'NFR_LOADED.jsonl':p.read_text()}
pins={str(q):dict(sha256=hashlib.sha256(q.read_bytes()).hexdigest(),size=q.stat().st_size) for q in [b/'NFO_native/NFR_Coherence']}
sys.stdout.buffer.write(lzma.compress(json.dumps(dict(files=files,pins=pins),sort_keys=True).encode(),preset=6))
"""
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code.encode(),capture_output=True)
assert r.returncode==0,r.stderr
raw=lzma.decompress(r.stdout);data=json.loads(raw)
(E/'NFR_SCAN_ARTIFACTS.json.xz').write_bytes(r.stdout)
(E/'NFR_SCAN_ARTIFACTS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
loaded=[json.loads(line) for line in data['files']['NFR_LOADED.jsonl'].splitlines()]
inherited=[row for row in loaded if row['dangling'] and not row['module'].startswith('NFR_')]
own=[row for row in loaded if row['module'].startswith('NFR_')]
assert all(not row['dangling'] for row in own)
assert sum(len(row['dangling']) for row in inherited)==650
old=json.loads((E/'NFR_INHERITED_INCOHERENCE.json').read_text())
assert {row['module']:row['dangling'] for row in old['modules']}=={row['module']:row['dangling'] for row in inherited}
(E/'NFR_INHERITED_INCOHERENCE.json').write_text(json.dumps(dict(source='NFR_SCAN_ARTIFACTS.json.xz',prior_source=old['source'],classification='Inherited, not waived; exact same650 references as NFO; no imported module repaired',total_unresolved=650,modules=inherited,new_modules=own,new_module_unresolved=0),indent=1)+'\n')
audit_rows=[json.loads(line.split('NEP_RESULT ',1)[1]) for line in (E/audit_attempt/'stdout.log').read_text().splitlines() if line.startswith('NEP_RESULT ')]
fixtures=audit_rows[:8];roots=audit_rows[8:];assert len(roots)==len(json.loads((E/'NFR_AUDIT_INPUTS.json').read_text())['roots'])
standard={'propext','Classical.choice','Quot.sound'}
assert all(set(row['walked_axioms'])<=standard for row in roots)
assert all(row['equal'] for row in audit_rows)
inputs=json.loads((E/'NFR_AUDIT_INPUTS.json').read_text())
canonical=(E.parent/'axaudit2-20261102/NEP_WALKER.lean').read_bytes()
assert (E/'NFR_WALKER.lean').read_bytes()==canonical
scan_receipt=json.loads((E/scan_attempt/'receipt.json').read_text());audit_receipt=json.loads((E/audit_attempt/'receipt.json').read_text())
(E/'NFR_AUDIT.json').write_text(json.dumps(dict(disposition='PASS new roots; inherited closure incoherence OPEN',authoritative='Raw checked-kernel ax2 traversal',walker_identical=True,walker_sha256=hashlib.sha256(canonical).hexdigest(),driver_diff='NFR_DRIVER.diff',fixture_results=fixtures,roots=roots,new_roots=len(roots),new_root_unresolved=0,collect_disagreements=[],inherited_collect_disagreement='NFO five ReadModel gate roots have raw standard axioms omitted by collectAxioms, retained finding per ruling(ab\'); not a proof failure',compiled_proof_modules=inputs['sources'],audit_receipt=audit_receipt,scan_receipt=scan_receipt,loaded_modules=len(loaded),new_modules=[row['module'] for row in own],new_module_unresolved=0,inherited_unresolved=650,inherited_modules=15,formal_release=False,cold_replay=False),indent=1)+'\n')
print(len(roots),'raw roots standard; own modules',len(own),'zero unresolved; inherited',len(inherited),'/650 unchanged')
