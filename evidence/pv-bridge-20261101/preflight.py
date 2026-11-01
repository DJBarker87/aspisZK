"""Compile-free generated-source validation. Does not certify Lean elaboration."""
from pathlib import Path
import json,hashlib,re,subprocess
B=Path(__file__).resolve().parent
files=[B/'rekey.py',B/'prepare_bridge.py',B/'prepare_admission.py',B/'prepare_migration.py']
outputs=list(B.glob('*.lean'))+list((B/'draft-migration').glob('*.lean'))+[B/n for n in ['REKEYED.json','RUST-ORIGINS.json','SOURCE-TRANSFORM.json','MIGRATION-MANIFEST.json']]
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
before={str(p.relative_to(B)):h(p) for p in outputs}
for p in files:subprocess.run(['python3',str(p)],check=True)
after={str(p.relative_to(B)):h(p) for p in outputs}
assert before==after,'generator output changed'
assert all(p.stem.startswith('PV_BR_') for p in outputs if p.suffix=='.lean')
s=json.loads((B/'SELECTED-SOURCES.json').read_text())
assert len(s)==95 and all(hashlib.sha256(v['text'].encode()).hexdigest()==v['sha256'] for v in s.values())
m=json.loads((B/'MIGRATION-MANIFEST.json').read_text())
assert len(m['modules'])==67
assert set(v for row in m['modules'] for v in row['members'])==set(s)
assert m['budget_plan']['total_if_first_attempt_passes']<=80
large=[str(p) for p in B.rglob('*') if p.is_file() and p.stat().st_size>20*1024*1024];assert not large,large
for p in outputs:
 if p.suffix=='.lean':assert not re.search(r'^\s*(?:axiom|admit|sorry)\b',p.read_text(),re.M),p
(B/'PREFLIGHT.json').write_text(json.dumps({'status':'PASS: compile-free generator and source-integrity checks only','selected_sources':95,'new_migration_modules':67,'prefix_check':True,'deterministic_regeneration':True,'normal_cap_attempt_plan':m['budget_plan'],'output_hashes':after,'lean_attempts':0,'print_axioms':'NOT RUN; no compiled claim'},indent=2)+'\n')
print('Compile-free preflight PASS; Lean validation NOT RUN')
