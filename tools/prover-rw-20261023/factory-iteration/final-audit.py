"""Local read-only packet audit; no compilation or proof replay."""
from pathlib import Path
import hashlib,json,subprocess
D=Path(__file__).resolve().parent;R=D.parents[2]
E=R/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/factory-iteration'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
subprocess.run(['python3',str(D/'source.py'),'--check'],check=True)
subprocess.run(['python3',str(D/'cut-source.py'),'--check'],check=True)
f=json.loads((D/'frame-source-map.json').read_text());a=json.loads((D/'source-map.json').read_text());s=(D/'proof-frame/selected.rs').read_text()
assert sha(D/'proof-frame/selected.rs')==f['selected_sha256']
assert hashlib.sha256(s.replace(f['additional_annotation'],'').replace(a['annotation'],'').encode()).hexdigest()==a['erased_selected_sha256']
assert not subprocess.check_output(['git','diff','745f551f8485241f7b5e74bf5945169dbf14b1fb','--','crates','programs'],cwd=R)
rows=[]
for p in sorted((E/'packet').glob('*/receipt.json')):
 r=json.loads(p.read_text());pre=json.loads((p.parent/'preflight.json').read_text())
 assert r['source_sha256']==pre['source_sha256']
 assert hashlib.sha256(json.dumps(pre['source_sha256'],sort_keys=True).encode()).hexdigest()==pre['dependency_fingerprint']
 assert r['print_axioms'].startswith('N/A:')
 for name in ['admission-before.json','admission-barrier.json']:
  a=json.loads((p.parent/name).read_text());assert a['allowed'] and a['projected_reserved_bytes']<55*2**30
 limits=json.loads((p.parent/'admission-barrier.json').read_text())['limits']
 assert limits=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0','pids.max':'64'}
 rows.append(dict(path=str(p.relative_to(E)),sha256=sha(p),exit_status=r['exit_status']))
for p in [*D.rglob('*'),*E.rglob('*')]:
 if p.is_file():
  assert p.suffix not in ['.olean','.rlib','.so','.elf','.out'],p
  if p.suffix=='.json':assert p.stat().st_size<=5_000_000,p
print(json.dumps(dict(schema='ProverRwFactoryIteration-local-audit-v1',receipts=rows,source_erasure='PASS for055/057 annotations',cut_factoring='PASS syntactic only; semantic equivalence OPEN',shipped_source_changes=False,print_axioms='N/A: no Lean declaration or emitted theorem')))
