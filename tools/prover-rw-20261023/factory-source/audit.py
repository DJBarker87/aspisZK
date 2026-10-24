"""Read-only local evidence/source checks; no builds or proof replay."""
from pathlib import Path
import hashlib,json,subprocess
D=Path(__file__).resolve().parent;R=D.parents[2]
E=R/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/factory-source'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for p in [D.parent/'factory-cleanup/source.py',D.parent/'factory-iteration/cut-source.py',D/'source.py']:
 subprocess.run(['python3',str(p),'--check'],check=True)
assert not subprocess.check_output(['git','diff','4b3e17fb01048bb79c26ff2363a5475827e58f1a','--','crates','programs'],cwd=R)
for O in sorted((E/'packet').iterdir()):
 pre=json.loads((O/'preflight.json').read_text());ad=json.loads((O/'admission-before.json').read_text());receipt=json.loads((O/'receipt.json').read_text())
 assert not ad['allowed'] and not receipt['extraction_executed']
 assert receipt['exit_status']==1 and receipt['print_axioms'].startswith('N/A:')
 assert pre['dependency_fingerprint']==hashlib.sha256(json.dumps(pre['source_sha256'],sort_keys=True).encode()).hexdigest()
 assert receipt['preflight_sha256']==sha(O/'preflight.json')
 assert receipt['admission_sha256']==sha(O/'admission-before.json')
 for p in (O/'source-inputs').rglob('*'):
  if p.is_file():
   host='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/factory-source/'+str(p.relative_to(O/'source-inputs'))
   assert pre['source_sha256'][host]==sha(p),(O,p)
 assert not (O/'admission-barrier.json').exists() and not (O/'raw-output').exists()
for p in [*D.rglob('*'),*E.rglob('*')]:
 if p.is_file():
  assert p.suffix not in ('.olean','.rlib','.so','.elf','.llbc','.o','.pyc'),p
  if p.suffix=='.json':assert p.stat().st_size<=5_000_000,p
print('PASS: prospective source bytes, original unchanged,056 association, three rejected admissions and original preflight hashes; no actual extraction/axiom/artifact claim')
