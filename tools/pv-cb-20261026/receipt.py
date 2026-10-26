"""Collect evidence from the existing launcher; never launches or changes it."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
attempt,module=sys.argv[1:3]
root=Path(__file__).resolve().parents[2]
output=root/'evidence/pv-cb-20261026'
base='/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence'
for stem,ext in [('out','log'),('time','log'),('sha','txt')]:
 p=f'{stem}-{attempt}.{ext}'
 data=subprocess.check_output(['ssh','dombarker@100.108.41.90','cat',f'{base}/{p}'],text=True)
 (output/p).write_text(data)
out=(output/f'out-{attempt}.log').read_text();time=(output/f'time-{attempt}.log').read_text()
def field(pattern):
 m=re.search(pattern,time);return m.group(1) if m else None
source=root/'docs/research/v8-r0-zk-20261009/lean'/f'{module}.lean'
if not source.exists() and module.startswith('R1Z/ProverRw'):
 source=root/'docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023'/f'{module.split("/")[-1]}.lean'
# Direct import object identities are captured separately, with the collection time explicit.
imports=re.findall(r'^import (\S+)',source.read_text(),re.M)
probe='''import json,hashlib
from pathlib import Path
base=Path('/home/dombarker/project-offloads')
env=base/'r1-privacy-build-integration-20261019/env/J.json'
paths=[str(base/'aspis-joint-20261019/objects')]+json.loads(env.read_text())['LEAN_PATH'].split(':')
result={}
for imp in IMPORTS:
 for folder in paths:
  p=Path(folder)/(imp.replace('.','/')+'.olean')
  if p.is_file():
   result[imp]={'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()};break
 else:raise SystemExit('missing dependency object '+imp)
print(json.dumps(result))
'''.replace('IMPORTS',repr(imports))
resolved=json.loads(subprocess.check_output(['ssh','dombarker@100.108.41.90','python3','-'],input=probe,text=True))
identities={imp:record['sha256'] for imp,record in resolved.items()}
submission=output/f'{attempt}-submission.json'
revision=json.loads(submission.read_text())['source_revision'] if submission.exists() else subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip()
r=dict(attempt=int(attempt),module=module,source_revision=revision,source_sha256=(output/f'sha-{attempt}.txt').read_text().split()[0],deps_fingerprint=hashlib.sha256(json.dumps(identities,sort_keys=True).encode()).hexdigest(),dependency_object_hashes=identities,dependency_object_resolution=resolved,dependency_collection='post-run read-only snapshot using restored run2.py search order (joint objects prepended to env/J.json LEAN_PATH); no dependencies changed by this worker',exit=int(re.search(r'^exit=(\d+)',out,re.M)[1]),wall=field(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (.+)'),peak_rss_kib=int(field(r'Maximum resident set size \(kbytes\): (\d+)')),swap=int(field(r'Swaps: (\d+)')),axioms=re.findall(r"'[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)",out,re.S),limits=dict(lean_M=7000,MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64),launcher='r1-privacy-build-integration-20261019/tools/run-joint.sh')
(output/f'{attempt}.json').write_text(json.dumps(r,indent=2)+'\n')
print(attempt,r['exit'],r['wall'])
