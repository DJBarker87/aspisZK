"""One module per existing Env-J launcher call; fingerprint direct effective imports."""
from pathlib import Path
import subprocess,json,hashlib,shlex,sys,re
root=Path(__file__).resolve().parents[2];a,module=sys.argv[1:3];host='dombarker@100.108.41.90';base='/home/dombarker/project-offloads';out=root/'evidence/pv-op134-20261027'
source=root/'docs/research/v8-r0-zk-20261009/lean'/f'{module}.lean'
if not source.exists():source=root/'docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023'/f'{module.split("/")[-1]}.lean'
assert source.exists(),source
imports=re.findall(r'^import (\S+)',source.read_text(),re.M)
code='''from pathlib import Path
import json,hashlib
base=Path(%r)
e=json.loads((base/'r1-privacy-build-integration-20261019/env/J.json').read_text())
paths=[str(base/'aspis-joint-20261019/objects')]+e['LEAN_PATH'].split(':')
r={}
for imp in %r:
 for p in paths:
  q=Path(p)/(imp.replace('.','/')+'.olean')
  if q.exists():r[imp]={'path':str(q),'sha256':hashlib.sha256(q.read_bytes()).hexdigest()};break
 else:r[imp]='MISSING'
print(json.dumps(r,sort_keys=True))
'''%(base,imports)
def ssh(c):return subprocess.run(['ssh',host,c],text=True,capture_output=True)
r=ssh('python3 -c '+shlex.quote(code));assert r.returncode==0,r.stderr;ids=json.loads(r.stdout);fp=hashlib.sha256(json.dumps(ids,sort_keys=True).encode()).hexdigest()
(out/f'{a}-preflight.json').write_text(json.dumps(dict(module=module,dependency_objects=ids,deps_fingerprint=fp,revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()),indent=2)+'\n')
# Shared sources must already be uploaded under this job's prefix or be unchanged extracted imports.
r=ssh(f'{base}/codex-pv-op134-20261027/run-joint.sh {a} {module} J 7000 8 {fp}')
(out/f'launch-{a}-resume.log').write_text(r.stdout+r.stderr);print(r.stdout+r.stderr)
if 'exit=' in r.stdout:
 subprocess.run([sys.executable,str(root/'tools/pv-op134-20261027/receipt.py'),a,module],check=True)
 sys.exit(json.loads((out/f'{a}.json').read_text())['exit'])
else:
 (out/f'{a}-refusal.json').write_text(json.dumps(dict(attempt=int(a),charged=False,exit=r.returncode,reason=r.stdout+r.stderr,module=module),indent=2)+'\n')
 sys.exit(r.returncode)
