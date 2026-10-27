"""One focused new-module compile through the unchanged shared launcher."""
from pathlib import Path
import hashlib,json,re,shlex,subprocess,sys
root=Path(__file__).resolve().parents[2];ev=root/'evidence/pv-cb-20261026'
n=int(sys.argv[1]);module=sys.argv[2];assert 38300<=n<=38599
p=root/'docs/research/v8-r0-zk-20261009/lean'/(module+'.lean')
assert p.name.startswith('PV_CB_')
assert not (ev/f'{n}-submission.json').exists()
imports=re.findall(r'^import (\S+)',p.read_text(),re.M)
probe='''import json,hashlib
from pathlib import Path
b=Path('/home/dombarker/project-offloads');j=b/'aspis-joint-20261019'
e=json.loads((b/'r1-privacy-build-integration-20261019/env/J.json').read_text())
r={}
for m in IMPORTS:
 for d in [str(j/'objects')]+e['LEAN_PATH'].split(':'):
  p=Path(d)/(m.replace('.','/')+'.olean')
  if p.exists():r[m]=hashlib.sha256(p.read_bytes()).hexdigest();break
 else:raise SystemExit('missing object '+m)
print(json.dumps(r,sort_keys=True))
'''.replace('IMPORTS',repr(imports))
host='dombarker@100.108.41.90';base='/home/dombarker/project-offloads'
deps=json.loads(subprocess.check_output(['ssh',host,'python3','-'],input=probe,text=True))
fp=hashlib.sha256(json.dumps(deps,sort_keys=True).encode()).hexdigest()
meta=dict(attempt=n,module=module,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),deps_fingerprint=fp,dependency_object_hashes=deps)
(ev/f'{n}-submission.json').write_text(json.dumps(meta,indent=2)+'\n')
# New names only; shared sources and outputs already present are snapshotted first.
dest=base+'/aspis-joint-20261019/sources/'+module+'.lean'
backup=base+'/codex-pv-cb-20261026/shared-backup-resume4/'+module
cmd=f'mkdir -p {shlex.quote(str(Path(backup).parent))}; if test -f {dest}; then cp -n {dest} {backup}.lean; fi; if test -f {base}/aspis-joint-20261019/objects/{module}.olean; then cp -n {base}/aspis-joint-20261019/objects/{module}.olean {backup}.olean; fi'
subprocess.run(['ssh',host,cmd],check=True)
subprocess.run(['scp',str(p),host+':'+dest],check=True)
cmd=shlex.join([base+'/r1-privacy-build-integration-20261019/tools/run-joint.sh',str(n),module,'J','7000','8',fp])
r=subprocess.run(['ssh',host,cmd],text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
(ev/f'{n}-launcher.log').write_text(r.stdout);print(r.stdout)
if 'exit=' in r.stdout:
 subprocess.run([sys.executable,str(root/'tools/pv-cb-20261026/receipt.py'),str(n),module],check=True)
else:print('UNCHARGED launcher refusal',r.returncode)
