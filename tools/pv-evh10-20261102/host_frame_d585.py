"""Read-only recovery verification of D585 evidence and pinned objects."""
from pathlib import Path
import hashlib,json,shlex,subprocess
E=Path('evidence/pv-evh10-20261102')
H='/home/dombarker/project-offloads/codex-pv-evh-20261029'
code='''from pathlib import Path
import hashlib,json,subprocess,time
p=Path(HOSTROOT)
quiet=Path('/home/dombarker/project-offloads/QUIET_WINDOW.json')
files={}
for a in range(90259,90267):
 for stem,suffix in [('admission','json'),('out','log'),('time','log')]:
  q=p/'evidence'/f'{stem}-{a}.{suffix}';files[q.name]=hashlib.sha256(q.read_bytes()).hexdigest()
modules=['PV_EVH_PhysicalFrame','PV_EVH_FrameTransitions','PV_EVH_FrameSource','PV_EVH_FrameWorld']
print(json.dumps(dict(epoch=time.time(),quiet=quiet.read_text() if quiet.exists() else None,
 units=subprocess.check_output(['systemctl','--user','list-units','pv-evh-*','--all','--no-pager'],text=True),
 files=files,objects={m:hashlib.sha256((p/'objects'/(m+'.olean')).read_bytes()).hexdigest() for m in modules})))
'''.replace('HOSTROOT',repr(H))
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],capture_output=True,text=True)
assert r.returncode==0,r.stderr
host=json.loads(r.stdout)
assert '0 loaded units listed.' in host['units']
for name,digest in host['files'].items():
 assert hashlib.sha256((E/name).read_bytes()).hexdigest()==digest
for a in range(90259,90267):
 receipt=json.loads((E/f'receipt-{a}.json').read_text())
 if receipt['accepted']:
  assert host['objects'][receipt['target']]==receipt['object_sha256']
(E/'host-final-D585.json').write_text(json.dumps(host,indent=2)+'\n')
print('PASS D585 recovered host evidence/object hashes; no owned live scope')
