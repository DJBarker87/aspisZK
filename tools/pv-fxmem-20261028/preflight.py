from pathlib import Path
import json,subprocess,hashlib
R=Path(__file__).resolve().parents[2]; E=R/'evidence/pv-fxmem-20261028'
manifest=json.loads((E/'external-object-manifest.json').read_text())
init=[x for x in manifest if x['module']=='Init' or x['module'].startswith('Init/')]
code='''from pathlib import Path
import json,hashlib,re,time
b=Path('/home/dombarker/project-offloads'); d=b/'codex-pv-fxmem-20261028'
e=json.loads((b/'r1-privacy-build-integration-20261019/env/J.json').read_text())
roots=[b/'aspis-joint-20261019/objects']+[Path(x) for x in e['LEAN_PATH'].split(':')]
hits=[];sent=b/'r1-privacy-build-integration-20261019/evidence/sent.txt'
for line in sent.read_text().splitlines():
 a=line.split()
 if len(a)>2 and a[2].isdigit() and 35500<=int(a[2])<=35599:hits.append(dict(path=str(sent),line=line))
for job in b.glob('codex-pv-*'):
 for dirname in ['runs','receipts','evidence']:
  parent=job/dirname
  if parent.exists():
   for p in parent.rglob('*'):
    if any(35500<=int(n)<=35599 for n in re.findall(r'(?<![0-9])([0-9]{5})(?![0-9])',p.name)):hits.append(dict(path=str(p)))
core=Path('/home/dombarker/.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/mem/mod.rs')
source=core.read_text()
pattern=r'pub const fn drop<T>\(_x: T\)\s*where\s*T: \[const\] Destruct,\s*\{\s*\}'
matched=re.search(pattern,source)
assert matched, 'pinned mem::drop shape changed'
source_check=dict(path=str(core),sha256=hashlib.sha256(core.read_bytes()).hexdigest(),complete_definition=matched.group(),complete_shape_match=True,boundary='automatic parameter cleanup invokes user Drop glue; the empty lexical body does not imply absence of destructor effects')
checks=[]
for x in MANIFEST:
 actual=next((root/(x['module']+'.olean') for root in roots if (root/(x['module']+'.olean')).exists()),None)
 h=hashlib.sha256(actual.read_bytes()).hexdigest() if actual else None
 checks.append(dict(module=x['module'],selected_path=str(actual),expected=x['object_sha256'],actual=h,ok=h==x['object_sha256']))
print(json.dumps(dict(utc_epoch=time.time(),id_range=[35500,35599],id_hits=hits,external=checks,drop_source_check=source_check,ok=not hits and all(x['ok'] for x in checks))))
'''.replace('MANIFEST',repr(init))
p=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True,capture_output=True)
if p.returncode: print(p.stderr);raise SystemExit(p.returncode)
x=json.loads(p.stdout);x['manifest_sha256']=hashlib.sha256((E/'external-object-manifest.json').read_bytes()).hexdigest()
(E/'PREFLIGHT.json').write_text(json.dumps(x,indent=2)+'\n')
print(json.dumps(dict(ok=x['ok'],id_hits=x['id_hits'],external_count=len(x['external']),mismatches=[v for v in x['external'] if not v['ok']])))
raise SystemExit(0 if x['ok'] else 1)
