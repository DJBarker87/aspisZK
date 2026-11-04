from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
x=json.loads((E/'NFC_PROOF_ROOTS.json').read_text());modules=x['modules']+['NFC_TailSources','NFC_FinalAudit']
code=f'''from pathlib import Path
import json,hashlib,shutil
B=Path('/home/dombarker/project-offloads/codex-cx-slice-q-mul5-20261029');C=Path('/home/dombarker/project-offloads/codex-cx-slice-q-mul5-cache-20261029');entries=[]
for name in {modules!r}+['NFA_WALKER','NFA_MemoryLimit']:
 sub='NFC_audit_support_20261104' if name.startswith('NFA_') else 'NFC_exports_20261104'
 for suffix in ['.olean','.olean.private','.olean.server','.ir']:
  p=B/'NFC_objects'/(name+suffix)
  if not p.is_file():continue
  q=C/sub/(name+suffix);q.parent.mkdir(parents=True,exist_ok=True)
  h=hashlib.sha256(p.read_bytes()).hexdigest()
  if q.exists():assert hashlib.sha256(q.read_bytes()).hexdigest()==h
  else:shutil.copyfile(p,q)
  assert hashlib.sha256(q.read_bytes()).hexdigest()==h
  entries.append(dict(module=name,source=str(p),destination=str(q),sha256=h,bytes=q.stat().st_size))
assert len({{x['module'] for x in entries if x['destination'].endswith('.olean')}})=={len(set(modules))+2}
print(json.dumps(dict(cache=str(C),entries=entries,qualification='Standalone NFC forest only; no combined headline object. Own cache retained.')))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,capture_output=True,text=True);assert r.returncode==0,r.stderr
(E/'NFC_EXPORTS.json').write_text(r.stdout);print(len(json.loads(r.stdout)['entries']),'objects/sidecars copied and hash checked')
