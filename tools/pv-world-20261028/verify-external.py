"""Read-only h4 preflight; no Lean invocation or object replacement."""
from pathlib import Path
import hashlib,json,subprocess,datetime
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-world-20261028'
p=E/'external-object-manifest.json'
code='''from pathlib import Path
import hashlib,json,time
manifest=json.loads(MANIFEST)
d=Path('/home/dombarker/project-offloads/codex-pv-world-20261028')
e=json.loads((d/'env-J.json').read_text())
roots=[d/'lean-objects']+[Path(x) for x in e['LEAN_PATH'].split(':')]
rows=[]
for x in manifest:
 m=x['module']; expected=x['object_sha256']; authority=Path(x['path'])
 actual=next((p/(m+'.olean') for p in roots if (p/(m+'.olean')).exists()),None)
 def sha(p):
  if p is None or not p.exists():return None
  h=hashlib.sha256()
  with p.open('rb') as f:
   for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
  return h.hexdigest()
 a=sha(authority);s=a if actual==authority else sha(actual)
 rows.append(dict(module=m,authority_path=str(authority),selected_path=str(actual),expected=expected,authority_sha256=a,selected_sha256=s,ok=a==expected and s==expected))
print(json.dumps(dict(checked_at=time.time(),count=len(rows),ok=all(x['ok'] for x in rows),rows=rows)))
'''.replace('MANIFEST',repr(p.read_text()))
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True,capture_output=True)
assert r.returncode==0,r.stderr
j=json.loads(r.stdout);j.update(manifest_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),mode='read-only before any resume compile; all 5673 external objects')
(E/'external-verification.json').write_text(json.dumps(j,indent=2)+'\n')
print(json.dumps({k:v for k,v in j.items() if k!='rows'}));print(json.dumps([x for x in j['rows'] if not x['ok']]))
