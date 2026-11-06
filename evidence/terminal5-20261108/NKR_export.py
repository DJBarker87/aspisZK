from pathlib import Path
import json,subprocess,base64
E=Path(__file__).resolve().parent
manifest=json.loads((E/'NKR_GATE_SOURCES.json').read_text())
code='''from pathlib import Path
import json,shutil,hashlib,subprocess
b=Path('/home/dombarker/project-offloads/codex-cx-terminal5-20261108');out=b/'NKR_exports_20261108';out.mkdir(exist_ok=True)
manifest=json.loads(INPUT)
files=[]
for r in manifest['source_extensions']:
 m=r['module'];p=b/(m+'.lean');assert hashlib.sha256(p.read_bytes()).hexdigest()==r['sha256'],str(p)
 candidates=[p]+[b/'NKR_objects'/(m+s) for s in ['.olean','.olean.private','.olean.server','.ir']]
 assert candidates[1].is_file(),m
 for q in candidates:
  if q.is_file():
   dest=out/q.name;shutil.copyfile(q,dest);files.append(dict(path=str(dest),source=str(q),bytes=dest.stat().st_size,sha256=hashlib.sha256(dest.read_bytes()).hexdigest()))
row=dict(path=str(out),status='FOCUSED_OBJECTS_ONLY_COMBINED_GATE_INCOMPLETE',files=files,bytes=sum(x['bytes']for x in files),free_bytes=shutil.disk_usage(b).free,workspace_bytes=int(subprocess.check_output(['du','-sb',str(b)]).split()[0]),cargo_target_dir=str(b/'NKR_target'))
(out/'NKR_EXPORT.json').write_text(json.dumps(row,indent=1));print(json.dumps(row))
'''.replace('INPUT',repr(json.dumps(manifest)))
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
assert r.returncode==0,r.stderr
(E/'NKR_EXPORT.json').write_text(json.dumps(json.loads(r.stdout),indent=1)+'\n')
print(json.dumps({k:v for k,v in json.loads(r.stdout).items()if k!='files'}))
