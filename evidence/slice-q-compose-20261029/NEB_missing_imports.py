from pathlib import Path
import json,subprocess,hashlib
E=Path(__file__).resolve().parent;D=json.loads((E/'NEB_DEPENDENCIES.json').read_text())
script='''from pathlib import Path
import json,hashlib
roots=[Path(p) for p in ['/home/dombarker/project-offloads/codex-cx-slice-q-compose-20261029','/home/dombarker/project-offloads/codex-cx-slice-q-compose-cache-20261029','/home/dombarker/project-offloads/codex-cx-sound-int2-20261025','/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects']]
mods=MODS
out={}
for m in mods:
 p=next((r/(m.replace('.','/')+'.olean') for r in roots if (r/(m.replace('.','/')+'.olean')).is_file()),None)
 out[m]=None if p is None else dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest())
print(json.dumps(out))
'''.replace('MODS',repr(list(D)))
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=script,text=True,capture_output=True);assert r.returncode==0,r.stderr
out=json.loads(r.stdout);(E/'NEB_IMPORT_OBJECT_INVENTORY.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps(dict(missing=[m for m,p in out.items() if p is None],present=len([1 for p in out.values() if p]))))
