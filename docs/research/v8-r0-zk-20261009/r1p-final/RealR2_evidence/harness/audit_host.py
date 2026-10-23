from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent.parent
p=E/'lean/11012/inputs.json'
code='''from pathlib import Path
import json,hashlib
J=Path('/home/dombarker/project-offloads/aspis-joint-20261019')
env=json.loads(Path('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/env/J.json').read_text())
paths=[J/'objects']+[Path(p) for p in env['LEAN_PATH'].split(':')]
r=json.loads(%r)
checked=[]
for m,sha in r['deps']:
 rel=Path(m.replace('.','/')+'.olean')
 p=next(p/rel for p in paths if (p/rel).exists())
 actual=hashlib.sha256(p.read_bytes()).hexdigest()
 assert sha==actual,(m,sha,actual)
 checked.append(dict(module=m,sha256=actual))
print(json.dumps(dict(target=r['module'],dependency_objects=checked,all_final_dependency_pins_match=True),indent=2))
'''%p.read_text()
r=subprocess.check_output(['ssh','dombarker@100.108.41.90','python3 -'],input=code,text=True)
(E/'final-host-audit.json').write_text(r);print(r)
