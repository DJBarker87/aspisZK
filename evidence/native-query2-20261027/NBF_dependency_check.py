from NBF_host import *
import hashlib
selected={};uses={}
for p in E.glob('NBF_L*/receipt.json'):
 rc=json.loads(p.read_text())
 if rc['exit_status']!=0:continue
 for x in rc['deps_fingerprint']['selected_objects'].values():
  path=x['path'];assert path not in selected or selected[path]==x['sha256'],('selected object changed between accepted compiles',path)
  selected[path]=x['sha256'];uses.setdefault(path,[]).append(rc['attempt'])
r=py(f'''from pathlib import Path
import hashlib,json
expected=json.loads({json.dumps(json.dumps(selected))})
out={{p:dict(exists=Path(p).is_file(),sha256=hashlib.sha256(Path(p).read_bytes()).hexdigest() if Path(p).is_file() else None) for p in expected}}
print(json.dumps(out))
''')
assert r.returncode==0,r.stderr
actual=json.loads(r.stdout);errors=[p for p,h in selected.items() if actual[p]['sha256']!=h]
out=dict(scope='All directly selected objects/sidecars from every accepted NBF compile; resolved Aeneas library additionally checked in NBF_TERMINAL_SOURCE.json',selected_objects=len(selected),errors=errors,objects={p:dict(expected_sha256=h,current=actual[p],accepted_attempts=uses[p]) for p,h in selected.items()},full_transitive_replay_claimed=False)
(E/'NBF_SELECTED_DEPENDENCIES.json').write_text(json.dumps(out,indent=2)+'\n')
assert not errors,errors
print(json.dumps(dict(selected_objects=len(selected),errors=errors)))
