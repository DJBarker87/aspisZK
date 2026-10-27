from pathlib import Path
import subprocess,json,hashlib
H='dombarker@100.108.41.90';D='/home/dombarker/project-offloads/codex-pv-batch2-20261027';E=Path('evidence/pv-batch2-20261027')
for packet in ['extraction','extraction-weights']:
 code='''from pathlib import Path
import json,hashlib
D=Path(DIR)
print(json.dumps({str(p.relative_to(D)):dict(bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in D.rglob('*') if p.is_file()}))
'''.replace('DIR',repr(D+'/'+packet))
 r=subprocess.run(['ssh',H,'python3 -'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
 manifest=json.loads(r.stdout);o=E/packet;o.mkdir(exist_ok=True)
 (o/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
 for name in manifest:
  if name.endswith('.llbc'):continue
  p=o/name;p.parent.mkdir(parents=True,exist_ok=True)
  raw=subprocess.check_output(['ssh',H,'cat '+D+'/'+packet+'/'+name]);assert hashlib.sha256(raw).hexdigest()==manifest[name]['sha256'];p.write_bytes(raw)
