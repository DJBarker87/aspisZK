from pathlib import Path
import json,lzma,base64,re,posixpath,subprocess,hashlib
E=Path(__file__).resolve().parent
payload=json.loads(lzma.decompress((E/'NJB_FROZEN_PAYLOAD.json.xz').read_bytes()));queue=list(payload);extra={}
while queue:
 p=queue.pop()
 if not p.endswith('.rs'):continue
 raw=base64.b64decode(payload.get(p,extra.get(p)));s=raw.decode()
 for rel in re.findall(r'#\[path\s*=\s*"([^"]+)"\]',s):
  q=posixpath.normpath(posixpath.join(posixpath.dirname(p),rel))
  if q.startswith('../'):continue
  if q in payload or q in extra:continue
  r=subprocess.run(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+q],capture_output=True)
  if r.returncode:continue # cfg-disabled or nested-inline-module interpretation: recorded below
  extra[q]=base64.b64encode(r.stdout).decode();queue.append(q)
(E/'NJB_EXTRA_INPUTS.json').write_text(json.dumps(extra,indent=1)+'\n')
x=json.loads((E/'NJB_FROZEN_FILE_PINS.json').read_text());x.update({q:hashlib.sha256(base64.b64decode(v)).hexdigest()for q,v in extra.items()});(E/'NJB_FROZEN_FILE_PINS.json').write_text(json.dumps(x))
(E/'NJB_install_paths.py').write_text('''from pathlib import Path
import json,base64,hashlib
b=Path(__file__).resolve().parent;s=b/'NJB_src';x=json.loads((b/'NJB_EXTRA_INPUTS.json').read_text())
for q,v in x.items():
 p=s/q;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(base64.b64decode(v,validate=True))
print('frozen literal path closure restored: '+str(len(x))+' files')
''')
x=dict(attempt='NJB_L006',kind='setup',module='NJB_literal_path_closure',sources=['NJB_install_paths.py','NJB_EXTRA_INPUTS.json'],command=['python3','NJB_install_paths.py'],timeout=180,env={'CARGO_TARGET_DIR':'/home/dombarker/project-offloads/codex-cx-terminal-20261107/NJB_target'},deps_fingerprint={},expected_time='Install recursively discovered unchanged literal path inputs; no compiler')
(E/'NJB_L006.json').write_text(json.dumps(x));print('additional frozen inputs:',len(extra),'bytes:',sum(len(base64.b64decode(v))for v in extra.values()))
