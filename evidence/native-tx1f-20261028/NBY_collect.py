from pathlib import Path
import sys,json,hashlib,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1];sys.path.insert(0,str(E));import NBY_host as h
names=[p.stem for p in E.glob('NBY_K[0-9][0-9][0-9].json') if (E/p.stem/'receipt.json').is_file()]+[p.stem for p in E.glob('NBY_L[0-9][0-9][0-9].json') if (E/p.stem/'receipt.json').is_file()]
r=h.remote_py(f'''from pathlib import Path
import json
b=Path({h.B!r});out={{}}
for a in {names!r}:
 for suffix in ['.json','-graph.json','-metadata.stderr']:
  p=b/(a+suffix)
  if p.is_file():out[p.name]=p.read_text()
 root=b/a/'sources'
 for p in root.rglob('*'):
  if p.is_file():out[str(p.relative_to(b))]=p.read_text()
print(json.dumps(out))''');assert r.returncode==0,r.stderr
for n,s in json.loads(r.stdout).items():
 p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
print('collected',len(names),'receipts and immutable source snapshots')
