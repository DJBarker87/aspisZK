from pathlib import Path
import json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-rdcd-20261028');S=Path('/home/dombarker/project-offloads/codex-pv-fscan-20261028/src');j=json.load(open(D/'source-freeze-pins.json'));bad=[]
for r in j['files']:
 p=S/r['path'];h=hashlib.sha256(p.read_bytes()).hexdigest()
 if h!=r['sha256']:bad.append(dict(path=str(p),expected=r['sha256'],actual=h))
(D/'source-freeze-result.json').write_text(json.dumps(dict(head=j['head'],checked=len(j['files']),mismatches=bad),indent=2)+'\n');print(len(j['files']),'source pins;',len(bad),'mismatches');assert not bad
