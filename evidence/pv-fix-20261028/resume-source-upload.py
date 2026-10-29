from pathlib import Path
import subprocess,json,hashlib
E=Path('evidence/pv-fix-20261028');g=json.loads((E/'inherited-rdcd-fingerprint.json').read_text())['modules'];payload={};pins={}
for m,r in g.items():
 b=subprocess.check_output(['git','cat-file','blob',r['blob']]);assert hashlib.sha256(b).hexdigest()==r['sha256'];assert subprocess.check_output(['git','rev-parse','HEAD:'+r['path']]).decode().strip()==r['blob']
 payload[m]=b.decode();pins[m]={k:r[k] for k in ['path','blob','sha256','authority']}
(E/'resume-source-pins.json').write_text(json.dumps(pins,indent=2)+'\n')
code="from pathlib import Path;import json,sys;d=Path('/home/dombarker/project-offloads/codex-pv-fix-20261028/rdcd/sources');data=json.load(sys.stdin);\nfor m,s in data.items():\n p=d/(m+'.lean');p.parent.mkdir(parents=True,exist_ok=True);assert not p.exists() or p.read_text()==s,m;p.write_text(s) if not p.exists() else None"
p=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+__import__('shlex').quote(code)],input=json.dumps(payload).encode());assert p.returncode==0
