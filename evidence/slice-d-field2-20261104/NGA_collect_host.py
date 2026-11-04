from pathlib import Path
import subprocess,json,base64,hashlib
E=Path(__file__).resolve().parent
code='''from pathlib import Path
import json,base64,hashlib
B=Path('/home/dombarker/project-offloads/codex-cx-slice-d-field2-20261104')
names=['NGA_CACHE_END.json','NGA_CACHE_INVENTORY.json.xz','NGA_CACHE_INVENTORY.json.sha256','NGA_L009.json','NGA_L011.json']
print(json.dumps({n:base64.b64encode((B/n).read_bytes()).decode()for n in names}))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
assert r.returncode==0,r.stderr
for name,data in json.loads(r.stdout).items():(E/name).write_bytes(base64.b64decode(data))
# Keep the two prelaunch errors in the main attempt ledger as explicitly unmeasured failures.
rows=[json.loads(l)for l in (E/'NGA_ATTEMPTS.jsonl').read_text().splitlines()]
for a in ['NGA_L009','NGA_L011']:
 p=E/(a+'_CLIENT_FAILURE.json');x=json.loads(p.read_text());cfg=json.loads((E/(a+'.json')).read_text())
 x.update(source_revision=cfg['source_revision'],command=cfg['command'],source_hashes=None,deps_fingerprint=None,measurement_status='N/A: own direct-dependency pinning rejected before submission; no prover executed')
 p.write_text(json.dumps(x,indent=2)+'\n')
 if not any(r['attempt']==a for r in rows):rows.append(x)
(E/'NGA_ATTEMPTS.jsonl').write_text(''.join(json.dumps(r)+'\n'for r in sorted(rows,key=lambda r:r['attempt'])))
print(json.dumps(dict(collected=len(json.loads(r.stdout)),attempt_records=len(rows))))
