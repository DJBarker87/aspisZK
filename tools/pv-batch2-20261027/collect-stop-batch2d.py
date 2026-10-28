"""Read-only host recovery of the fatal barrier receipt and retained output pins."""
from pathlib import Path
import subprocess,json,shlex
E=Path('evidence/pv-batch2-20261027/batch2d');O=E/'host-incident';O.mkdir(exist_ok=True)
code='''from pathlib import Path
import hashlib,json,stat
H=Path('/home/dombarker/project-offloads/codex-pv-batch2-20261027');D=H/'candidate/batch2d-lean-39887'
files={n:(D/n).read_text() for n in ['scope.log','command.json','refusal-classification.json','reservation.json','reservation.log','admission-barrier.json'] if (D/n).exists()}
objects=[dict(path=str(p.relative_to(H)),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size) for p in (H/'lean-objects').rglob('*.olean') if p.is_file() and not p.is_symlink()]
old=json.loads((H/'batch2c-key-retention.json').read_text());keys=[]
for k in old['keys']:
 p=Path(k['path']);keys.append(dict(path=str(p),public_key=k['public_key'],retained=p.exists(),mode=oct(stat.S_IMODE(p.stat().st_mode)) if p.exists() else None))
print(json.dumps(dict(files=files,objects=objects,keys=keys,compiler_receipt_exists=(D/'receipt/receipt.json').exists(),no_transactions=True,no_key_cleanup=True,no_cache_cleanup=True)))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],capture_output=True,text=True,check=True);j=json.loads(r.stdout)
for n,s in j.pop('files').items():(O/n).write_text(s)
assert not j['compiler_receipt_exists'];assert all(k['retained'] and k['mode']=='0o600' for k in j['keys'])
(E/'OUTPUT-OBJECT-PINS.json').write_text(json.dumps(j.pop('objects'),indent=2)+'\n')
(E/'KEY-RETENTION.json').write_text(json.dumps(j,indent=2)+'\n')
print('fatal receipt recovered; objects pinned; keys retained',len(j['keys']))
