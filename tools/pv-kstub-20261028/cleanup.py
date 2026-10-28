"""Inventory and remove only this completed job's rebuildable proof caches."""
from pathlib import Path
import subprocess,json,time,shutil
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-kstub-20261028'
assert len(list(E.glob('K??/receipt.json')))==30
assert len(list(E.glob('447??/receipt.json')))==10
assert json.loads((E/'validation.json').read_text())['ok']
code='''from pathlib import Path
import json,hashlib,shutil,subprocess
D=Path('/home/dombarker/project-offloads/codex-pv-kstub-20261028')
live=[]
for line in subprocess.check_output(['ps','-u','dombarker','-o','pid,comm,args'],text=True).splitlines():
 if str(D) in line and any(x in line for x in ['cargo-kani','cbmc','/lean ','kissat']):live.append(line)
assert not live,live
objects=[]
for p in sorted((D/'lean-objects').glob('*.olean')):objects.append(dict(path=str(p),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
removed=[]
for name in ['target','lean-objects','tmp-Kani']:
 p=D/name
 assert p.parent==D and not p.is_symlink()
 size=sum(f.stat().st_size for f in p.rglob('*') if f.is_file()) if p.exists() else 0
 if p.exists():shutil.rmtree(p)
 removed.append(dict(path=str(p),bytes=size,exists_after=p.exists()))
record=dict(live_own_proof_processes=live,compiled_objects=objects,removed_rebuildable_caches=removed,retained='All source freezes, admission logs, outputs, times and proof sources. No keys were created or removed; global/unattributed temporary files untouched.')
(D/'cleanup.json').write_text(json.dumps(record,indent=2));print(json.dumps(record))
'''
for k in range(11):
 q=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -'],input=code,text=True,capture_output=True)
 if q.returncode!=255:break
 with (E/'cleanup-transport.jsonl').open('a') as f:f.write(json.dumps(dict(exit=255,attempt=k,time=time.time(),stderr=q.stderr))+'\n')
 if k<10:time.sleep(60)
assert q.returncode==0,q.stderr
(E/'cleanup.json').write_text(q.stdout)
p=R/'tools/pv-kstub-20261028/__pycache__'
if p.exists():shutil.rmtree(p)
print('Only owned rebuildable caches removed; evidence retained')
