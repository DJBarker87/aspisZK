"""Read-only timing hint; always followed by the unchanged real admission gate."""
from pathlib import Path
import subprocess,json,time,shlex
root=Path(__file__).resolve().parents[2];out=root/'evidence/pv-cblib-20261027'
code='''import importlib.util,json,datetime,hashlib
from pathlib import Path
p=Path('/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy/reservation.py')
s=importlib.util.spec_from_file_location('standing_inventory',p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
r={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'read-only timing hint, no reservation or permission; real gates still required','scanner_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'ready':False}
try:
 rows=m.inventory(Path('/sys/fs/cgroup'));total=sum(x['charged_bytes'] for x in rows)
 r.update(bounded_reserved_bytes=total,requested_bytes=8*m.GIB,safe_limit_bytes=m.LIMIT,ready=total+8*m.GIB<m.LIMIT)
except (OSError,ValueError) as e:r['error']=str(e)
print(json.dumps(r))'''
while True:
 p=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],text=True,capture_output=True)
 try:r=json.loads(p.stdout)
 except ValueError:r={'ready':False,'transport_error':p.stderr,'time':time.time()}
 with (out/'capacity-timing.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
 if p.returncode==0 and r.get('ready'):break
 time.sleep(10)
