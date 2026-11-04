from pathlib import Path
import subprocess,json,hashlib,sys,time
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-slice-s-compose7-20261029'
def remote(code):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input=code,text=True,capture_output=True)
 assert r.returncode==0,r.stderr
 return r.stdout
# Reservation output is redirected on host before source transfer.
print(remote(f'''from pathlib import Path
import subprocess,json
b=Path({B!r});b.mkdir(exist_ok=True)
p=b/'NEU_SETUP-barrier.log'
with p.open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/'NEU_SETUP-reservation.json')],stdout=f,stderr=subprocess.STDOUT)
print(json.dumps(dict(exit=r.returncode,log=p.read_text(),reservation=json.loads((b/'NEU_SETUP-reservation.json').read_text()))))
'''),end='')
