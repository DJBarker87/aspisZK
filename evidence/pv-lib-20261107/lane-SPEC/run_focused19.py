"""Serial focused job; independent turn SSH before each attempt; retain receipts."""
from pathlib import Path
import subprocess,sys,json,lzma
R=Path(__file__).resolve().parents[3];L=Path(__file__).resolve().parent
H='dombarker@100.108.41.90';P='/home/dombarker/project-offloads/codex-pv-lib-spec-20261107'
a=int(sys.argv[1]);m=sys.argv[2]
assert 55781<=a<=55789 or 56200<=a<=56289
rev=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip()
subprocess.run(['scp',str(R/'lean'/(m+'.lean')),H+':'+P+'/sources/'],check=True)
subprocess.run(['ssh',H,'STREAMB_SLOTS=3 /home/dombarker/streamb-slots/turn.sh'],check=True)
r=subprocess.run(['ssh',H,'python3',P+'/host_attempt_s19.py',str(a),m,rev,'active19'])
for f in [f'receipt-{a}.json',f'out-{a}.log',f'time-{a}.log',f'admission-{a}.json']:
 subprocess.run(['scp',H+':'+P+'/evidence/'+f,str(L/f)],check=False)
receipt=json.loads((L/f'receipt-{a}.json').read_text())
if receipt['accepted']:
 subprocess.run(['git','add','--sparse',str(R/'lean'/(m+'.lean')),str(L)],cwd=R,check=True)
 subprocess.run(['git','commit','-m',f'SPEC session19: check {m} ({a})'],cwd=R,check=True)
else:
 (L/f'failed-{a}.lean.xz').write_bytes(lzma.compress((R/'lean'/(m+'.lean')).read_bytes()))
sys.exit(r.returncode)
