"""Task-local admitted input/evidence transfer; no compiler or shared-tree writes."""
from pathlib import Path
import subprocess,json,sys
from cooldown import check_ready,refuse
check_ready()
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdb2f-20261029';D='/home/dombarker/project-offloads/codex-pv-rdb2f-20261029';H='dombarker@100.108.41.90';G='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy'
name=sys.argv[1];assert name.replace('-','').isalnum()
r=subprocess.run(['ssh',H,f'python3 {G}/reservation.py {D}/{name}-transfer-admission.json > {D}/{name}-transfer-admission.log 2>&1'],capture_output=True,text=True)
a=subprocess.check_output(['ssh',H,f'cat {D}/{name}-transfer-admission.json'],text=True);(E/(name+'-transfer-admission.json')).write_text(a)
if r.returncode!=0 or json.loads(a).get('allowed')is not True:
 refuse('transfer '+name,json.loads(a));sys.exit(78)
for p in sys.argv[2:]:subprocess.run(['scp','-q',p,H+':'+D+'/'],check=True)
