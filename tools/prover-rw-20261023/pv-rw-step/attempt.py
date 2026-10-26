"""One focused compile through the unchanged shared launcher; no retries."""
from pathlib import Path
import subprocess,sys
r=Path(__file__).resolve().parents[3]
a=int(sys.argv[1]);m=sys.argv[2]
assert 23700<=a<=23999 and m.startswith('PV_RW_') and m.replace('_','').isalnum()
h='dombarker@100.108.41.90';b='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023';s='/home/dombarker/project-offloads/aspis-joint-20261019/sources/R1Z/'
def run(args):subprocess.run(args,check=True)
run(['ssh',h,f'python3 {b}/src/tools/prover-rw-20261023/native-entropy/reservation.py {b}/pv-rw-step/{a}-admission.json > {b}/pv-rw-step/{a}-admission.log 2>&1; pv_rw_admit_status=$?; cat {b}/pv-rw-step/{a}-admission.log; exit $pv_rw_admit_status'])
run(['scp',str(r/'docs/research/v8-r0-zk-20261009/lean/R1Z'/f'{m}.lean'),h+':'+s])
rev=subprocess.check_output(['git','rev-parse','HEAD'],cwd=r,text=True).strip()+'+uncommitted'
run(['ssh',h,f'python3 {b}/pv-rw-step/input.py {a} R1Z/{m} {rev} > {b}/pv-rw-step/{a}-fp.txt && sh /home/dombarker/project-offloads/r1-privacy-build-integration-20261019/tools/run-joint.sh {a} R1Z/{m} J 7000 8 "$(cat {b}/pv-rw-step/{a}-fp.txt)"'])
