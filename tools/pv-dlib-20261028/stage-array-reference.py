from pathlib import Path
from cooldown import check_ready,refuse
import subprocess,json,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-dlib-20261028';H='dombarker@100.108.41.90';D='/home/dombarker/project-offloads/codex-pv-dlib-20261028';G='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy'
check_ready()
name=sys.argv[1];assert name.replace('-','').isalnum()
r=subprocess.run(['ssh',H,f'mkdir -p {D}/{name}; python3 {G}/reservation.py {D}/{name}/admission.json > {D}/{name}/reservation.log 2>&1'],capture_output=True,text=True)
a=subprocess.check_output(['ssh',H,f'cat {D}/{name}/admission.json'],text=True);(E/(name+'.json')).write_text(a)
if r.returncode!=0 or json.loads(a).get('allowed') is not True:
 refuse('staging '+name,{k:json.loads(a).get(k) for k in ['utc','allowed','error']});sys.exit(78)
for local,remote in [('array-owned-reference.rs','array-owned-reference.rs'),('ArrayCargo.toml.txt','Cargo.toml')]:
 subprocess.run(['scp','-q',str(R/'tools/pv-dlib-20261028'/local),H+':'+D+'/array-proof/'+remote],check=True)
