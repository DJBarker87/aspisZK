from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
jobs=[('NLE_L065','lean','NLE_Driver'),('NLE_L066','lean','NLE_ProofDriver'),('NLE_L067','link','NLE_Driver'),('NLE_L068','link','NLE_ProofDriver'),('NLE_L069','audit','fixtures'),('NLE_L070','audit','scan')]
for i in range(len(json.loads((E/'NLE_AUDIT_ROOTS.json').read_text())['groups'])):jobs.append(('NLE_L'+str(71+i).zfill(3),'audit','batch'+str(i)))
start=int(sys.argv[1]) if len(sys.argv)>1 else 0
for i,(attempt,kind,target) in enumerate(jobs):
 if i<start:continue
 assert not (E/attempt).exists(),'No replay of existing attempt'
 r=subprocess.run([sys.executable,str(E/'NLE_run.py'),attempt,kind,target])
 if r.returncode:sys.exit(r.returncode)
