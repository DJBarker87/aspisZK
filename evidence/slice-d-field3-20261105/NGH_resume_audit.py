"""Focused final replay after changed NGH model support; serial admitted scopes."""
from pathlib import Path
import subprocess,os,json,time,re
E=Path(__file__).resolve().parent
while not (E/'NGH_L022/receipt.json').exists():time.sleep(3)
assert json.loads((E/'NGH_L022/receipt.json').read_text())['exit_status']==0,'Fix focused outer model before aggregation'
subprocess.run(['python3',str(E/'NGH_make_audit.py')],check=True)
p=E/'NGH_review_batch.py';s=p.read_text();s,n=re.subn(r"out=B/'NGH_review[^']*'","out=B/'NGH_review_resume'",s);assert n==1;p.write_text(s)
env=os.environ.copy();env['NGH_REVIEW_OUTPUT']='NGH_review_resume'
for a,kind,target in [('NGH_L023','lean','NGH_COMBINED_IMPORT'),('NGH_L024','lean','NGH_Driver'),('NGH_L025','review','NGH_Driver')]:
 assert not (E/a/'receipt.json').exists()
 with (E/(a+'-client.log')).open('w')as f:r=subprocess.run(['python3',str(E/'NGH_run.py'),a,kind,target],env=env,stdout=f,stderr=subprocess.STDOUT)
 assert r.returncode==0,(a,'inspect retained diagnostics; no automatic rerun')
 print(a,'PASS',flush=True)
for script,args in [('NGH_dedup.py',[]),('NGH_certify.py',['wide','NGH_review_resume']),('NGH_tests.py',[]),('NGH_resume_validate.py',[])]:
 subprocess.run(['python3',str(E/script),*args],check=True)
(E/'NGH_RESUME_AUDIT_COMPLETE.json').write_text(json.dumps(dict(status='PASS',review='NGH_L025',combined='NGH_L023',driver='NGH_L024',source_change='two new NGH model association modules, additive helper gate wording',new_helper_closures=0),indent=1)+'\n')
