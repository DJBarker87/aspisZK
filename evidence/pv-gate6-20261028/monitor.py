from pathlib import Path
import subprocess
CODE='''from pathlib import Path
import json,time,os
D=Path('/home/dombarker/project-offloads/codex-pv-gate6-20261028');r=dict(utc=time.time())
r['driver_tail']=(D/'stage-a2-driver.log').read_text()[-1500:]
launch=json.loads((D/'stage-a2-launch.json').read_text());r['driver_pid_exists']=Path('/proc/'+str(launch['pid'])).exists()
p=D/'combined/corpus-6000/pipeline-progress.json'
if p.exists():
 x=json.loads(p.read_text());r['progress']={k:v for k,v in x.items() if k!='cases'}
review=D/'combined/corpus-6000/pipeline-resource-reviews.jsonl'
if review.exists():
 r['last_resource_review']=json.loads(review.read_text().splitlines()[-1])
 v=r['last_resource_review'];r['driver_tail']+=' RESOURCE '+json.dumps({k:v[k] for k in ['completed_pairs','memory_current_bytes','memory_peak_bytes','pids_current','memory_swap_current_bytes']})
for n in ['pipeline-failure.json','pipeline-resources-final.json']:
 p=D/'combined/corpus-6000'/n
 if p.exists():r[n]=json.loads(p.read_text())
p=D/'stage-a-complete.json'
if p.exists():r['stage_a_complete']=json.loads(p.read_text())
print(json.dumps(r))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=CODE,text=True,capture_output=True)
print(r.stdout,r.stderr);r.check_returncode()
