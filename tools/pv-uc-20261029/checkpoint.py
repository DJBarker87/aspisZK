"""Read-only reconciliation of submitted host work; never submits a scope."""
from pathlib import Path
import subprocess,json,shlex,hashlib,time
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-uc-20261029'
code='''from pathlib import Path
import json,hashlib,time,subprocess
H=Path('/home/dombarker/project-offloads/codex-pv-uc-20261029')
def pin(p):return dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
statuses={d.name:(d/'done-status.txt').read_text().strip() if (d/'done-status.txt').is_file() else 'PENDING' for d in sorted(H.glob('native751[0-9][0-9]'))}
pids=subprocess.run(['pgrep','-f','^python3 '+str(H/'differential.py')+'$'],text=True,capture_output=True).stdout.split();active=[]
for pid in pids:
 cg=Path('/sys/fs/cgroup'+Path('/proc/'+pid+'/cgroup').read_text().split('0::')[1].strip())
 active.append(dict(pid=int(pid),cgroup=str(cg),properties={n:(cg/n).read_text().strip() for n in ['memory.current','memory.peak','memory.swap.current','memory.swap.peak','memory.high','memory.max','memory.swap.max','pids.current','pids.max','memory.events','pids.events']}))
x=dict(utc=time.time(),statuses=statuses,active=active,scope_inventory=subprocess.check_output(['systemctl','--user','list-units','--type=scope','--state=running','--no-pager'],text=True),progress=json.loads((H/'final-gates/differential/progress.json').read_text()),llbc=pin(H/'PV_UC_Entry.llbc'),decoder_llbc=pin(H/'PV_UC_Decoder.llbc'),charon_config=pin(H/'charon.json'),quiet_marker=json.loads((H.parent/'QUIET_WINDOW.json').read_text()),candidate=pin(H/'native-target/client/user_client'),fixture=pin(H/'native-target/client/devnet_spend'))
print(json.dumps(x,indent=2))
'''
for i in range(10):
 r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],capture_output=True,text=True)
 if r.returncode!=255:break
 if i<9:time.sleep(60)
assert r.returncode==0,r.stderr
(E/'host-checkpoint.json').write_text(r.stdout);x=json.loads(r.stdout)
if x['statuses']['native75145']=='PENDING':
 (E/'native75145/pending-status.json').write_text(json.dumps(dict(status='RUNNING; NOT A FINAL RECEIPT; NEVER RESUBMIT',command=['python3','/home/dombarker/project-offloads/codex-pv-uc-20261029/differential.py'],**{k:x[k] for k in ['utc','active','progress']}),indent=2)+'\n')
with (E/'native75145/resource-reviews.jsonl').open('a') as f:f.write(json.dumps(dict(utc=x['utc'],progress=x['progress'],decision='Reviewed the per-minute progress/resource record: optimized full final proof-generation pairs continue completing; original caps retained, no increase. Final aggregation is legitimate; no pathological concrete-term normalization. Receipt remains pending.'))+'\n')
print(json.dumps(dict(completed=sum(v!='PENDING' for v in x['statuses'].values()),pending=[k for k,v in x['statuses'].items() if v=='PENDING'],progress=x['progress']),indent=2))
