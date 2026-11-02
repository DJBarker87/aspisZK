"""Remove only this task's rebuildable target after final evidence validation."""
from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent;v=json.loads((E/'D549-VALIDATION.json').read_text());assert v['status']=='PASS'and v['charged_invocations']==60
code='''from pathlib import Path
import json,time,shutil,subprocess
R=Path('/home/dombarker/project-offloads/codex-pv-k3scan-20261101');p=R/'resume-target'
assert p.resolve()==Path('/home/dombarker/project-offloads/codex-pv-k3scan-20261101/resume-target')
cg=Path('/sys/fs/cgroup/user.slice/user-1000.slice/user@1000.service/app.slice');scopes=[]
for q in cg.glob('pv-k3scan-K792*.scope'):
 e=(q/'cgroup.events').read_text();assert 'populated 0'in e,(q,e);scopes.append({'scope':str(q),'events':e})
size=subprocess.check_output(['du','-sb',str(p)],text=True).strip()if p.exists()else None
out={'epoch':time.time(),'path':str(p),'size_before':size,'scope_checks':scopes,'action':'Remove only owned Cargo/Kani rebuildable target after source/symbol/receipt/lock capture and final artifact validation. Sources, run directories, snapshots and evidence retained. No keys were generated or deleted by this task.'}
if p.exists():shutil.rmtree(p)
out['exists_after']=p.exists();assert not out['exists_after'];print(json.dumps(out))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr;(E/'D549-CACHE-CLEANUP.json').write_text(json.dumps(json.loads(r.stdout),indent=2)+'\n');print(r.stdout)
