from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
code='''from pathlib import Path
import subprocess,shutil,json,time
R=Path('/home/dombarker/project-offloads/codex-pv-k4trace-20261104')
r=subprocess.run(['systemctl','--user','list-units','--type=scope','--state=running','--plain','--no-legend'],capture_output=True,text=True)
assert r.returncode==0,r.stderr
assert not any('pv-k4trace-'in l for l in r.stdout.splitlines()),r.stdout
removed=[]
for p in [R/'target',R/'tmp']:
 if p.exists():shutil.rmtree(p);removed.append(str(p))
print(json.dumps({'epoch':time.time(),'running_task_scopes':[],'removed_rebuildable_caches':removed,'preserved':'all source snapshots, receipts, traces and symbol maps','keys':'No keys generated, used or removed'}))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,capture_output=True,text=True);assert r.returncode==0,r.stderr;(E/'cleanup.json').write_text(r.stdout);print(r.stdout)
