from pathlib import Path
import hashlib,json,subprocess
D=Path('/home/dombarker/project-offloads/codex-pv-mfe-20261029');R=D.parent/'codex-pv-replay-20261027';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();old=json.load(open(D/'replay-cohort-integrity.json'))['project_results'];bad=[]
for v in old:
 p=R/'objects'/(v['module']+'.olean')
 if not p.exists() or sha(p)!=v['object_sha256']:bad.append(v['module'])
scopes=subprocess.check_output(['systemctl','--user','list-units','--all','--no-legend','--plain','pv-mfe-lean-*.scope'],text=True)
ps=subprocess.check_output(['ps','-eo','args'],text=True);queues=[x for x in ps.splitlines() if '/codex-pv-mfe-20261029/PV_MF_' in x and '_queue.py' in x]
runs=[json.load(open(p)) for p in D.glob('lean-*/result.json')];(D/'collection.json').write_text(json.dumps(dict(completed=len(runs),original_replay_objects_checked=len(old),original_replay_object_mismatches=bad,task_scopes=scopes,active_queues=queues),indent=2)+'\n');print('completed',len(runs),'original replay object mismatches',bad,'task scopes',scopes.strip())
