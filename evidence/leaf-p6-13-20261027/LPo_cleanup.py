"""Check selected hashes and remove only this job's rebuildable caches."""
from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-leaf-p6-13-20261027'
code=f'''from pathlib import Path
import json,hashlib,shutil,subprocess
B=Path('{B}');pins={{}}
active=subprocess.run(['pgrep','-af','^(/usr/bin/)?python3 S2W_(run|lean)_host.py LPo_'],capture_output=True,text=True)
assert not active.stdout,active.stdout
for p in B.glob('LPo_*/receipt.json'):
 r=json.loads(p.read_text())
 for x in r.get('deps_fingerprint',{{}}).get('selected_objects',{{}}).values():pins[x['path']]=x['sha256']
 pins.update(r.get('deps_fingerprint',{{}}).get('aeneas_library_objects',{{}}))
for p,h in pins.items():assert hashlib.sha256(Path(p).read_bytes()).hexdigest()==h,p
rows=[]
for name in ['LPo_target','LPo_objects']:
 p=B/name;size=sum(q.stat().st_size for q in p.rglob('*') if q.is_file()) if p.exists() else 0
 rows.append({{'path':str(p),'bytes':size}})
 if p.exists():shutil.rmtree(p)
p=B/'LPo_circle_probe'
if p.exists():rows.append({{'path':str(p),'bytes':p.stat().st_size}});p.unlink()
removed=[]
for p in (B/'LPo_tmp').glob('*'):
 if p.is_file() and (p.name.startswith('external-sat') or p.name.startswith('smt2_dec_problem')):removed.append(str(p));p.unlink()
o={{'checked_object_hashes':len(pins),'removed_rebuildable':rows,'removed_owned_solver_temps':removed,'active_own_scope':False,'shared_cache_modified':False,'wallet_keys_created_deleted':0}}
(B/'LPo_CLEANUP.json').write_text(json.dumps(o,indent=2)+'\\n')
print(json.dumps(o))
'''
r=subprocess.run(['ssh',H,"python3 - <<'REMOTE'\n"+code+'\nREMOTE'],capture_output=True,text=True,check=True);print(r.stdout)
subprocess.run(['scp','-q',H+':'+B+'/LPo_CLEANUP.json',str(E/'LPo_CLEANUP.json')],check=True)
