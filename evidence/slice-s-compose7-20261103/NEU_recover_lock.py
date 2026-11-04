"""Read-only timeout lock/scope recovery, never launch or resubmit."""
from pathlib import Path
import subprocess,json,hashlib,sys
E=Path(__file__).resolve().parent;a=sys.argv[1];assert a.startswith('NEU_')
B='/home/dombarker/project-offloads/codex-cx-slice-s-compose7-20261029'
code=f'''from pathlib import Path
import json,hashlib
b=Path({B!r});r=json.loads((b/{(a+'/receipt.json')!r}).read_text());cg=Path(r['cgroup']);p=b/'NEU_src/Cargo.lock';h=hashlib.sha256(p.read_bytes()).hexdigest();print(json.dumps(dict(attempt={a!r},before='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef',after=h,unchanged=h=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef',read_only_recovery=True,scope_exists=cg.exists(),scope_events=(cg/'cgroup.events').read_text() if cg.exists() else 'removed')))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
d=json.loads(r.stdout);assert d['unchanged'];assert not d['scope_exists'] or 'populated 0' in d['scope_events'];(E/(a+'-lock-check.json')).write_text(json.dumps(d,indent=1)+'\n');print(r.stdout)
