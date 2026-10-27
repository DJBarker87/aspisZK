"""After all gates, remove exact observed own solver temps and own Rust targets.
Retain sources, evidence, pinned tools and accepted Lean artifacts. No key paths.
"""
from pathlib import Path
import subprocess,json,re
root=Path(__file__).resolve().parents[2];ev=root/'evidence/pv-cb-20261026';t=json.loads((ev/'RESUME5-TALLY.json').read_text())
assert t['lean_charged']==100 and t['kani_charged']==12
assert all(x['state']=='complete' for x in t['kani_runs'])
files=set();units=[]
for run in t['kani_runs']:
 p=ev/run['name'];c=json.loads((p/'cleanup.json').read_text());assert c.get('scope_absent_or_empty') or (c.get('scope_exists_after') is False and not c.get('processes_after'));units.append(c['unit'])
 s=p/'cgroup-sample.json'
 if s.exists():
  r=json.loads(s.read_text())
  for proc in r.get('processes',[]):
   for f in re.findall(r'/tmp/external-sat[^\s\x00]*\.cnf',proc['command']):files.add(f)
code='''from pathlib import Path
import os,json,shutil
base=Path('/home/dombarker/project-offloads/codex-pv-cb-20261026')
for unit in UNITS:
 c=Path('/sys/fs/cgroup/user.slice/user-1000.slice/user@1000.service/app.slice')/unit
 assert not c.exists() or not (c/'cgroup.procs').read_text().strip(),unit
removed=[]
for name in FILES:
 p=Path(name);assert p.parent==Path('/tmp') and p.name.startswith('external-sat') and p.suffix=='.cnf'
 if p.exists():
  assert p.is_file() and not p.is_symlink() and p.stat().st_uid==os.getuid(),name
  removed.append({'path':name,'size':p.stat().st_size});p.unlink()
 else:removed.append({'path':name,'already_absent':True})
cache=[]
for name in ['source-kani-target','charon-target','config-target']:
 p=base/name;assert p.parent==base and not p.is_symlink()
 if p.exists():shutil.rmtree(p);cache.append(str(p))
print(json.dumps({'own_solver_temps':removed,'own_rust_caches_removed':cache,'retained':'source/evidence/pinned-tools/accepted Lean objects','wallet_keys':'No keys were created, modified or deleted'},indent=2))
'''.replace('UNITS',repr(units)).replace('FILES',repr(sorted(files)))
s=subprocess.check_output(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True)
(ev/'RESUME5-FINAL-CLEANUP.json').write_text(s+'\n');print(s)
