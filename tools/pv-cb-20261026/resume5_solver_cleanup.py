"""Remove solver files for exact observed own CBMC PIDs after their scope ends."""
from pathlib import Path
import json,re,subprocess,sys
root=Path(__file__).resolve().parents[2];ev=root/'evidence/pv-cb-20261026';name=sys.argv[1]
assert re.fullmatch('[A-Za-z0-9-]+',name)
p=ev/name;c=json.loads((p/'cleanup.json').read_text());assert c['scope_absent_or_empty']
r=json.loads((p/'cgroup-sample.json').read_text());pids=[x['pid'] for x in r['processes'] if x['command'].startswith('cbmc ')]
code='''from pathlib import Path
from datetime import datetime
import os,json
base=Path('/home/dombarker/project-offloads/codex-pv-cb-20261026')/NAME
c=Path('/sys/fs/cgroup/user.slice/user-1000.slice/user@1000.service/app.slice')/UNIT
assert not c.exists() or not (c/'cgroup.procs').read_text().strip()
a=json.loads((base/'admission-before.json').read_text());start=datetime.fromisoformat(a['utc']).timestamp();end=(base/'time.log').stat().st_mtime
rows=[]
for pid in PIDS:
 for p in Path('/tmp').glob('external-sat'+str(pid)+'.*.cnf'):
  assert p.is_file() and not p.is_symlink() and p.stat().st_uid==os.getuid()
  st=p.stat()
  if not start-2 <= st.st_mtime <= end+2:
   rows.append({'path':str(p),'action':'kept: outside exact run window'});continue
  rows.append({'path':str(p),'size':st.st_size,'cbmc_pid':pid,'action':'removed after scope absent/empty'});p.unlink()
print(json.dumps({'unit':UNIT,'observed_own_cbmc_pids':PIDS,'exact_pid_prefix_and_run_window':True,'files':rows},indent=2))
'''.replace('NAME',repr(name)).replace('UNIT',repr(c['unit'])).replace('PIDS',repr(pids))
s=subprocess.check_output(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True)
(p/'solver-cleanup.json').write_text(s+'\n');print(s)
