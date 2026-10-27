"""Read-only observation of exactly one owned native scope; never kills jobs."""
from pathlib import Path
import subprocess,json,re,sys
root=Path(__file__).resolve().parents[2];ev=root/'evidence/pv-cb-20261026';name=sys.argv[1]
assert re.fullmatch('[a-zA-Z0-9-]+',name)
base='/home/dombarker/project-offloads/codex-pv-cb-20261026'
code='''from pathlib import Path
import json,re
p=Path(BASE)/NAME
s=(p/'output.log').read_text();m=re.search(r'Running as unit: ([^;\\s]+)',s);assert m,s[:200]
u=m[1];c=Path('/sys/fs/cgroup/user.slice/user-1000.slice/user@1000.service/app.slice')/u
r={'unit':u,'scope_exists':c.exists(),'during_run':MODE=='sample'}
r['processes']=[]
if c.exists():
 r['metrics']={x:(c/x).read_text().strip() for x in ['memory.current','memory.peak','memory.swap.current','memory.swap.peak','memory.high','memory.max','memory.swap.max','pids.max'] if (c/x).exists()}
 for pid in (c/'cgroup.procs').read_text().split():
  try:r['processes'].append({'pid':int(pid),'command':(Path('/proc')/pid/'cmdline').read_bytes().replace(b'\\0',b' ').decode(errors='replace')})
  except FileNotFoundError:pass
if MODE=='cleanup':assert not c.exists() or not (c/'cgroup.procs').read_text().strip(),'scope still populated'
r['scope_absent_or_empty']=not bool(r['processes'])
print(json.dumps(r,indent=2))
'''.replace('BASE',repr(base)).replace('NAME',repr(name)).replace('MODE',repr(sys.argv[2]))
s=subprocess.check_output(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True)
if sys.argv[2]!='sample' or json.loads(s)['scope_exists']:
 (ev/name/('cgroup-sample.json' if sys.argv[2]=='sample' else 'cleanup.json')).write_text(s+'\n')
print(name,sys.argv[2],json.loads(s)['scope_exists'])
