"""Read-only recovery of a submitted Kani attempt; never launches anything."""
from pathlib import Path
import json,subprocess,sys,hashlib
E=Path(__file__).resolve().parent;a=sys.argv[1]
assert a.startswith('NFV_K')
names=[a+'/receipt.json',a+'/stdout.log',a+'/time.log',*[a+'-'+n for n in ['source-check.json','tools.json','metadata-pin.json','metadata.stderr','graph-check.json','lock-check.json','rule16-check.json','temp-files.json']]]
code="from pathlib import Path;import json;b=Path('/home/dombarker/project-offloads/codex-cx-pool-retdata3-20261104');print(json.dumps({n:(b/n).read_text() for n in "+repr(names)+" if (b/n).exists()}))"
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
assert r.returncode==0,r.stderr;out=json.loads(r.stdout);assert a+'/receipt.json' in out
for n,v in out.items():p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(v)
rows=[json.loads(l) for l in (E/'NFV_ATTEMPTS.jsonl').read_text().splitlines()];assert not any(row['attempt']==a for row in rows)
rc=json.loads(out[a+'/receipt.json']);row={k:v for k,v in rc.items() if k!='deps_fingerprint'};row['recovery']='read-only after submitted SSH255; never resubmitted'
with (E/'NFV_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(row)+'\n')
active=E/'NFV_ACTIVE.json';assert active.read_text()==a;active.unlink()
sys.dont_write_bytecode=True
from NFV_checkpoint import checkpoint
checkpoint()
print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps']}))
