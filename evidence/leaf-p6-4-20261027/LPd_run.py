"""Serial calls to existing admission/runner; no launcher implementation changes."""
from pathlib import Path
import subprocess,sys,json,time
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-leaf-p6-4-20261027'
a=sys.argv[1]
def ssh(s):return subprocess.run(['ssh',H,s],capture_output=True,text=True)
def get(n):
 (E/n).parent.mkdir(parents=True,exist_ok=True)
 subprocess.run(['scp','-q',H+':'+B+'/'+n,str(E/n)],check=True)
for retry in range(11):
 log=a+f'-barrier-{retry}.log';r=ssh(f'python3 /home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py {B}/{a}-reservation.json > {B}/{log} 2>&1');get(log)
 exists=ssh(f'test -f {B}/{a}-reservation.json').returncode==0
 if not exists and retry==0:time.sleep(30);continue
 if exists:
  get(a+'-reservation.json');ad=json.loads((E/(a+'-reservation.json')).read_text())
  if r.returncode==0 and ad['allowed']:break
  if (r.returncode==78 or 'quiet window' in ad.get('reason','')) and retry<10:print('reservation wait',flush=True);time.sleep(180);continue
 if 'FileNotFoundError' in (E/log).read_text() and retry==0:time.sleep(30);continue
 raise SystemExit('STOP admission '+r.stdout+r.stderr)
else:raise SystemExit('STOP admission retries')
x=json.loads((E/(a+'.json')).read_text());x['reservation_retries']=retry
(E/(a+'.json')).write_text(json.dumps(x,indent=2)+'\n')
# Graph and lock audited afresh before each Kani launch, using --locked --offline.
if x['kind']=='kani':
 r=ssh(f'cd {B} && sha256sum LPd_src/Cargo.lock && /home/dombarker/.cargo/bin/cargo metadata --manifest-path LPd_src/Cargo.toml --locked --offline --format-version 1 > {a}-graph.json 2> {a}-graph.stderr')
 (E/(a+'-graph-command.log')).write_text(r.stdout+r.stderr)
 get(a+'-graph.json');get(a+'-graph.stderr')
 import tomllib,hashlib
 lock=tomllib.loads(Path('Cargo.lock').read_text());frozen={(p['name'],p['version'],p.get('source')) for p in lock['package']}
 graph=json.loads((E/(a+'-graph.json')).read_text());added=[(p['name'],p['version'],p.get('source')) for p in graph['packages'] if (p['name'],p['version'],p.get('source')) not in frozen]
 assert r.returncode==0 and not added and r.stdout.startswith('5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'),(r,added)
 # Keep one full graph and per-run hash; graphs differ only after source module changes.
 (E/(a+'-graph-check.json')).write_text(json.dumps(dict(added=added,graph_sha256=hashlib.sha256((E/(a+'-graph.json')).read_bytes()).hexdigest(),frozen_lock_unchanged=True),indent=2)+'\n')
 (E/(a+'-graph.json')).unlink()
subprocess.run(['scp','-q',str(E/(a+'.json')),H+':'+B+'/'+a+'.json'],check=True)
runner='S2W_lean_host.py' if x['kind']=='lean' else 'S2W_run_host.py'
r=ssh(f'cd {B} && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 {runner} {a}.json')
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
for f in ['receipt.json','stdout.log','time.log']:get(a+'/'+f)
rc=json.loads((E/a/'receipt.json').read_text());print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']}));print((E/a/'stdout.log').read_text()[-6000:])
