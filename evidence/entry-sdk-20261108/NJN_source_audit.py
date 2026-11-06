from pathlib import Path
import json,subprocess,hashlib,os
B=Path.cwd();S=B/'NJN_src';sha=lambda b:hashlib.sha256(b).hexdigest()
cmd=['/home/dombarker/.cargo/bin/cargo','metadata','--locked','--offline','--format-version','1','--features','aspis-r1-cost-probe-program/pool-adapter,aspis-r1-cost-probe-program/private-leaf-salts']
r=subprocess.run(cmd,cwd=S,capture_output=True,text=True);assert r.returncode==0,r.stderr
m=json.loads(next(l for l in r.stdout.splitlines() if l.startswith('{')))
expected=json.loads((B/'NJN_SDK_PINS.json').read_text());rows=[];sources={}
nodes={p['id']:p for p in m['resolve']['nodes']};seen=set()
def visit(i):
 if i in seen:return
 seen.add(i)
 for d in nodes[i]['dependencies']:visit(d)
visit(next(p['id'] for p in m['packages'] if p['name']=='aspis-r1-cost-probe-program'))
wanted={'solana-account-info':'2.3.0','solana-clock':'2.2.3','solana-pubkey':'2.4.0','solana-program-error':'2.2.2','solana-sysvar':'2.3.0'}
packages={p['name']:p for p in m['packages'] if p['id'] in seen and p['name'] in wanted}
assert set(packages)==set(wanted)
assert all(p['version']==wanted[n] for n,p in packages.items())
for name,p in packages.items():
 root=Path(p['manifest_path']).parent
 files=['src/lib.rs']+(['src/sysvar.rs'] if name=='solana-clock' else [])+(['src/clock.rs'] if name=='solana-sysvar' else [])
 for n in files:
  q=root/n
  if not q.exists():continue
  raw=q.read_bytes();key=f"{name}-{p['version']}/{n}";h=sha(raw);old=expected.get(key)
  if old:assert h==old['sha256'],('SDK_SOURCE_MISMATCH',key,h,old)
  rows.append(dict(package=name,version=p['version'],source=p.get('source'),path=str(q),sha256=h,bytes=len(raw),matches_initial_pin=True if old else None))
  sources[key]=raw.decode()
host_tools=[]
for name in ['S2W_run_host.py','S2W_lean_host.py']:
 q=B/name;raw=q.read_bytes();old=Path('/home/dombarker/project-offloads/codex-cx-entry-leaves-20261107')/name
 assert raw==old.read_bytes()
 host_tools.append(dict(path=str(q),predecessor=str(old),sha256=sha(raw),bytes=len(raw),unchanged=True))
 sources['host/'+name]=raw.decode()
locks=[]
for p in B.glob('NJN_K*-lock-check.json'):
 x=json.loads(p.read_text());assert x['unchanged'] and x['before']==x['after'];locks.append(dict(path=p.name,sha256=x['after']))
assert all(x['sha256']==sha((S/'Cargo.lock').read_bytes()) for x in locks)
x=dict(command=cmd,graph_sha256=sha(r.stdout.encode()),sdk=rows,host_tools=host_tools,locks=locks,CARGO_TARGET_DIR=os.environ['CARGO_TARGET_DIR'],source_lock_sha256=sha((S/'Cargo.lock').read_bytes()),sources=sources)
(B/'NJN_ACTUAL_SDK.json').write_text(json.dumps(x,indent=1)+'\n');print(json.dumps(dict(actual_sdk_sources=len(rows),all_initial_sdk_pins_match=True,post_run_lock_checks=len(locks))))
