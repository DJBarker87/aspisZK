"""Serial scratch-only Kani/metadata driver using the unchanged host launcher."""
from pathlib import Path
import subprocess,json,sys,time,hashlib,shlex,tomllib
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-slice-s-compose10-20261029';H='dombarker@100.108.41.90'
a,kind,harness=sys.argv[1:];assert kind in ['metadata','kani'];assert a.startswith('NFD_M' if kind=='metadata' else 'NFD_K')
if kind=='kani':
 assert 'fn '+harness.rsplit('::',1)[-1]+'(' in ((E/'NFD_oracle.patch').read_text()+(E/'NFD_native_contracts.patch').read_text()),'missing requested harness; no launch'
assert not (E/'NFD_LEAN_ACTIVE.json').exists();assert not (E/a).exists();assert len(list(E.glob('NFD_K*/receipt.json')))<150
assert 1<=int(a[5:])<=150 if kind=='kani' else True
active=E/'NFD_ACTIVE.json';assert not active.exists();active.write_text(json.dumps(dict(attempt=a,kind=kind)))
def ssh(code,stdin=None,submitted=False):
 for retry in range(11):
  r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','-o','ServerAliveInterval=15','-o','ServerAliveCountMax=2',H,code],input=stdin,text=True,capture_output=True)
  with (E/'NFD_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,retry=retry,exit=r.returncode,submitted=submitted,stderr=r.stderr))+'\n')
  if r.returncode!=255 or submitted:return r
  if retry<10:time.sleep(60)
 raise SystemExit('STOP transport exhausted')
for retry in range(11):
 code=f'''from pathlib import Path
import subprocess,json,sys
b=Path({B!r});p=b/{(a+'-barrier-'+str(retry)+'.log')!r}
with p.open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/{(a+'-reservation.json')!r})],stdout=f,stderr=subprocess.STDOUT)
print(p.read_text())
prior=b/'NFD_K118/receipt.json'
if prior.exists():
 info=json.loads(prior.read_text());cg=Path('/sys/fs/cgroup')/info['cgroup'].lstrip('/')
 print(json.dumps(dict(own_previous_attempt='NFD_K118',cgroup_exists=cg.exists(),events=(cg/'cgroup.events').read_text() if cg.exists() else 'removed')))
sys.exit(r.returncode)
'''
 r=ssh('python3',code);(E/(a+f'-barrier-{retry}.log')).write_text(r.stdout+r.stderr)
 try:ad=next(json.loads(l) for l in r.stdout.splitlines() if l.startswith('{'))
 except (StopIteration,json.JSONDecodeError):
  if retry==0:time.sleep(30);continue
  raise SystemExit('STOP reservation JSON missing')
 (E/(a+'-admission.json')).write_text(json.dumps(dict(exit=r.returncode,reservation=ad)))
 if r.returncode==0 and ad.get('allowed') is True:break
 if (r.returncode==78 or ad.get('allowed') is False) and retry<10:time.sleep(180);continue
 raise SystemExit('STOP admission')
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
probe=tomllib.loads(subprocess.check_output(['git','show',rev+':crates/aspis-r1-cost-probe/Cargo.toml'],text=True));stmt=tomllib.loads(subprocess.check_output(['git','show',rev+':crates/aspis-statement/Cargo.toml'],text=True))
features=['r0','pool-v1-kernel']+[s.split('/',1)[1] for s in probe['features']['optimized-terminal']]
closure=set()
def visit(n):
 if n in closure:return
 closure.add(n)
 for v in stmt['features'].get(n,[]):
  if '/' not in v and not v.startswith('dep:'):visit(v)
for n in features:visit(n)
native=['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path',B+'/NFD_src/crates/aspis-statement/Cargo.toml','--target-dir',B+'/NFD_target','--lib','--features',','.join(features),'-j','1','-Z','unstable-options','-Z','function-contracts','-Z','stubbing','--harness-timeout','90s','--exact','--harness',harness,'--output-format','terse']
if kind=='metadata':native=[]
env=dict(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_BUILD_JOBS='1',CARGO_NET_OFFLINE='true',CARGO_PROFILE_DEV_OPT_LEVEL='3',CARGO_PROFILE_DEV_DEBUG='0',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',RUSTFLAGS='-C link-arg=-Wl,--threads=1',TMPDIR=B+'/NFD_tmp')
files={'NFD_native_contracts.patch':(E/'NFD_native_contracts.patch').read_text(),'NFD_oracle.patch':(E/'NFD_oracle.patch').read_text(),'NFD_kani_gate.py':(E/'NFD_kani_gate.py').read_text(),'NFD_contract_controls.patch':(E/'NFD_contract_controls.patch').read_text(),'NFD_KMX_copy_stubs.patch':subprocess.check_output(['git','show','HEAD:evidence/kani-mitig-20261028/KMX_copy_stubs.patch'],text=True),'NFD_RUST_SOURCE_PINS.json':(E/'NFD_RUST_SOURCE_PINS.json').read_text(),'NFD_FROZEN_GRAPH.json':subprocess.check_output(['git','show','HEAD:evidence/leaf-p6-11-20261027/LPm_frozen_graph.json'],text=True)}
cfg=dict(attempt=a,kind=kind,module=harness,command=['python3','NFD_kani_gate.py',a+'.json'],native_command=native,sources=list(files)+['NFD_RUST_SHA256.json','NFD_src/Cargo.lock','NFD_src/crates/aspis-statement/src/lib.rs','NFD_src/crates/aspis-statement/src/NED_controls.rs'],env=env,timeout=180,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,deps_fingerprint=dict(frozen_revision=rev,frozen_source_pinset='NFD_RUST_SOURCE_PINS.json'),statement_features=','.join(features),required_statement_features=sorted(closure),expected_time='frozen dependency/feature validation, optimized compilation, then named call-window or interface-fidelity step; no native field arithmetic or protocol loop',copy_patch_sha256='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67')
for patchname in ['NFD_oracle.patch','NFD_native_contracts.patch']:(E/(a+'-'+patchname)).write_text(files[patchname])
files[a+'.json']=json.dumps(cfg,indent=1)
code=f'''from pathlib import Path
import json,subprocess,hashlib
b=Path({B!r});s=b/'NFD_src';files=json.loads({json.dumps(files)!r})
for n,v in files.items():(b/n).write_text(v)
(b/'NFD_tmp').mkdir(exist_ok=True)
if not (b/'NFD_RUST_SHA256.json').exists():
 pins=json.loads((b/'NFD_RUST_SOURCE_PINS.json').read_text());errors=[]
 for n,p in pins['files'].items():
  data=(s/n).read_bytes();h=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\\0'+data).hexdigest()
  if h!=p['git_blob']:errors.append(n)
 assert not errors,('frozen upload mismatch',errors)
 for patch in ['NFD_KMX_copy_stubs.patch','NFD_contract_controls.patch']:
  subprocess.run(['git','apply',str(b/patch)],cwd=s,check=True,capture_output=True)
 out={{str(p.relative_to(s)):hashlib.sha256(p.read_bytes()).hexdigest() for p in s.rglob('*') if p.is_file()}}
 (b/'NFD_RUST_SHA256.json').write_text(json.dumps(out,indent=1)+'\\n')
if not (s/'crates/aspis-statement/src/pool_v1/NFD_oracle.rs').exists():
 before=json.loads((b/'NFD_RUST_SHA256.json').read_text())
 assert all(hashlib.sha256((s/n).read_bytes()).hexdigest()==h for n,h in before.items()),'STOP pre-update source drift'
 subprocess.run(['git','apply',str(b/'NFD_oracle.patch')],cwd=s,check=True,capture_output=True)
 out={{str(p.relative_to(s)):hashlib.sha256(p.read_bytes()).hexdigest() for p in s.rglob('*') if p.is_file()}}
 (b/'NFD_RUST_SHA256.json').write_text(json.dumps(out,indent=1)+'\\n')
# Lane-owned patch revision: only our added oracle source may be replaced.
current=(b/'NFD_oracle.patch').read_text();lines=current.splitlines();lo=next(i for i,l in enumerate(lines) if l.startswith('@@ -0,0'));hi=next(i for i,l in enumerate(lines[lo+1:],lo+1) if l.startswith('--- a/'))
body='\\n'.join(l[1:] for l in lines[lo+1:hi] if l.startswith('+'))+'\\n'
q=s/'crates/aspis-statement/src/pool_v1/NFD_oracle.rs'
before=json.loads((b/'NFD_RUST_SHA256.json').read_text());assert all(hashlib.sha256((s/n).read_bytes()).hexdigest()==h for n,h in before.items()),'STOP own revision source drift'
q.write_text(body);before[str(q.relative_to(s))]=hashlib.sha256(q.read_bytes()).hexdigest();(b/'NFD_RUST_SHA256.json').write_text(json.dumps(before,indent=1))
# Reversible cfg(kani)-only actual-function contract annotations.
current=(b/'NFD_native_contracts.patch').read_text();previous=b/'NFD_contracts_applied.patch'
if previous.exists() and previous.read_text():subprocess.run(['git','apply','--reverse',str(previous)],cwd=s,check=True,capture_output=True)
if current:subprocess.run(['git','apply',str(b/'NFD_native_contracts.patch')],cwd=s,check=True,capture_output=True)
previous.write_text(current)
pins={{str(p.relative_to(s)):hashlib.sha256(p.read_bytes()).hexdigest() for p in s.rglob('*') if p.is_file()}}
(b/'NFD_RUST_SHA256.json').write_text(json.dumps(pins,indent=1))
print((b/'NFD_RUST_SHA256.json').read_text())
'''
r=ssh('python3',code);(E/(a+'-upload.log')).write_text(r.stderr);assert r.returncode==0,r.stderr
manifest=r.stdout.removesuffix('\n')
(E/'NFD_RUST_SHA256.json').write_text(manifest)
(E/(a+'-RUST_SHA256.json')).write_text(manifest)
(E/(a+'.json')).write_text(json.dumps(cfg,indent=1)+'\n')
from NFD_frozen_identity import check as frozen_identity
identity=frozen_identity(a)
(E/(a+'-frozen-identity.json')).write_text(json.dumps(identity,indent=1)+'\n')
r=ssh('cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+a+'.json',submitted=True)
(E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
code=f'''from pathlib import Path
import json
b=Path({B!r});names={[a+'/receipt.json',a+'/stdout.log',a+'/time.log',a+'-source-check.json',a+'-tools.json',a+'-metadata-pin.json',a+'-metadata.stderr',a+'-graph-check.json',a+'-lock-check.json',a+'-rule16-check.json']!r}
print(json.dumps({{n:(b/n).read_text() for n in names if (b/n).exists()}}))
'''
r=ssh('python3',code);assert r.returncode==0,r.stderr;out=json.loads(r.stdout)
for n,v in out.items():p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(v)
assert a+'/receipt.json' in out,'submitted attempt unresolved; never resubmit'
# Required disk hygiene after receipt recovery, with no live own solver.
cleanup_code=f'''from pathlib import Path
import json,hashlib
b=Path({B!r});deleted=[]
for p in (b/'NFD_tmp').rglob('*'):
 if p.is_file() and (p.name.startswith('external-sat') and p.suffix=='.cnf' or p.name.startswith('smt2_dec_problem')):
  deleted.append(dict(path=str(p),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest()));p.unlink()
print(json.dumps(dict(attempt={a!r},deleted_solver_temps=deleted,scope='own NFD_tmp only; after native scope completion')))
'''
clean=ssh('python3',cleanup_code);assert clean.returncode==0,clean.stderr
(E/(a+'-temp-cleanup.json')).write_text(clean.stdout)
if not (E/'NFD_LAUNCHER_READ.py').exists():
 r=ssh('python3',f"from pathlib import Path;print((Path({B!r})/'S2W_run_host.py').read_text(),end='')")
 assert r.returncode==0,r.stderr
 assert hashlib.sha256(r.stdout.encode()).hexdigest()=='61cf135a831640c1b6adfa433ac001a0d178046d436f1d94d1fd08b25f162101'
 (E/'NFD_LAUNCHER_READ.py').write_text(r.stdout)

rc=json.loads(out[a+'/receipt.json'])
# Rule17: retain exact execution inputs from the unchanged launcher's snapshots.
import lzma
history=not (E/'NFD_SOURCE_HISTORY.json.xz').exists()
source_code=f'''from pathlib import Path
import json,hashlib
b=Path({B!r});result={{}}
folders=sorted(p for p in b.glob('NFD_K[0-9]*') if p.is_dir()) if {history!r} else [b/{a!r}]
for p in folders:
 if not (p/'receipt.json').exists():continue
 r=json.loads((p/'receipt.json').read_text());sources={{n:(p/'sources'/n).read_text() for n in r['sources']}}
 assert all(hashlib.sha256(v.encode()).hexdigest()==r['source_hashes'][n] for n,v in sources.items())
 result[p.name]=sources
print(json.dumps(result))
'''
r=ssh('python3',source_code);assert r.returncode==0,r.stderr
snapshots=json.loads(r.stdout);assert a in snapshots
assert all(hashlib.sha256(v.encode()).hexdigest()==rc['source_hashes'][n] for n,v in snapshots[a].items())
name='NFD_SOURCE_HISTORY.json' if history else a+'-inputs.json'
raw=r.stdout.encode();(E/(name+'.xz')).write_bytes(lzma.compress(raw,preset=6));(E/(name+'.sha256')).write_text(hashlib.sha256(raw).hexdigest()+'\n')
entry={k:v for k,v in rc.items() if k!='deps_fingerprint'}
entry['full_receipt']=dict(path=str(E/a/'receipt.json'),sha256=hashlib.sha256((E/a/'receipt.json').read_bytes()).hexdigest())
with (E/'NFD_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(entry)+'\n')
active.unlink();print(json.dumps({k:rc[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps']}));print(out[a+'/stdout.log'][-900:])
sys.exit(rc['exit_status'])
